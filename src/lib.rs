//! A hierarchy labeling scheme called ORDPATH.

#![deny(missing_docs)]

use std::alloc::Layout;
use std::cmp::Ordering;
use std::fmt;
use std::mem::MaybeUninit;
use std::num::ParseIntError;
use std::ops::{Shl, Shr};
use std::ptr::{addr_of, addr_of_mut};
use std::str::FromStr;

#[cfg(feature = "serde")]
use serde::{
    de::{Deserialize, Deserializer, Visitor},
    ser::{Serialize, Serializer},
};

use enc::Encoding;
pub mod enc;

/// Creates an [`OrdPath`] containing the arguments and with the [`Default`] encoding.
#[macro_export]
macro_rules! ordpath {
    ($($x:expr),*$(,)*) => {
        OrdPath::from_slice(&vec![$($x),*], $crate::enc::Default)
    };
}

/// An error which can be returned when parsing an `OrdPath`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParseError;

impl From<ParseIntError> for ParseError {
    fn from(_: ParseIntError) -> Self {
        ParseError {}
    }
}

/// A compressed binary container of hierarchy labels represented by `i64` values.
pub struct OrdPath<E: Encoding = enc::Default> {
    enc: E,
    len: usize,
    data: OrdPathData,
}

impl<E: Encoding> OrdPath<E> {
    const END_BITS: u32 = 3;
    const LEN_BITS: u32 = usize::BITS - Self::END_BITS;
    const LEN_MASK: usize = usize::MAX >> Self::END_BITS;

    fn with_capacity(n: usize, enc: E) -> OrdPath<E> {
        let data = unsafe {
            if n > OrdPathData::INLINE_LEN {
                OrdPathData {
                    heap: std::alloc::alloc(Self::layout(n)),
                }
            } else {
                OrdPathData {
                    inline: MaybeUninit::uninit().assume_init(),
                }
            }
        };

        OrdPath { enc, len: n, data }
    }

    /// Parses a string `s` to return a new `OrdPath` with the specified encoding.
    pub fn from_str(s: &str, enc: E) -> Result<OrdPath<E>, ParseError> {
        let mut v = Vec::new();
        for x in s.split_terminator('.') {
            v.push(i64::from_str_radix(x, 10)?);
        }
        Ok(Self::from_slice(&v, enc))
    }

    /// Creates a new `OrdPath` containing elements of the slice with the specified encoding.
    pub fn from_slice(s: &[i64], enc: E) -> OrdPath<E> {
        let mut len = 0usize;
        let mut acc = 0usize;

        for value in s {
            acc += enc.stage_by_value(*value).unwrap().len() as usize;

            const ACC_LIMIT: usize = usize::MAX - 8 - 64;

            if acc > ACC_LIMIT {
                len += acc / u8::BITS as usize;
                acc -= ACC_LIMIT;
            }
        }

        if acc > 0 || len > 0 {
            len += (acc - 1) / u8::BITS as usize + 1;
        }

        if len > usize::MAX.shr(3) {
            panic!("the path is too long")
        }

        let mut path = OrdPath::with_capacity(len, enc);
        let mut ptr = path.as_mut_ptr();
        let mut acc = 0u64;
        let mut len = 0u8;

        for value in s {
            let value = *value;
            let stage = path.encoding().stage_by_value(value).unwrap();

            let prefix = stage.prefix() as u64;
            let value = (value - stage.value_low()) as u64;

            let buf = match stage.len() < 64 {
                true => (prefix.shl(stage.value_len()) | value).shl(64 - stage.len()),
                false => prefix.shl(64 - stage.prefix_len()) | value.shr(stage.len() - 64),
            };

            acc |= buf >> len;
            len += stage.len();

            if len >= 64 {
                unsafe {
                    ptr.copy_from_nonoverlapping(acc.to_be_bytes().as_ptr(), 8);
                    ptr = ptr.add(8);
                }

                len -= 64;
                acc = match stage.len() <= 64 {
                    true => buf.shl(stage.len() - len),
                    false => value.shl(stage.len() - len),
                };
            }
        }

        unsafe {
            ptr.copy_from_nonoverlapping(acc.to_be_bytes().as_ptr(), len.div_ceil(8).into());
        }

        path.len |= (u64::BITS as usize - len as usize)
            .wrapping_rem(u8::BITS as usize)
            .shl(Self::LEN_BITS);
        path
    }

    /// Returns `true` if `self` has a length of zero bytes.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[macro_use] extern crate ordpath;
    /// # use ordpath::OrdPath;
    /// let p = ordpath![1, 2, 3];
    /// assert!(!p.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns `true` if `self` is an ancestor of `other`.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[macro_use] extern crate ordpath;
    /// # use ordpath::OrdPath;
    /// let a = ordpath![1, 2];
    /// let c = ordpath![1, 2, 3];
    /// assert!(a.is_ancestor_of(&c));
    /// ```
    pub fn is_ancestor_of(&self, other: &Self) -> bool {
        let self_len = self.len();
        let other_len = other.len();

        if self_len > 0 && self_len <= other_len {
            unsafe {
                let self_slice = std::slice::from_raw_parts(self.as_ptr(), self_len - 1);
                let other_slice = std::slice::from_raw_parts(other.as_ptr(), self_len - 1);

                if self_slice.eq(other_slice) {
                    let zeros = self.trailing_zeros();

                    if self_len < other_len || zeros > other.trailing_zeros() {
                        let self_last = self.as_ptr().add(self_len - 1).read();
                        let other_last = other.as_ptr().add(self_len - 1).read();

                        return self_last == other_last & u8::MAX.shl(zeros);
                    }
                }
            }
        }

        self_len == 0 && other_len != 0
    }

    fn spilled(&self) -> bool {
        self.len() > OrdPathData::INLINE_LEN
    }

    /// Returns a reference to the used encoding.
    pub fn encoding(&self) -> &E {
        &self.enc
    }

    /// Returns the number of bytes used.
    pub fn len(&self) -> usize {
        self.len & Self::LEN_MASK
    }

    fn trailing_zeros(&self) -> u32 {
        self.len.shr(Self::LEN_BITS) as u32
    }

    fn as_ptr(&self) -> *const u8 {
        unsafe {
            if self.spilled() {
                self.data.heap
            } else {
                addr_of!(self.data.inline) as *const u8
            }
        }
    }

    fn as_mut_ptr(&mut self) -> *mut u8 {
        unsafe {
            if self.spilled() {
                self.data.heap as *mut u8
            } else {
                addr_of_mut!(self.data.inline) as *mut u8
            }
        }
    }

    /// Extracts a slice containing the encoded values.
    pub fn as_slice(&self) -> &[u8] {
        unsafe { std::slice::from_raw_parts(self.as_ptr(), self.len()) }
    }

    fn as_mut_slice(&mut self) -> &mut [u8] {
        unsafe { std::slice::from_raw_parts_mut(self.as_mut_ptr(), self.len()) }
    }

    fn layout(n: usize) -> Layout {
        unsafe { Layout::array::<u8>(n).unwrap_unchecked() }
    }
}

impl<E: Encoding + Clone> OrdPath<E> {
    /// Returns the `OrdPath<E>` without its final element, if there is one.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[macro_use] extern crate ordpath;
    /// # use ordpath::OrdPath;
    /// let path = ordpath![1, 2];
    /// let parent = path.parent();
    /// assert_eq!(parent, Some(ordpath![1]));
    /// let grand_parent = parent.and_then(|p| p.parent());
    /// assert_eq!(grand_parent, Some(ordpath![]));
    /// let grand_grand_parent = grand_parent.and_then(|p| p.parent());
    /// assert_eq!(grand_grand_parent, None);
    /// ```
    pub fn parent(&self) -> Option<Self> {
        if self.is_empty() {
            return None;
        }

        let mut iter = self.into_iter();
        let mut consumed_bytes = 0;
        let mut consumed_bits = 0;
        if iter.next().is_some() {
            loop {
                let tmp_bytes = iter.pos;
                let tmp_bits = iter.len;

                if iter.next().is_none() {
                    break;
                }

                consumed_bytes = tmp_bytes;
                consumed_bits = tmp_bits;
            }
        }

        let len = consumed_bytes - consumed_bits.div_euclid(8) as usize;
        let trailing_zeros = consumed_bits.rem_euclid(8);

        let mut path = Self::with_capacity(len, self.encoding().clone());
        let data = path.as_mut_slice();

        data.copy_from_slice(&self.as_slice()[..len]);

        if let Some(last) = data.last_mut() {
            *last &= u8::MAX.shl(trailing_zeros);
        }

        path.len |= (trailing_zeros as usize).shl(Self::LEN_BITS);

        Some(path)
    }
}

impl FromStr for OrdPath<enc::Default> {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::from_str(s, enc::Default)
    }
}

impl<E: Encoding + Clone> Clone for OrdPath<E> {
    fn clone(&self) -> Self {
        let mut clone = Self::with_capacity(self.len(), self.encoding().clone());
        unsafe {
            std::ptr::copy(self.as_ptr(), clone.as_mut_ptr(), clone.len());
        }
        clone.len = self.len;
        clone
    }
}

impl<E: Encoding> PartialEq for OrdPath<E> {
    fn eq(&self, other: &Self) -> bool {
        self.as_slice() == other.as_slice()
    }
}

impl<E: Encoding> Eq for OrdPath<E> {}

impl<E: Encoding> PartialOrd for OrdPath<E> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<E: Encoding> Ord for OrdPath<E> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.as_slice().cmp(&other.as_slice())
    }
}

impl<E: Encoding> Drop for OrdPath<E> {
    fn drop(&mut self) {
        unsafe {
            if self.spilled() {
                std::alloc::dealloc(self.as_ptr() as *mut u8, Self::layout(self.len()));
            }
        }
    }
}

impl<E: Encoding> fmt::Debug for OrdPath<E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.into_iter()).finish()
    }
}

impl<E: Encoding> fmt::Display for OrdPath<E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        let mut iterator = self.into_iter();
        if let Some(value) = iterator.next() {
            write!(f, "{}", value)?;
            while let Some(value) = iterator.next() {
                write!(f, ".{}", value)?;
            }
        }
        Ok(())
    }
}

impl<'a, E: Encoding> IntoIterator for &'a OrdPath<E> {
    type IntoIter = IntoIter<'a, E>;
    type Item = i64;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter::<E> {
            path: self,
            pos: 0,
            acc: 0,
            len: 0,
        }
    }
}

#[cfg(feature = "serde")]
#[cfg_attr(docsrs, doc(cfg(feature = "serde")))]
impl<E: Encoding> Serialize for OrdPath<E> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        self.as_slice().serialize(serializer)
    }
}

#[cfg(feature = "serde")]
#[cfg_attr(docsrs, doc(cfg(feature = "serde")))]
impl<'de> Deserialize<'de> for OrdPath<enc::Default> {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_bytes(OrdPathVisitor {})
    }
}

#[cfg(feature = "serde")]
struct OrdPathVisitor;

#[cfg(feature = "serde")]
impl<'de> Visitor<'de> for OrdPathVisitor {
    type Value = OrdPath<enc::Default>;

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter.write_str("bytes")
    }

    fn visit_bytes<E>(self, v: &[u8]) -> Result<Self::Value, E> {
        let mut path = OrdPath::with_capacity(v.len(), enc::Default);
        let bytes =
            unsafe { std::slice::from_raw_parts_mut(path.as_mut_ptr() as *mut u8, path.len()) };

        bytes.copy_from_slice(&v);

        let mut iter = path.into_iter();
        while iter.next().is_some() {}

        path.len |= (iter.len as usize).shl(OrdPath::<enc::Default>::LEN_BITS);

        Ok(path)
    }
}

union OrdPathData {
    inline: [MaybeUninit<u8>; Self::INLINE_LEN],
    heap: *const u8,
}

impl OrdPathData {
    const INLINE_LEN: usize = (usize::BITS / u8::BITS) as usize;
}

/// An iterator that references an `OrdPath` and yields its items by value.
///
/// Returned from [`OrdPath::into_iter`].
pub struct IntoIter<'a, E: Encoding> {
    path: &'a OrdPath<E>,
    pos: usize,
    acc: u64,
    len: u8,
}

impl<'a, E: Encoding> Iterator for IntoIter<'a, E> {
    type Item = i64;

    fn next(&mut self) -> Option<Self::Item> {
        let prefix = (self.acc >> 56) as u8;
        let stage = self.path.encoding().stage_by_prefix(prefix);

        if let Some(stage) = stage {
            if stage.len() <= self.len {
                let value = (self.acc << stage.prefix_len()) >> (64 - stage.value_len());

                self.acc <<= stage.len();
                self.len -= stage.len();

                return Some(value as i64 + stage.value_low());
            }
        }

        let left = self.path.len() - self.pos;

        if left > 0 {
            let consumed = left.min(8);
            let acc_next = unsafe {
                let mut buffer = 0u64;
                self.path
                    .as_ptr()
                    .add(self.pos)
                    .copy_to_nonoverlapping(&mut buffer as *mut u64 as *mut u8, consumed);

                u64::from_be(buffer)
            };

            let acc = self.acc | acc_next >> self.len;
            let len = self.len + (consumed as u32 * u8::BITS) as u8;

            let prefix = (acc >> 56) as u8;
            let stage = self
                .path
                .encoding()
                .stage_by_prefix(prefix)
                .expect("unknown_prefix");

            self.pos += consumed;

            if stage.len() <= len {
                let value = (acc << stage.prefix_len()) >> (64 - stage.value_len());

                self.acc = acc_next << (stage.len() - self.len);
                self.len = len - stage.len();

                return Some(value as i64 + stage.value_low());
            }
        }

        None
    }
}

/// An encoding stage used for vlue compression.
pub struct Stage {
    prefix_len: u8,
    prefix: u8,
    value_len: u8,
    value_low: i64,
}

impl Stage {
    /// Constructs a stage with the given prefix and value range.
    pub const fn new(prefix_len: u8, prefix: u8, value_len: u8, value_low: i64) -> Stage {
        assert!(prefix_len < 8);
        assert!(value_len < 64);

        Stage {
            prefix_len,
            prefix,
            value_len,
            value_low,
        }
    }

    /// Returs the prefix identifying the stage.
    pub const fn prefix(&self) -> u8 {
        self.prefix
    }

    /// Returns the number of bits used to encode the prefix.
    pub const fn prefix_len(&self) -> u8 {
        self.prefix_len
    }

    /// Returns the lowest value which can be encoded by the stage.
    pub const fn value_low(&self) -> i64 {
        self.value_low
    }

    /// Returns the upper value which can be encoded by the stage.
    pub const fn value_high(&self) -> i64 {
        self.value_low + ((1 << self.value_len) - 1)
    }

    /// Returns the number of bits used to encode the value part.
    pub const fn value_len(&self) -> u8 {
        self.value_len
    }

    /// Returns the total number of bits used to encode a value.
    pub const fn len(&self) -> u8 {
        self.prefix_len() + self.value_len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn path_from_slice() {
        fn assert_path(s: &[i64]) {
            assert_eq!(
                OrdPath::from_slice(s, enc::Default)
                    .into_iter()
                    .collect::<Vec<_>>(),
                s
            );
        }

        assert_path(&[0; 0]);
        assert_path(&[0]);
        assert_path(&[0, 8]);
        assert_path(&[4440, 4440, 4440, 8]);
        assert_path(&[4440, 4440, 4440, 8, 0]);
        assert_path(&[4440, 4440, 4440, 4440]);
        assert_path(&[4440, 4440, 4440, 4440, 88]);
        assert_path(&[4295037272, 4295037272]);
        assert_path(&[4295037272, 4295037272, 4440, 88]);
        assert_path(&[4295037272, 4295037272, 4440, 344]);
        assert_path(&[4295037272, 4295037272, 4440, 4440]);

        assert_path(&[0 + 3]);
        assert_path(&[0 + 3, 8 + 5]);
        assert_path(&[4440 + 13, 4440 + 179, 4440 + 7541, 8 + 11]);
        assert_path(&[4440 + 13, 4440 + 179, 4440 + 7541, 8 + 11, 0 + 3]);
        assert_path(&[4440 + 13, 4440 + 179, 4440 + 7541, 4440 + 123]);
        assert_path(&[4440 + 13, 4440 + 179, 4440 + 7541, 4440 + 123, 88 + 11]);
        assert_path(&[4295037272 + 31, 4295037272 + 6793]);
        assert_path(&[4295037272 + 31, 4295037272 + 6793, 4440 + 7541, 88 + 11]);
        assert_path(&[4295037272 + 31, 4295037272 + 6793, 4440 + 7541, 344 + 71]);
        assert_path(&[4295037272 + 31, 4295037272 + 6793, 4440 + 7541, 4440 + 123]);
    }

    #[test]
    fn path_from_str() {
        fn assert_path(s: &str, p: Result<OrdPath, ParseError>) {
            assert_eq!(OrdPath::from_str(s, enc::Default), p);
        }

        assert_path("", Ok(ordpath![]));
        assert_path("0", Ok(ordpath![0]));
        assert_path("1", Ok(ordpath![1]));
        assert_path("1.2", Ok(ordpath![1, 2]));
        assert_path("1.a", Err(ParseError {}));
        assert_path("1_2", Err(ParseError {}));
        assert_path("a", Err(ParseError {}));
    }

    #[test]
    fn path_to_string() {
        fn assert_path(p: Vec<i64>, s: &str) {
            assert_eq!(OrdPath::from_slice(&p, enc::Default).to_string(), s);
        }

        assert_path(vec![], "");
        assert_path(vec![0], "0");
        assert_path(vec![1], "1");
        assert_path(vec![1, 2], "1.2");
    }

    #[test]
    fn path_clone() {
        fn assert_path<E: Encoding + Clone>(p: OrdPath<E>) {
            assert_eq!(
                p.into_iter().collect::<Vec<_>>(),
                p.clone().into_iter().collect::<Vec<_>>()
            );
        }

        assert_path(ordpath![]);
        assert_path(ordpath![0]);
        assert_path(ordpath![1]);
        assert_path(ordpath![1, 2]);
    }

    #[test]
    fn path_ordering() {
        fn cmp(left: &[i64], right: &[i64]) -> Ordering {
            let left = OrdPath::from_slice(left, enc::Default);
            let right = OrdPath::from_slice(right, enc::Default);

            left.cmp(&right)
        }

        assert_eq!(cmp(&[0; 0], &[0; 0]), Ordering::Equal);
        assert_eq!(cmp(&[0; 0], &[0]), Ordering::Less);
        assert_eq!(cmp(&[0], &[0; 0]), Ordering::Greater);
        assert_eq!(cmp(&[0], &[0]), Ordering::Equal);
        assert_eq!(cmp(&[0], &[1]), Ordering::Less);
        assert_eq!(cmp(&[0], &[0, 1]), Ordering::Less);
        assert_eq!(cmp(&[0], &[69976, 69976]), Ordering::Less);
        assert_eq!(cmp(&[0], &[4295037272, 4295037272]), Ordering::Less);
    }

    #[test]
    fn path_is_empty() {
        assert_eq!(ordpath![].is_empty(), true);
        assert_eq!(ordpath![0].is_empty(), false);
    }

    #[test]
    fn path_is_ancestor() {
        assert!(ordpath![].is_ancestor_of(&ordpath![0]));
        assert!(ordpath![0].is_ancestor_of(&ordpath![0, 1]));
        assert!(ordpath![0, 1].is_ancestor_of(&ordpath![0, 1, 2, 3]));
        assert!(
            ordpath![4295037272, 4295037272].is_ancestor_of(&ordpath![4295037272, 4295037272, 1])
        );

        assert!(!ordpath![].is_ancestor_of(&ordpath![]));
        assert!(!ordpath![0].is_ancestor_of(&ordpath![]));
        assert!(!ordpath![0].is_ancestor_of(&ordpath![0]));
        assert!(!ordpath![0].is_ancestor_of(&ordpath![1]));
        assert!(!ordpath![0, 1].is_ancestor_of(&ordpath![0]));
        assert!(!ordpath![0, 1, 2, 3].is_ancestor_of(&ordpath![0, 1]));
        assert!(
            !ordpath![4295037272, 4295037272, 1].is_ancestor_of(&ordpath![4295037272, 4295037272])
        );
    }

    #[test]
    fn path_parent() {
        let path = ordpath![1, 2];
        let parent = path.parent();
        assert_eq!(parent, Some(ordpath![1]));
        let grand_parent = parent.and_then(|p| p.parent());
        assert_eq!(grand_parent, Some(ordpath![]));
        let grand_grand_parent = grand_parent.and_then(|p| p.parent());
        assert_eq!(grand_grand_parent, None);
    }

    #[cfg(feature = "serde")]
    #[test]
    fn path_serialization() {
        let path = ordpath![0, 1, 2, 3];

        let encoded = bincode::serialize(&path).unwrap();
        let decoded = bincode::deserialize(&encoded).unwrap();

        assert_eq!(path, decoded);
        assert_eq!(path.trailing_zeros(), decoded.trailing_zeros());
    }
}
