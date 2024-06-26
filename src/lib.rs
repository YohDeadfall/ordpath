//! A hierarchy labeling scheme called ORDPATH.

#![deny(missing_docs)]

use std::iter::FusedIterator;
use std::str::FromStr;
use std::{cmp::Ordering, io::Write};
use std::{fmt, io};

#[cfg(feature = "serde")]
use serde::{
    de::{Deserialize, Deserializer, Visitor},
    ser::{Serialize, Serializer},
};

pub mod enc;
mod error;
mod raw;
mod reader;
mod writer;

use enc::Encoding;
pub use error::{Error, ErrorKind};
use raw::RawOrdPath;
pub use reader::Reader;
pub use writer::Writer;

/// Creates an [`OrdPath`] containing the arguments and with the [`Default`] encoding.
#[macro_export]
macro_rules! ordpath {
    ($($x:expr),*$(,)*) => {
        <OrdPath>::from_slice(&vec![$($x),*], $crate::enc::Default).unwrap()
    };
}

struct Counter(usize);

impl Write for Counter {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        self.0 = self
            .0
            .checked_add(buf.len())
            .ok_or_else(|| io::Error::other("reached memory limit"))?;

        Ok(buf.len())
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

const USIZE_BYTES: usize = (usize::BITS / 8) as usize;

/// A compressed binary container of hierarchy labels represented by `i64` values.
pub struct OrdPath<E: Encoding = enc::Default, const N: usize = USIZE_BYTES> {
    enc: E,
    raw: RawOrdPath<N>,
}

impl<E: Encoding, const N: usize> OrdPath<E, N> {
    /// Parses a string `s` to return a new `OrdPath` with the specified encoding.
    pub fn from_str(s: &str, enc: E) -> Result<Self, Error> {
        let mut v = Vec::new();
        for x in s.split_terminator('.') {
            v.push(i64::from_str_radix(x, 10)?);
        }
        Self::from_slice(&v, enc)
    }

    /// Creates a new `OrdPath` containing elements of the slice with the specified encoding.
    pub fn from_slice(s: &[i64], enc: E) -> Result<Self, Error> {
        let mut len = Counter(0);
        let mut writer = Writer::one_terminated(len.by_ref(), &enc);

        for value in s {
            writer.write(*value)?;
        }

        drop(writer);

        let mut raw = RawOrdPath::new(len.0)?;
        let mut writer = Writer::one_terminated(raw.as_mut_slice(), &enc);

        for value in s {
            writer.write(*value)?;
        }

        drop(writer);

        Ok(OrdPath { enc, raw })
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
    /// let d = ordpath![1, 2, 3];
    /// assert!(a.is_ancestor_of(&d));
    /// ```
    pub fn is_ancestor_of(&self, other: &Self) -> bool {
        let self_len = self.len();
        let other_len = other.len();

        if self_len > 0 && self_len <= other_len {
            unsafe {
                let self_slice = std::slice::from_raw_parts(self.as_ptr(), self_len - 1);
                let other_slice = std::slice::from_raw_parts(other.as_ptr(), self_len - 1);

                if self_slice.eq(other_slice) {
                    let self_last = self.as_ptr().add(self_len - 1).read();
                    let self_last_len = self_last.trailing_zeros() + 1;

                    let other_last = other.as_ptr().add(self_len - 1).read();
                    let other_last_len = other_last.trailing_zeros() + 1;

                    return self_last_len > other_last_len
                        && (self_last >> self_last_len) == (other_last >> self_last_len);
                }
            }
        }

        self_len == 0 && other_len != 0
    }

    /// Returns `true` if `self` is a descendant of `other`.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[macro_use] extern crate ordpath;
    /// # use ordpath::OrdPath;
    /// let a = ordpath![1, 2];
    /// let d = ordpath![1, 2, 3];
    /// assert!(d.is_descendant_of(&a));
    /// ```
    pub fn is_descendant_of(&self, other: &Self) -> bool {
        other.is_ancestor_of(self)
    }

    /// Returns a reference to the used encoding.
    pub fn encoding(&self) -> &E {
        &self.enc
    }

    /// Returns the number of bytes used.
    pub fn len(&self) -> usize {
        self.raw.len()
    }

    fn as_ptr(&self) -> *const u8 {
        self.raw.as_ptr()
    }

    /// Extracts a slice containing the encoded values.
    pub fn as_slice(&self) -> &[u8] {
        self.raw.as_slice()
    }

    /// Returns an iterator over the encoded values.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[macro_use] extern crate ordpath;
    /// # use ordpath::OrdPath;
    /// let path = ordpath![1, 2, 3, 4];
    ///
    /// // Print 1, 2, 3, 4
    /// for x in path.iter() {
    ///     println!("{x}");
    /// }
    /// ```
    pub fn iter(&self) -> Iter<'_, E> {
        Iter {
            reader: Reader::one_terminated(self.as_slice(), self.encoding()),
        }
    }
}

impl<E: Encoding + Clone, const N: usize> OrdPath<E, N> {
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

        let mut stages = Reader::one_terminated(self.as_slice(), &self.enc);
        let mut consumed_bytes = 0usize;
        let mut consumed_bits = 0u8;
        if let Ok(Some((_, stage))) = stages.read_stage() {
            let mut prev_len = stage.len();
            while let Ok(Some((_, stage))) = stages.read_stage() {
                let bits = consumed_bits + prev_len;

                consumed_bytes += bits as usize / 8;
                consumed_bits = bits & 7;
                prev_len = stage.len();
            }
        }

        let len = if consumed_bytes > 0 || consumed_bits > 0 {
            consumed_bytes + (consumed_bits + 1).div_ceil(8) as usize
        } else {
            0
        };

        unsafe {
            // SAFETY: The resulting path is shorter that self.
            let mut raw = RawOrdPath::<N>::new(len).unwrap_unchecked();

            if len > 0 {
                let ptr = raw.as_mut_ptr();
                ptr.copy_from_nonoverlapping(self.raw.as_ptr(), len);
                let ptr = ptr.add(len - 1);
                ptr.write(ptr.read() & (255 << ((8 - consumed_bits) & 7)) | (128 >> consumed_bits));
            }

            Some(Self {
                enc: self.enc.clone(),
                raw,
            })
        }
    }
}

unsafe impl<E: Encoding + Send, const N: usize> Send for OrdPath<E, N> {}
unsafe impl<E: Encoding + Sync, const N: usize> Sync for OrdPath<E, N> {}

impl<const N: usize> FromStr for OrdPath<enc::Default, N> {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::from_str(s, enc::Default)
    }
}

impl<E: Encoding + Clone, const N: usize> Clone for OrdPath<E, N> {
    fn clone(&self) -> Self {
        Self {
            enc: self.enc.clone(),
            raw: self.raw.clone(),
        }
    }
}

impl<E: Encoding, const N: usize> PartialEq for OrdPath<E, N> {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other).is_eq()
    }
}

impl<E: Encoding, const N: usize> Eq for OrdPath<E, N> {}

impl<E: Encoding, const N: usize> PartialOrd for OrdPath<E, N> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<E: Encoding, const N: usize> Ord for OrdPath<E, N> {
    fn cmp(&self, other: &Self) -> Ordering {
        let lhs = self.as_slice();
        let rhs = other.as_slice();
        let len = lhs.len().min(rhs.len());

        if len == 0 {
            lhs.len().cmp(&rhs.len())
        } else {
            let len = len - 1;

            lhs[..len].cmp(&rhs[..len]).then_with(|| {
                fn get_at(s: &[u8], index: usize) -> u8 {
                    let item = s[index];
                    if s.len() == index + 1 {
                        let tail = item.trailing_zeros() + 1;
                        let mask = 255 << (tail & 7);

                        item & mask
                    } else {
                        item
                    }
                }

                let lhs = get_at(lhs, len);
                let rhs = get_at(rhs, len);

                lhs.cmp(&rhs)
            })
        }
    }
}

impl<E: Encoding, const N: usize> fmt::Debug for OrdPath<E, N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.into_iter()).finish()
    }
}

impl<E: Encoding, const N: usize> fmt::Display for OrdPath<E, N> {
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

impl<'a, E: Encoding, const N: usize> IntoIterator for &'a OrdPath<E, N> {
    type IntoIter = Iter<'a, E>;
    type Item = i64;

    fn into_iter(self) -> Self::IntoIter {
        Iter::<E> {
            reader: Reader::one_terminated(self.as_slice().into(), &self.enc),
        }
    }
}

/// An iterator that references an `OrdPath` and yields its items by value.
///
/// Returned from [`OrdPath::into_iter`].
pub struct Iter<'a, E: Encoding> {
    reader: Reader<&'a [u8], &'a E>,
}

impl<'a, E: Encoding> Iterator for Iter<'a, E> {
    type Item = i64;

    fn next(&mut self) -> Option<Self::Item> {
        self.reader.read().unwrap()
    }
}

impl<'a, E: Encoding> FusedIterator for Iter<'a, E> {}

#[cfg(feature = "serde")]
#[cfg_attr(docsrs, doc(cfg(feature = "serde")))]
impl<E: Encoding, const N: usize> Serialize for OrdPath<E, N> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        self.as_slice().serialize(serializer)
    }
}

#[cfg(feature = "serde")]
#[cfg_attr(docsrs, doc(cfg(feature = "serde")))]
impl<'de> Deserialize<'de> for OrdPath {
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
    type Value = OrdPath;

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter.write_str("bytes")
    }

    fn visit_bytes<E: serde::de::Error>(self, v: &[u8]) -> Result<Self::Value, E> {
        let mut raw = RawOrdPath::new(v.len()).map_err(E::custom)?;

        raw.as_mut_slice().copy_from_slice(v);

        Ok(OrdPath {
            enc: enc::Default,
            raw,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn path_from_slice() {
        fn assert_path(s: &[i64]) {
            assert_eq!(
                OrdPath::<enc::Default, USIZE_BYTES>::from_slice(s, enc::Default)
                    .unwrap()
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
        fn assert_path(s: &str, p: Result<OrdPath, Error>) {
            assert_eq!(OrdPath::from_str(s, enc::Default), p);
        }

        assert_path("", Ok(ordpath![]));
        assert_path("0", Ok(ordpath![0]));
        assert_path("1", Ok(ordpath![1]));
        assert_path("1.2", Ok(ordpath![1, 2]));
        assert_path("1.a", Err(Error::new(ErrorKind::InvalidInput)));
        assert_path("1_2", Err(Error::new(ErrorKind::InvalidInput)));
        assert_path("a", Err(Error::new(ErrorKind::InvalidInput)));
    }

    #[test]
    fn path_to_string() {
        fn assert_path(p: Vec<i64>, s: &str) {
            assert_eq!(
                OrdPath::<_, USIZE_BYTES>::from_slice(&p, enc::Default)
                    .unwrap()
                    .to_string(),
                s
            );
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
        fn cmp(lhs: &[i64], rhs: &[i64]) -> Ordering {
            let lhs = <OrdPath>::from_slice(lhs, enc::Default).unwrap();
            let rhs = <OrdPath>::from_slice(rhs, enc::Default).unwrap();

            lhs.cmp(&rhs)
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
    fn path_iter_fused() {
        let path = ordpath![1, 2];
        let mut iter = path.iter();

        assert_eq!(iter.next(), Some(1));
        assert_eq!(iter.next(), Some(2));
        assert_eq!(iter.next(), None);
        assert_eq!(iter.next(), None);
        assert_eq!(iter.next(), None);
        assert_eq!(iter.next(), None);
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
    }
}
