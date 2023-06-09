//! A hierarchy labeling scheme called ORDPATH.

#![deny(missing_docs)]

use std::alloc::Layout;
use std::cmp::Ordering;
use std::fmt;
use std::mem::{self, MaybeUninit};
use std::num::ParseIntError;
use std::ops::{Shl, Shr};
use std::str::FromStr;

/// Creates an [`OrdPath`] containing the arguments and with the [`Default`] encoding.
#[macro_export]
macro_rules! ordpath {
    ($($x:expr),*$(,)*) => {
        OrdPath::from_slice(&vec![$($x),*], Default {})
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
pub struct OrdPath<E: Encoding = Default> {
    enc: E,
    len: usize,
    data: OrdPathData,
}

impl<E: Encoding> OrdPath<E> {
    fn with_capacity(n: usize, enc: E) -> OrdPath<E> {
        let data = unsafe {
            if n > 1 {
                OrdPathData {
                    heap: std::alloc::alloc(Self::layout(n)) as *const u64,
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
                len += acc / u64::BITS as usize;
                acc -= ACC_LIMIT;
            }
        }

        if acc > 0 || len > 0 {
            acc += 1;
            len += (acc - 1) / u64::BITS as usize + 1;
        }

        let path = OrdPath::with_capacity(len, enc);
        let mut ptr = path.ptr() as *mut u64;
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

            if len > 64 {
                unsafe {
                    ptr.write(acc.to_be());
                    ptr = ptr.add(1);
                }

                len -= 64;
                acc = match stage.len() <= 64 {
                    true => buf.shl(stage.len() - len),
                    false => value.shl(stage.len() - len),
                };
            }
        }

        if len < 64 {
            acc |= 1 << (63 - len);
        } else {
            unsafe {
                ptr.add(1).write(1 << 63);
            }
        }

        unsafe {
            ptr.write(acc.to_be());
        }

        path
    }

    /// Returns `true` if `self` has a length of zero bytes.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[macro_use] extern crate ordpath;
    /// # use ordpath::{OrdPath, Default};
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
    /// # use ordpath::{OrdPath, Default};
    /// let a = ordpath![1, 2];
    /// let c = ordpath![1, 2, 3];
    /// assert!(a.is_ancestor_of(&c));
    /// ````
    pub fn is_ancestor_of(&self, other: &Self) -> bool {
        let self_len = self.len();
        let other_len = other.len();

        if self_len > 0 && self_len <= other.len() {
            unsafe {
                let self_slice = std::slice::from_raw_parts(self.ptr(), self_len - 1);
                let other_slice = std::slice::from_raw_parts(other.ptr(), self_len - 1);

                if self_slice.eq(other_slice) {
                    fn read_at<E: Encoding>(p: &OrdPath<E>, i: usize) -> u64 {
                        unsafe {
                            let value = p.ptr().add(i).read();
                            if cfg!(target_endian = "little") {
                                value.swap_bytes()
                            } else {
                                value
                            }
                        }
                    }

                    let self_last = read_at(self, self_len - 1);
                    let self_tail = self_last.trailing_zeros() + 1;

                    let other_last = read_at(other, self_len - 1);
                    let other_tail = other_last.trailing_zeros() + 1;

                    return self_tail > other_tail
                        && (self_last >> self_tail) == (other_last >> self_tail);
                }
            }
        }

        self_len == 0 && other_len != 0
    }

    fn spilled(&self) -> bool {
        self.len > 1
    }

    fn encoding(&self) -> &E {
        &self.enc
    }

    fn len(&self) -> usize {
        self.len
    }

    fn ptr(&self) -> *const u64 {
        unsafe {
            if self.spilled() {
                self.data.heap
            } else {
                mem::transmute(self.data.inline.as_ptr())
            }
        }
    }

    fn as_slice(&self) -> &[u64] {
        unsafe { std::slice::from_raw_parts(self.ptr(), self.len()) }
    }

    fn as_slice_and_last(&self) -> Option<(&[u64], u64)> {
        match self.len() {
            0 => None,
            l => unsafe {
                let slice = std::slice::from_raw_parts(self.ptr(), l - 1);
                let last = self.ptr().add(l - 1).read();

                Some((
                    slice,
                    last & u64::MAX.wrapping_shl(last.trailing_zeros() + 1),
                ))
            },
        }
    }

    fn layout(n: usize) -> Layout {
        unsafe { Layout::array::<u64>(n).unwrap_unchecked() }
    }
}

impl FromStr for OrdPath<Default> {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::from_str(s, Default {})
    }
}

impl<E: Encoding + Clone> Clone for OrdPath<E> {
    fn clone(&self) -> Self {
        let clone = Self::with_capacity(self.len(), self.encoding().clone());
        unsafe {
            std::ptr::copy(self.ptr(), clone.ptr() as *mut u64, clone.len());
        }
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
        self.as_slice_and_last().cmp(&other.as_slice_and_last())
    }
}

impl<E: Encoding> Drop for OrdPath<E> {
    fn drop(&mut self) {
        unsafe {
            if self.spilled() {
                std::alloc::dealloc(self.ptr() as *mut u8, Self::layout(self.len));
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

union OrdPathData {
    inline: [MaybeUninit<u64>; 1],
    heap: *const u64,
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
            let acc_prev = self.acc;
            let mut acc_next = unsafe { self.path.ptr().add(self.pos).read() };

            if cfg!(target_endian = "little") {
                acc_next = acc_next.swap_bytes();
            }

            let acc = acc_prev | acc_next >> self.len;
            let len = self.len
                + match left {
                    1 => 64 - acc_next.trailing_zeros() - 1,
                    _ => 64,
                } as u8;

            let prefix = (acc >> 56) as u8;
            let stage = self
                .path
                .encoding()
                .stage_by_prefix(prefix)
                .expect("unknown_prefix");

            self.pos += 1;

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

/// An implementation of `Alloctor` is responsible for providing a [`Stage`]
/// for the provided value or prefix.
pub trait Encoding {
    /// Returns a reference to the [`Stage`] corresponding to the prefix.
    fn stage_by_prefix(&self, prefix: u8) -> Option<&Stage>;

    /// Returns a reference to the [`Stage`] which range contains the value.
    fn stage_by_value(&self, value: i64) -> Option<&Stage>;
}

macro_rules! replace_expr {
    ($e:expr; $s:expr) => {
        $s
    };
}

macro_rules! count {
    ($($e:expr,)*) => {<[()]>::len(&[$(replace_expr!($e; ())),*])};
}

/// Defines a new encoding with the specified stages.
#[macro_export]
macro_rules! encoding {
    ($v:vis $t:ident :[$(($prefix:expr, $prefix_len:expr, $value_len:expr)),+]) => {
        #[allow(missing_docs)]
        #[derive(Copy, Clone, Default, Debug)]
        $v struct $t;

        impl $t {
            const STAGES: [Stage; count!($($prefix,)*)] = {
                let mut stages = [
                    $(Stage::new($prefix_len, $prefix, $value_len, 0)),+
                ];

                let origin = stages.len() / 2;

                let mut index = origin;
                while index > 0  {
                    index -= 1;
                    stages[index] = Stage::new(
                        stages[index].prefix_len(),
                        stages[index].prefix(),
                        stages[index].value_len(),
                        stages[index + 1].value_low() - stages[index].value_high() - 1);
                }

                let mut index = origin;
                while index + 1 < stages.len() {
                    index += 1;
                    stages[index] = Stage::new(
                        stages[index].prefix_len(),
                        stages[index].prefix(),
                        stages[index].value_len(),
                        stages[index - 1].value_high() + 1);
                }

                stages
            };

            const STAGE_LOOKUP: [u8; u8::MAX as usize] = {
                let mut lookup = [u8::MAX; u8::MAX as usize];
                let mut index = 0;
                while index < Self::STAGES.len() {
                    let stage = &Self::STAGES[index];
                    let prefix_offset = u8::BITS as u8 - stage.prefix_len();
                    let prefix = stage.prefix << prefix_offset;
                    let mut data = 0;
                    while data < 1 << prefix_offset {
                        lookup[(prefix | data) as usize] = index as u8;
                        data += 1;
                    }

                    index += 1;
                }

                lookup
            };
        }

        impl Encoding for $t {
            fn stage_by_prefix(&self, prefix: u8) -> Option<&Stage> {
                match Self::STAGE_LOOKUP[prefix as usize] {
                    u8::MAX => None,
                    index => Some(&Self::STAGES[index as usize])
                }
            }

            fn stage_by_value(&self, value: i64) -> Option<&Stage> {
                Self::STAGES.binary_search_by(|stage|{
                    let result = stage.value_low().cmp(&value);
                    if result.is_gt() {
                        return result;
                    }

                    let result = stage.value_high().cmp(&value);
                    if result.is_lt() {
                        return result;
                    }

                    Ordering::Equal
                })
                .map(|index| &Self::STAGES[index]).ok()
            }
        }
    };
}

encoding!(pub Default: [
    (0b0000001, 7, 48),
    (0b0000010, 7, 32),
    (0b0000011, 7, 16),
    (0b000010 , 6, 12),
    (0b000011 , 6, 8 ),
    (0b00010  , 5, 6 ),
    (0b00011  , 5, 4 ),
    (0b001    , 3, 3 ),
    (0b01     , 2, 3 ),
    (0b100    , 3, 4 ),
    (0b101    , 3, 6 ),
    (0b1100   , 4, 8 ),
    (0b1101   , 4, 12),
    (0b11100  , 5, 16),
    (0b11101  , 5, 32),
    (0b11110  , 5, 48)]
);

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn path_from_slice() {
        fn assert_path(s: &[i64]) {
            assert_eq!(
                OrdPath::from_slice(s, Default {})
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
            assert_eq!(OrdPath::from_str(s, Default {}), p);
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
            assert_eq!(OrdPath::from_slice(&p, Default {}).to_string(), s);
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
            let left = OrdPath::from_slice(left, Default {});
            let right = OrdPath::from_slice(right, Default {});

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
    fn default_encoding() {
        assert_eq!(
            Default::STAGES.map(|s| (s.prefix(), s.value_low(), s.value_high())),
            [
                (0b0000001, -281479271747928, -4295037273),
                (0b0000010, -4295037272, -69977),
                (0b0000011, -69976, -4441),
                (0b000010, -4440, -345),
                (0b000011, -344, -89),
                (0b00010, -88, -25),
                (0b00011, -24, -9),
                (0b001, -8, -1),
                (0b01, 0, 7),
                (0b100, 8, 23),
                (0b101, 24, 87),
                (0b1100, 88, 343),
                (0b1101, 344, 4439),
                (0b11100, 4440, 69975),
                (0b11101, 69976, 4295037271),
                (0b11110, 4295037272, 281479271747927)
            ]
        );
    }
}
