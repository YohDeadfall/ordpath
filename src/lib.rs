//! A hierarchy labeling scheme called ORDPATH.

#![deny(missing_docs)]

use std::cmp::Ordering;
use std::fmt::{self, Binary, Debug, Display, LowerHex, UpperHex};
use std::hash::{Hash, Hasher};
use std::io::{self, Read, Write};
use std::iter::FusedIterator;
use std::ops::Deref;
use std::str::FromStr;

#[cfg(feature = "serde")]
use std::marker::PhantomData;

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
use raw::RawOrdPath;

pub use error::{Error, ErrorKind};
pub use reader::Reader;
pub use writer::Writer;

const USIZE_BYTES: usize = (usize::BITS / 8) as usize;

/// A data type representing an ORDPATH is stored as a continuous sequence of bytes.
pub struct OrdPath<E: Encoding = enc::Default, const N: usize = USIZE_BYTES> {
    raw: RawOrdPath<N>,
    enc: E,
}

impl<E: Encoding, const N: usize> OrdPath<E, N> {
    #[inline]
    fn new(len: usize, enc: E) -> Result<Self, Error> {
        Ok(Self {
            raw: RawOrdPath::new(len)?,
            enc,
        })
    }

    /// Encodes a slice `s` to return a new [OrdPath] with the specified encoding.
    ///
    /// # Panics
    ///
    /// This function might panic if the given slice contains ordinals that are
    /// out of the range the provided encoding supports, or the resulting
    /// ORDPATH exceeds the maximum supported length.
    ///
    /// See also [try_from_slice] which will return an [Error] rather than panicking.
    #[inline]
    pub fn from_slice(s: &[i64], enc: E) -> Self {
        Self::try_from_slice(s, enc).unwrap()
    }

    /// Parses a string `s` to return a new [OrdPath] with the specified encoding.
    ///
    /// # Panics
    ///
    /// This function might panic if the given string contains any value other
    /// than numbers separated by dots, or it contains numbers that are out of
    /// the range the provided encoding supports, or the resulting ORDPATH
    /// exceeds the maximum supported length.
    ///
    /// See also [try_from_str] which will return an [Error] rather than panicking.
    #[inline]
    pub fn from_str(s: &str, enc: E) -> Self {
        Self::try_from_str(s, enc).unwrap()
    }

    /// Creates an [OrdPath] from a byte slice `s`.
    ///
    /// # Panics
    /// This function might panic if the given slice is not a valid ORDPATH, it
    /// cannot be read by the provided encoding, or the given slice exceeds the
    /// maximum supported length.
    ///
    /// See also [try_from_bytes] which will return an [Error] rather than panicking.
    pub fn from_bytes(s: &[u8], enc: E) -> Self {
        Self::try_from_bytes(s, enc).unwrap()
    }

    /// Tries to encode a slice of ordinals `s`.
    pub fn try_from_slice(s: &[i64], enc: E) -> Result<Self, Error> {
        let mut len = Len(0);
        let mut writer = Writer::new(&mut len, &enc);
        for ordinal in s {
            writer.write(*ordinal)?;
        }

        drop(writer);

        let mut path = Self::new(len.0, enc)?;
        let mut writer = Writer::new(path.raw.as_mut_slice(), &path.enc);
        for ordinal in s {
            writer.write(*ordinal)?;
        }

        let bits = writer.trailing_bits();

        drop(writer);
        path.raw.set_trailing_bits(bits);

        Ok(path)
    }

    /// Tries to parse a string `s` and create a new [OrdPath].
    pub fn try_from_str(s: &str, enc: E) -> Result<Self, Error> {
        let mut v = Vec::new();
        for x in s.split_terminator('.') {
            v.push(i64::from_str_radix(x, 10)?);
        }

        Self::try_from_slice(&v, enc)
    }

    /// Tries to create an [OrdPath] from a byte slice 's`.
    pub fn try_from_bytes(s: &[u8], enc: E) -> Result<Self, Error> {
        let mut bits = 0u8;
        let mut reader = Reader::new(s, &enc);
        while let Some((_, stage)) = reader.read()? {
            bits = bits.wrapping_add(stage.len());
        }

        let mut path = Self::new(s.len(), enc)?;

        path.raw.as_mut_slice().copy_from_slice(s);
        path.raw.set_trailing_bits(bits);

        Ok(path)
    }

    /// Returns a reference to the used encoding.
    #[inline]
    pub fn encoding(&self) -> &E {
        &self.enc
    }

    /// An iterator over the bytes of an ORDPATH.
    #[inline]
    pub fn bytes(&self) -> &[u8] {
        self.raw.as_slice()
    }

    /// An iterator over the ordinals of an ORDPATH.
    #[inline]
    pub fn ordinals(&self) -> Ordinals<&[u8], &E> {
        Ordinals {
            reader: Reader::new(self.bytes(), self.encoding()),
        }
    }

    /// Returns `true` if `self` is empty.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.raw.len() == 0
    }

    /// Returns true if the data has spilled into a heap-allocated buffer.
    #[inline]
    pub fn spilled(&self) -> bool {
        self.raw.spilled()
    }

    /// Returns `true` if `self` is an ancestor of `other`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use ordpath::{enc, OrdPath};
    /// let a = <OrdPath>::from_slice(&[1, 2], enc::Default);
    /// let d = <OrdPath>::from_slice(&[1, 2, 3], enc::Default);
    /// assert!(a.is_ancestor_of(&d));
    /// ```
    //
    /// See also [is_descendant_of].
    pub fn is_ancestor_of(&self, other: &Self) -> bool {
        self.encoding().eq(other.encoding()) && self.raw.is_ancestor(&other.raw)
    }

    /// Returns `true` if `self` is an descendant of `other`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use ordpath::{enc, OrdPath};
    /// let a = <OrdPath>::from_slice(&[1, 2], enc::Default);
    /// let d = <OrdPath>::from_slice(&[1, 2, 3], enc::Default);
    /// assert!(d.is_descendant_of(&a));
    /// ```
    ///
    /// See also [is_ancestor_of].
    pub fn is_descendant_of(&self, other: &Self) -> bool {
        other.is_ancestor_of(self)
    }

    /// Returns the `OrdPath<E>` without its final element, if there is one.
    ///
    /// # Examples
    ///
    /// ```
    /// # use ordpath::{enc, OrdPath};
    /// let path = <OrdPath>::from_slice(&[1, 2], enc::Default);
    /// let parent = path.parent();
    /// assert_eq!(parent, Some(<OrdPath>::from_slice(&[1], enc::Default)));
    /// let grand_parent = parent.and_then(|p| p.parent());
    /// assert_eq!(grand_parent, Some(<OrdPath>::from_slice(&[], enc::Default)));
    /// let grand_grand_parent = grand_parent.and_then(|p| p.parent());
    /// assert_eq!(grand_grand_parent, None);
    /// ```
    pub fn parent(&self) -> Option<Self>
    where
        E: Clone,
    {
        let src = self.bytes();
        if src.is_empty() {
            return None;
        }

        let mut bits = 0u8;
        let mut bytes = 0;
        let mut reader = Reader::new(src, self.encoding());
        unsafe {
            // SAFETY: Validation of the data happens on creation even for a byte slice.
            if let Some((_, stage)) = reader.read().unwrap_unchecked() {
                let mut prev_len = stage.len();
                while let Some((_, stage)) = reader.read().unwrap_unchecked() {
                    let len = bits + prev_len;

                    prev_len = stage.len();
                    bytes += len as usize >> 3;
                    bits = len & 7;
                }

                if bits > 0 || bytes > 0 {
                    bytes += bits.div_ceil(8) as usize;
                    bits = bits & 7;
                }
            }
        }

        let mut path = Self::new(bytes, self.encoding().clone()).unwrap();
        let dst = path.raw.as_mut_slice();
        if dst.len() > 0 {
            dst.copy_from_slice(&src[..dst.len()]);

            let bits = (8 - bits) & 7;
            let last = &mut dst[dst.len() - 1];

            *last = *last & (u8::MAX << bits);
            path.raw.set_trailing_bits(bits);
        }

        Some(path)
    }
}

impl<E: Encoding, const N: usize> PartialEq for OrdPath<E, N> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.encoding().eq(other.encoding()) && self.raw.eq(&other.raw)
    }
}

impl<E: Encoding, const N: usize> Eq for OrdPath<E, N> {}

impl<E: Encoding, const N: usize> PartialOrd for OrdPath<E, N> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.encoding()
            .eq(other.encoding())
            .then(|| self.bytes().cmp(other.bytes()))
    }
}

impl<E: Encoding + Ord, const N: usize> Ord for OrdPath<E, N> {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        self.encoding()
            .cmp(other.encoding())
            .then_with(|| self.bytes().cmp(other.bytes()))
    }
}

impl<E: Encoding, const N: usize> Hash for OrdPath<E, N> {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        state.write(&self);
    }
}

impl<E: Encoding + Clone, const N: usize> Clone for OrdPath<E, N> {
    #[inline]
    fn clone(&self) -> Self {
        Self {
            raw: self.raw.clone(),
            enc: self.enc.clone(),
        }
    }
}

impl<E: Encoding, const N: usize> Deref for OrdPath<E, N> {
    type Target = [u8];

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.bytes()
    }
}

impl<E: Encoding, const N: usize> Debug for OrdPath<E, N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <Self as Display>::fmt(self, f)
    }
}

impl<E: Encoding, const N: usize> Display for OrdPath<E, N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut ordinals = self.ordinals();
        if let Some(value) = ordinals.next() {
            write!(f, "{}", value)?;
            while let Some(value) = ordinals.next() {
                write!(f, ".{}", value)?;
            }
        }
        Ok(())
    }
}

impl<E: Encoding, const N: usize> Binary for OrdPath<E, N> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Binary::fmt(&self.raw, f)
    }
}

impl<E: Encoding, const N: usize> LowerHex for OrdPath<E, N> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        LowerHex::fmt(&self.raw, f)
    }
}

impl<E: Encoding, const N: usize> UpperHex for OrdPath<E, N> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        UpperHex::fmt(&self.raw, f)
    }
}

impl<'a, E: Encoding, const N: usize> IntoIterator for &'a OrdPath<E, N> {
    type Item = i64;
    type IntoIter = Ordinals<&'a [u8], &'a E>;

    fn into_iter(self) -> Self::IntoIter {
        self.ordinals()
    }
}

impl<E: Encoding + Default, const N: usize> FromStr for OrdPath<E, N> {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::try_from_str(s, Default::default())
    }
}

#[cfg(feature = "serde")]
#[cfg_attr(docsrs, doc(cfg(feature = "serde")))]
impl<E: Encoding, const N: usize> Serialize for OrdPath<E, N> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        self.bytes().serialize(serializer)
    }
}

#[cfg(feature = "serde")]
#[cfg_attr(docsrs, doc(cfg(feature = "serde")))]
impl<'de, E: Encoding + Default, const N: usize> Deserialize<'de> for OrdPath<E, N> {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_bytes(OrdPathVisitor::<E, N> {
            marker: PhantomData,
        })
    }
}

#[cfg(feature = "serde")]
struct OrdPathVisitor<Enc, const N: usize> {
    marker: PhantomData<Enc>,
}

#[cfg(feature = "serde")]
impl<'de, Enc: Encoding + Default, const N: usize> Visitor<'de> for OrdPathVisitor<Enc, N> {
    type Value = OrdPath<Enc, N>;

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter.write_str("bytes")
    }

    fn visit_bytes<Err: serde::de::Error>(self, v: &[u8]) -> Result<Self::Value, Err> {
        Self::Value::try_from_bytes(v, Default::default()).map_err(Err::custom)
    }
}

/// An iterator over the ordinals of an ORDPATH.
///
/// This struct is created by the [`ordinals`] method on [`OrdPath`].
/// See its documentation for more.
///
/// ['ordinals']: OrdPath::ordinals
pub struct Ordinals<R: Read, E: Encoding> {
    reader: Reader<R, E>,
}

impl<R: Read, E: Encoding> Iterator for Ordinals<R, E> {
    type Item = i64;

    fn next(&mut self) -> Option<Self::Item> {
        self.reader.read().unwrap().map(|x| x.0)
    }
}

impl<R: Read, E: Encoding> FusedIterator for Ordinals<R, E> {}

struct Len(usize);

impl Write for Len {
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn path_from_slice() {
        fn assert(s: &[i64]) {
            assert_eq!(
                <OrdPath>::from_slice(s, enc::Default)
                    .into_iter()
                    .collect::<Vec<_>>(),
                s
            );
        }

        assert(&[0; 0]);
        assert(&[0]);
        assert(&[0, 8]);
        assert(&[4440, 4440, 4440, 8]);
        assert(&[4440, 4440, 4440, 8, 0]);
        assert(&[4440, 4440, 4440, 4440]);
        assert(&[4440, 4440, 4440, 4440, 88]);
        assert(&[4295037272, 4295037272]);
        assert(&[4295037272, 4295037272, 4440, 88]);
        assert(&[4295037272, 4295037272, 4440, 344]);
        assert(&[4295037272, 4295037272, 4440, 4440]);

        assert(&[0 + 3]);
        assert(&[0 + 3, 8 + 5]);
        assert(&[4440 + 13, 4440 + 179, 4440 + 7541, 8 + 11]);
        assert(&[4440 + 13, 4440 + 179, 4440 + 7541, 8 + 11, 0 + 3]);
        assert(&[4440 + 13, 4440 + 179, 4440 + 7541, 4440 + 123]);
        assert(&[4440 + 13, 4440 + 179, 4440 + 7541, 4440 + 123, 88 + 11]);
        assert(&[4295037272 + 31, 4295037272 + 6793]);
        assert(&[4295037272 + 31, 4295037272 + 6793, 4440 + 7541, 88 + 11]);
        assert(&[4295037272 + 31, 4295037272 + 6793, 4440 + 7541, 344 + 71]);
        assert(&[4295037272 + 31, 4295037272 + 6793, 4440 + 7541, 4440 + 123]);
    }

    #[test]
    fn path_from_str() {
        fn assert(s: &str, o: &[i64]) {
            assert_eq!(
                <OrdPath>::try_from_str(s, enc::Default),
                Ok(<OrdPath>::from_slice(o, enc::Default))
            );
        }

        fn assert_err(s: &str, e: Error) {
            assert_eq!(<OrdPath>::try_from_str(s, enc::Default), Err(e.clone()));
        }

        assert("", &[]);
        assert("0", &[0]);
        assert("1", &[1]);
        assert("1.2", &[1, 2]);
        assert_err("1.a", Error::new(ErrorKind::InvalidInput));
        assert_err("1_2", Error::new(ErrorKind::InvalidInput));
        assert_err("a", Error::new(ErrorKind::InvalidInput));
    }

    #[test]
    fn path_to_string() {
        fn assert(o: Vec<i64>, s: &str) {
            assert_eq!(<OrdPath>::from_slice(&o, enc::Default).to_string(), s);
        }

        assert(vec![], "");
        assert(vec![0], "0");
        assert(vec![1], "1");
        assert(vec![1, 2], "1.2");
    }

    #[test]
    fn path_clone() {
        fn assert(o: &[i64]) {
            assert_eq!(
                <OrdPath>::from_slice(&o, enc::Default).clone(),
                <OrdPath>::from_slice(&o, enc::Default)
            );
        }

        assert(&[]);
        assert(&[0]);
        assert(&[1]);
        assert(&[1, 2]);
    }

    #[test]
    fn path_ordering() {
        fn assert(lhs: &[i64], rhs: &[i64], o: Ordering) {
            assert_eq!(
                <OrdPath>::from_slice(lhs, enc::Default)
                    .cmp(&<OrdPath>::from_slice(rhs, enc::Default)),
                o
            );
        }

        assert(&[0; 0], &[0; 0], Ordering::Equal);
        assert(&[0; 0], &[0], Ordering::Less);
        assert(&[0], &[0; 0], Ordering::Greater);
        assert(&[0], &[0], Ordering::Equal);
        assert(&[0], &[1], Ordering::Less);
        assert(&[0], &[0, 1], Ordering::Less);
        assert(&[0], &[69976, 69976], Ordering::Less);
        assert(&[0], &[4295037272, 4295037272], Ordering::Less);
    }

    #[test]
    fn path_is_ancestor() {
        fn assert(e: bool, a: &[i64], d: &[i64]) {
            let x = <OrdPath>::from_slice(&a, enc::Default);
            let y = <OrdPath>::from_slice(&d, enc::Default);

            assert_eq!(e, x.is_ancestor_of(&y));
            assert_eq!(e, y.is_descendant_of(&x));
        }

        assert(true, &[], &[0]);
        assert(true, &[0], &[0, 1]);
        assert(true, &[0, 1], &[0, 1, 2, 3]);
        assert(
            true,
            &[4295037272, 4295037272],
            &[4295037272, 4295037272, 1],
        );

        assert(false, &[0], &[]);
        assert(false, &[0, 1], &[0]);
        assert(false, &[0, 1, 2, 3], &[0, 1]);
        assert(
            false,
            &[4295037272, 4295037272, 1],
            &[4295037272, 4295037272],
        );

        assert(false, &[], &[]);
        assert(false, &[0], &[0]);
        assert(false, &[0], &[1]);
    }

    #[test]
    fn path_iter_fused() {
        fn assert<R: Read, E: Encoding>(mut iter: Ordinals<R, E>) {
            assert_eq!(iter.next(), Some(1));
            assert_eq!(iter.next(), Some(2));
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);
        }

        assert(<OrdPath>::from_slice(&[1, 2], enc::Default).ordinals());
    }

    #[test]
    fn path_parent() {
        fn assert(s: &[i64]) {
            let mut p = Some(<OrdPath>::from_slice(s, enc::Default));
            for i in (0..s.len()).rev() {
                p = p.and_then(|p| p.parent());
                assert_eq!(p, Some(OrdPath::from_slice(&s[..i], enc::Default)));
            }
            assert_eq!(p.and_then(|p| p.parent()), None);
        }

        assert(&[1, 2]);
        assert(&[344, 345]);
    }

    #[cfg(feature = "serde")]
    #[test]
    fn path_serialization() {
        fn assert(s: &[i64]) {
            let p = <OrdPath>::from_slice(s, enc::Default);
            let encoded = bincode::serialize(&p).unwrap();
            let decoded = bincode::deserialize(&encoded).unwrap();

            assert_eq!(p, decoded);
        }

        assert(&[0, 1, 2, 3]);
    }
}
