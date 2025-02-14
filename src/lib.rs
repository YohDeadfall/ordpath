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

mod enc;
mod error;
mod raw;
mod reader;
mod writer;

use raw::{RawOrdPath, RawOrdPathSlice};

pub use enc::*;
pub use error::*;
pub use raw::Bytes;
pub use reader::*;
pub use writer::*;

const USIZE_BYTES: usize = (usize::BITS / 8) as usize;

/// A data type representing an ORDPATH is stored as a continuous sequence of bytes.
pub struct OrdPath<E: Encoding = DefaultEncoding, const N: usize = USIZE_BYTES> {
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

    /// Encodes a slice `s` to return a new `OrdPath` with the specified encoding.
    ///
    /// # Panics
    ///
    /// This function might panic if the given slice contains ordinals that are
    /// out of the range the provided encoding supports, or the resulting
    /// ORDPATH exceeds the maximum supported length.
    ///
    /// See also [`OrdPath::try_from_ordinals`] which will return an [`Error`] rather than panicking.
    #[inline]
    pub fn from_ordinals(s: &[i64], enc: E) -> Self {
        Self::try_from_ordinals(s, enc).unwrap()
    }

    /// Parses a string `s` to return a new `OrdPath` with the specified encoding.
    ///
    /// # Panics
    ///
    /// This function might panic if the given string contains any value other
    /// than numbers separated by dots, or it contains numbers that are out of
    /// the range the provided encoding supports, or the resulting ORDPATH
    /// exceeds the maximum supported length.
    ///
    /// See also [`OrdPath::try_from_str`] which will return an [`Error`] rather than panicking.
    #[inline]
    pub fn from_str(s: &str, enc: E) -> Self {
        Self::try_from_str(s, enc).unwrap()
    }

    /// Creates an `OrdPath` from a byte slice `s`.
    ///
    /// # Panics
    ///
    /// This function might panic if the given slice is not a valid ORDPATH, it
    /// cannot be read by the provided encoding, or the given slice exceeds the
    /// maximum supported length.
    ///
    /// See also [`OrdPath::try_from_bytes`] which will return an [`Error`] rather than panicking.
    #[inline]
    pub fn from_bytes(s: &[u8], enc: E) -> Self {
        Self::try_from_bytes(s, enc).unwrap()
    }

    /// Tries to allocate a new `OrdPath` storing the slice.
    pub fn try_from_slice(s: OrdPathSlice<'_, E>) -> Result<Self, Error>
    where
        E: Clone,
    {
        let mut bytes = s.bytes();
        let mut path = Self::new(bytes.len(), s.encoding().clone())?;

        bytes.read_exact(path.raw.as_mut_slice())?;

        Ok(path)
    }

    /// Tries to encode a slice of ordinals `s` and create a new `OrdPath`.
    pub fn try_from_ordinals(s: &[i64], enc: E) -> Result<Self, Error> {
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

    /// Tries to parse a string `s` and create a new `OrdPath`.
    pub fn try_from_str(s: &str, enc: E) -> Result<Self, Error> {
        let mut v = Vec::new();
        for x in s.split_terminator('.') {
            v.push(x.parse::<i64>()?);
        }

        Self::try_from_ordinals(&v, enc)
    }

    /// Tries to create an `OrdPath` from a byte slice 's`.
    pub fn try_from_bytes(s: &[u8], enc: E) -> Result<Self, Error> {
        let mut bits = 0u8;
        let mut reader = Reader::new(s, &enc);
        while let Some((_, stage)) = reader.read()? {
            bits = bits.wrapping_add(stage.bits());
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

    /// An iterator over the bytes of an `OrdPath`.
    #[inline]
    pub fn bytes(&self) -> &[u8] {
        self.raw.as_slice()
    }

    /// An iterator over the ordinals of an `OrdPath`.
    #[inline]
    pub fn ordinals(&self) -> Ordinals<&[u8], &E> {
        Ordinals {
            reader: Reader::new(self.bytes(), self.encoding()),
        }
    }

    /// Returns `true` if `self` is empty.
    #[inline]
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.raw.len() == 0
    }

    /// Returns `true` if the data has spilled into a heap-allocated buffer.
    #[inline]
    pub fn spilled(&self) -> bool {
        self.raw.spilled()
    }

    /// Returns `true` if `self` is an ancestor of `other`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use ordpath::{DefaultEncoding, OrdPath};
    /// let a = <OrdPath>::from_ordinals(&[1, 2], DefaultEncoding);
    /// let d = <OrdPath>::from_ordinals(&[1, 2, 3], DefaultEncoding);
    /// assert!(a.is_ancestor_of(&d));
    /// ```
    //
    /// See also [`OrdPath::is_descendant_of`].
    #[inline]
    pub fn is_ancestor_of(&self, other: &Self) -> bool
    where
        E: PartialEq,
    {
        self.encoding().eq(other.encoding()) && self.raw.is_ancestor(&other.raw)
    }

    /// Returns `true` if `self` is an descendant of `other`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use ordpath::{DefaultEncoding, OrdPath};
    /// let a = <OrdPath>::from_ordinals(&[1, 2], DefaultEncoding);
    /// let d = <OrdPath>::from_ordinals(&[1, 2, 3], DefaultEncoding);
    /// assert!(d.is_descendant_of(&a));
    /// ```
    ///
    /// See also [`OrdPath::is_ancestor_of`].
    #[inline]
    pub fn is_descendant_of(&self, other: &Self) -> bool
    where
        E: PartialEq,
    {
        other.is_ancestor_of(self)
    }

    /// Returns the `OrdPath` without its final element, if there is one.
    ///
    /// # Examples
    ///
    /// ```
    /// # use ordpath::{DefaultEncoding, OrdPath};
    /// let path = <OrdPath>::from_ordinals(&[1, 2], DefaultEncoding);
    /// let parent = path.parent();
    /// assert_eq!(parent, Some(<OrdPath>::from_ordinals(&[1], DefaultEncoding).as_slice()));
    /// let grand_parent = parent.and_then(|p| p.parent());
    /// assert_eq!(grand_parent, Some(<OrdPath>::from_ordinals(&[], DefaultEncoding).as_slice()));
    /// let grand_grand_parent = grand_parent.and_then(|p| p.parent());
    /// assert_eq!(grand_grand_parent, None);
    /// ```
    pub fn parent(&self) -> Option<OrdPathSlice<'_, E>> {
        self.as_slice().parent()
    }

    /// Returns a slice containing the entire `OrdPath`.
    pub fn as_slice(&self) -> OrdPathSlice<E> {
        OrdPathSlice {
            raw: RawOrdPathSlice::new(self.bytes(), 0, self.raw.trailing_bits()),
            enc: self.encoding(),
        }
    }
}

impl<E: Encoding + PartialEq, const N: usize> PartialEq for OrdPath<E, N> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.encoding().eq(other.encoding()) && self.raw.eq(&other.raw)
    }
}

impl<E: Encoding + PartialEq, const N: usize> PartialOrd for OrdPath<E, N> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.encoding()
            .eq(other.encoding())
            .then(|| self.bytes().cmp(other.bytes()))
    }
}

impl<E: Encoding, const N: usize> Hash for OrdPath<E, N> {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        state.write(self);
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
            for value in ordinals {
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

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.ordinals()
    }
}

impl<E: Encoding + Default, const N: usize> FromStr for OrdPath<E, N> {
    type Err = Error;

    #[inline]
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
impl<Enc: Encoding + Default, const N: usize> Visitor<'_> for OrdPathVisitor<Enc, N> {
    type Value = OrdPath<Enc, N>;

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter.write_str("bytes")
    }

    fn visit_bytes<Err: serde::de::Error>(self, v: &[u8]) -> Result<Self::Value, Err> {
        Self::Value::try_from_bytes(v, Default::default()).map_err(Err::custom)
    }
}

/// A slice of an [`OrdPath`].
pub struct OrdPathSlice<'a, E: Encoding> {
    raw: RawOrdPathSlice<'a>,
    enc: &'a E,
}

impl<'a, E: Encoding> OrdPathSlice<'a, E> {
    /// Returns a reference to the used encoding.
    #[inline]
    pub fn encoding(&self) -> &'a E {
        self.enc
    }

    /// An iterator over the bytes of an `OrdPathSlice`.
    #[inline]
    pub fn bytes(&self) -> Bytes {
        self.raw.bytes()
    }

    /// An iterator over the ordinals of an `OrdPathSlice`.
    #[inline]
    pub fn ordinals(&self) -> Ordinals<Bytes, &E> {
        Ordinals {
            reader: Reader::new(self.bytes(), self.encoding()),
        }
    }

    /// Returns the `OrdPathSlice` without its final element, if there is one.
    ///
    /// See [`OrdPath::parent()`] for an example.
    pub fn parent(&self) -> Option<OrdPathSlice<'a, E>> {
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
                let mut bits_prev = stage.bits();
                while let Some((_, stage)) = reader.read().unwrap_unchecked() {
                    let bits_tmp = bits + bits_prev;

                    bits_prev = stage.bits();
                    bits = bits_tmp & 7;
                    bytes += bits_tmp as usize >> 3;
                }

                if bits > 0 || bytes > 0 {
                    bytes += bits.div_ceil(8) as usize;
                    bits &= 7;
                }
            }
        }

        Some(Self {
            raw: self.raw.take(bytes, (8 - bits) & 7),
            enc: self.encoding(),
        })
    }

    /// Creates an owned [`OrdPath`] by cloning the data.
    pub fn to_path<const N: usize>(&self) -> OrdPath<E, N>
    where
        E: Clone,
    {
        let mut bytes = self.bytes();
        let mut path = OrdPath::new(bytes.len(), self.encoding().clone()).unwrap();

        unsafe {
            // SAFETY: The path has the same size as the slice.
            bytes.read_exact(path.raw.as_mut_slice()).unwrap_unchecked();
        }

        path
    }
}

impl<E: Encoding + PartialEq> PartialEq for OrdPathSlice<'_, E> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.encoding().eq(other.encoding()) && self.raw.eq(&other.raw)
    }
}

impl<E: Encoding + PartialEq> PartialOrd for OrdPathSlice<'_, E> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.encoding()
            .eq(other.encoding())
            .then(|| self.bytes().cmp(other.bytes()))
    }
}

impl<E: Encoding> Hash for OrdPathSlice<'_, E> {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        for b in self.bytes() {
            state.write_u8(b);
        }
    }
}

impl<E: Encoding> Debug for OrdPathSlice<'_, E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <Self as Display>::fmt(self, f)
    }
}

impl<E: Encoding> Display for OrdPathSlice<'_, E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut ordinals = self.ordinals();
        if let Some(value) = ordinals.next() {
            write!(f, "{}", value)?;
            for value in ordinals {
                write!(f, ".{}", value)?;
            }
        }
        Ok(())
    }
}

impl<E: Encoding> Binary for OrdPathSlice<'_, E> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Binary::fmt(&self.raw, f)
    }
}

impl<E: Encoding> LowerHex for OrdPathSlice<'_, E> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        LowerHex::fmt(&self.raw, f)
    }
}

impl<E: Encoding> UpperHex for OrdPathSlice<'_, E> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        UpperHex::fmt(&self.raw, f)
    }
}

/// An iterator over the ordinals of an [`OrdPath`].
///
/// This struct is created by the [`ordinals`] method on [`OrdPath`].
/// See its documentation for more.
///
/// [`ordinals`]: OrdPath::ordinals
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
    fn path_from_ordinals() {
        fn assert(s: &[i64]) {
            assert_eq!(
                <OrdPath>::from_ordinals(s, DefaultEncoding)
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

        assert(&[3]);
        assert(&[3, 8 + 5]);
        assert(&[4440 + 13, 4440 + 179, 4440 + 7541, 8 + 11]);
        assert(&[4440 + 13, 4440 + 179, 4440 + 7541, 8 + 11, 3]);
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
                <OrdPath>::try_from_str(s, DefaultEncoding),
                Ok(<OrdPath>::from_ordinals(o, DefaultEncoding))
            );
        }

        fn assert_err(s: &str, e: Error) {
            assert_eq!(<OrdPath>::try_from_str(s, DefaultEncoding), Err(e.clone()));
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
            assert_eq!(<OrdPath>::from_ordinals(&o, DefaultEncoding).to_string(), s);
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
                <OrdPath>::from_ordinals(o, DefaultEncoding).clone(),
                <OrdPath>::from_ordinals(o, DefaultEncoding)
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
                <OrdPath>::from_ordinals(lhs, DefaultEncoding)
                    .cmp(&<OrdPath>::from_ordinals(rhs, DefaultEncoding)),
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
            let x = <OrdPath>::from_ordinals(a, DefaultEncoding);
            let y = <OrdPath>::from_ordinals(d, DefaultEncoding);

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

        assert(<OrdPath>::from_ordinals(&[1, 2], DefaultEncoding).ordinals());
    }

    #[test]
    fn path_parent() {
        fn parent(p: Option<OrdPath>) -> Option<OrdPath> {
            p.and_then(|p| p.parent().and_then(|p| OrdPath::try_from_slice(p).ok()))
        }

        fn assert(s: &[i64]) {
            let mut p = Some(<OrdPath>::from_ordinals(s, DefaultEncoding));
            for i in (0..s.len()).rev() {
                p = parent(p);
                assert_eq!(p, Some(OrdPath::from_ordinals(&s[..i], DefaultEncoding)));
            }
            assert_eq!(parent(p), None);
        }

        assert(&[1, 2]);
        assert(&[344, 345]);
    }

    #[cfg(feature = "serde")]
    #[test]
    fn path_serialization() {
        fn assert(s: &[i64]) {
            let p = <OrdPath>::from_ordinals(s, DefaultEncoding);
            let encoded = bincode::serialize(&p).unwrap();
            let decoded = bincode::deserialize(&encoded).unwrap();

            assert_eq!(p, decoded);
        }

        assert(&[0, 1, 2, 3]);
    }
}
