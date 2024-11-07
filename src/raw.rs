use std::alloc::{self, Layout};
use std::cmp::Ordering;
use std::fmt::{Binary, LowerHex, UpperHex};
use std::mem::{align_of, size_of, MaybeUninit};
use std::ptr::{addr_of, addr_of_mut, NonNull};
use std::slice;

use crate::{Error, ErrorKind};

#[derive(Clone, Copy)]
struct Metadata(usize);

impl Metadata {
    pub const fn bytes_for(data: usize) -> usize {
        let len_bits = usize::BITS - data.leading_zeros();
        len_bits.div_ceil(u8::BITS) as usize
    }

    #[inline]
    pub const fn new(len: usize, spilled: bool) -> Result<Self, Error> {
        if len < isize::MAX as usize {
            Ok(Self((len << 1) | spilled as usize))
        } else {
            Err(Error::new(ErrorKind::CapacityOverflow))
        }
    }

    #[inline]
    pub const fn len(&self, mask: usize) -> usize {
        (self.0 & mask) >> 1
    }

    #[inline]
    pub const fn spilled(&self) -> bool {
        (self.0 & 1) == 1
    }
}

union RawOrdPathData<const N: usize> {
    inline: MaybeUninit<[u8; N]>,
    heap: NonNull<u8>,
}

impl<const N: usize> RawOrdPathData<N> {
    pub const fn new() -> Self {
        Self::new_inline(MaybeUninit::uninit())
    }

    pub const fn new_inline(data: MaybeUninit<[u8; N]>) -> Self {
        Self { inline: data }
    }

    pub const fn new_heap(data: NonNull<u8>) -> Self {
        Self { heap: data }
    }
}

#[repr(C)]
pub(crate) struct RawOrdPath<const N: usize> {
    #[cfg(target_endian = "little")]
    meta: Metadata,
    data: RawOrdPathData<N>,
    #[cfg(target_endian = "big")]
    meta: Metadata,
}

impl<const N: usize> RawOrdPath<N> {
    const INLINE_META_LEN: usize = {
        const fn max(lhs: usize, rhs: usize) -> usize {
            if lhs > rhs {
                lhs
            } else {
                rhs
            }
        }

        let data = max(N, size_of::<NonNull<u8>>());
        let len = Metadata::bytes_for(data);

        let data = size_of::<RawOrdPath<N>>() - len;

        Metadata::bytes_for(data)
    };

    const INLINE_META_MASK: usize =
        usize::MAX >> (usize::BITS - u8::BITS * RawOrdPath::<N>::INLINE_META_LEN as u32);

    const INLINE_DATA_LEN: usize = size_of::<RawOrdPath<N>>() - Self::INLINE_META_LEN;
    const INLINE_DATA_OFFSET: usize = if cfg!(target_endian = "little") {
        size_of::<Metadata>() - Self::INLINE_META_LEN
    } else {
        0
    };

    pub fn new(len: usize) -> Result<Self, Error> {
        let len = match len {
            0 => 0,
            l => l + 1,
        };
        let meta = Metadata::new(len, len > Self::INLINE_DATA_LEN)?;
        let data = if meta.spilled() {
            let layout = Layout::array::<u8>(len).unwrap();
            let ptr = NonNull::new(unsafe { alloc::alloc(layout) }).unwrap();

            RawOrdPathData::new_heap(ptr)
        } else {
            RawOrdPathData::<N>::new()
        };

        Ok(Self { meta, data })
    }

    #[inline]
    pub const fn len(&self) -> usize {
        self.meta.len(Self::INLINE_META_MASK).saturating_sub(1)
    }

    #[inline]
    pub const fn spilled(&self) -> bool {
        self.meta.spilled()
    }

    #[inline]
    pub const fn trailing_bits(&self) -> u8 {
        match self.len() {
            0 => 0,
            l => unsafe { self.as_ptr().byte_add(l).read() },
        }
    }

    #[inline]
    pub fn set_trailing_bits(&mut self, bits: u8) {
        match self.len() {
            0 => (),
            l => unsafe { self.as_mut_ptr().byte_add(l).write(bits) },
        };
    }

    #[inline]
    pub const fn as_ptr(&self) -> *const u8 {
        unsafe {
            if self.spilled() {
                self.data.heap.as_ptr()
            } else {
                // TODO: replace by transpose when maybe_uninit_uninit_array_transpose stabilized.
                // https://github.com/rust-lang/rust/issues/96097
                addr_of!(self.data.inline)
                    .cast::<u8>()
                    .byte_sub(Self::INLINE_DATA_OFFSET)
            }
        }
    }

    #[inline]
    pub fn as_mut_ptr(&mut self) -> *mut u8 {
        unsafe {
            if self.spilled() {
                self.data.heap.as_ptr()
            } else {
                // TODO: replace by transpose when maybe_uninit_uninit_array_transpose stabilized.
                // https://github.com/rust-lang/rust/issues/96097
                addr_of_mut!(self.data.inline)
                    .cast::<u8>()
                    .byte_sub(Self::INLINE_DATA_OFFSET)
            }
        }
    }

    #[inline]
    pub const fn as_slice(&self) -> &[u8] {
        unsafe { slice::from_raw_parts(self.as_ptr(), self.len()) }
    }

    #[inline]
    pub fn as_mut_slice(&mut self) -> &mut [u8] {
        unsafe { slice::from_raw_parts_mut(self.as_mut_ptr(), self.len()) }
    }

    pub fn is_ancestor(&self, other: &Self) -> bool {
        let self_slice = self.as_slice();
        let other_slice = other.as_slice();

        if !self_slice.is_empty() && self_slice.len() <= other_slice.len() {
            let len = self_slice.len() - 1;

            if self_slice[..len].eq(&other_slice[..len]) {
                let bits = self.trailing_bits();
                let mask = if self_slice.len() == other_slice.len() && bits <= other.trailing_bits()
                {
                    return false;
                } else {
                    u8::MAX << bits
                };

                let self_last = self_slice[len] & mask;
                let other_last = other_slice[len] & mask;

                return self_last == other_last;
            }
        }

        self_slice.is_empty() && !other_slice.is_empty()
    }
}

impl<const N: usize> PartialEq for RawOrdPath<N> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.as_slice().eq(other.as_slice())
    }
}

impl<const N: usize> Eq for RawOrdPath<N> {}

impl<const N: usize> PartialOrd for RawOrdPath<N> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<const N: usize> Ord for RawOrdPath<N> {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        self.as_slice().cmp(other.as_slice())
    }
}

impl<const N: usize> Binary for RawOrdPath<N> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for b in self.as_slice() {
            write!(f, "{b:0>8b}")?;
        }
        Ok(())
    }
}

impl<const N: usize> LowerHex for RawOrdPath<N> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for b in self.as_slice() {
            write!(f, "{b:0>2x}")?;
        }
        Ok(())
    }
}

impl<const N: usize> UpperHex for RawOrdPath<N> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for b in self.as_slice() {
            write!(f, "{b:0>2X}")?;
        }
        Ok(())
    }
}

impl<const N: usize> Clone for RawOrdPath<N> {
    fn clone(&self) -> Self {
        let mut other = Self::new(self.len()).unwrap();
        other.as_mut_slice().clone_from_slice(self.as_slice());
        other.set_trailing_bits(self.trailing_bits());
        other
    }
}

impl<const N: usize> Drop for RawOrdPath<N> {
    fn drop(&mut self) {
        if self.meta.spilled() {
            unsafe {
                alloc::dealloc(
                    self.as_mut_ptr(),
                    Layout::from_size_align_unchecked(self.len(), align_of::<u8>()),
                );
            }
        }
    }
}
