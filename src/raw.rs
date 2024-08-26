use std::alloc::{self, Layout};
use std::cmp::Ordering;
use std::fmt::{Binary, LowerHex, UpperHex};
use std::mem::{align_of, size_of, MaybeUninit};
use std::ptr::{addr_of, addr_of_mut, NonNull};
use std::slice;

use crate::{Error, ErrorKind};

#[derive(Clone, Copy)]
struct Metadata<const N: usize>(usize);

impl<const N: usize> Metadata<N> {
    const INLINE_META_MASK: usize =
        usize::MAX >> (usize::BITS - u8::BITS * RawOrdPath::<N>::INLINE_META_LEN as u32);

    pub const fn size_for(data: usize) -> usize {
        let len_bits = usize::BITS - data.leading_zeros();
        let meta_bits = len_bits + 4;

        meta_bits.div_ceil(u8::BITS) as usize
    }

    pub const fn new(len: usize) -> Result<Self, Error> {
        if len < isize::MAX as usize {
            let heap = len > RawOrdPath::<N>::INLINE_DATA_LEN;
            let meta = (len << 1) | heap as usize;

            Ok(Self(meta))
        } else {
            Err(Error::new(ErrorKind::CapacityOverflow))
        }
    }

    pub const fn on_heap(&self) -> bool {
        self.0 & 1 == 1
    }

    pub const fn len(&self) -> usize {
        let meta = if self.on_heap() {
            self.0
        } else {
            self.0 & Self::INLINE_META_MASK
        };

        meta >> 1
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
    meta: Metadata<N>,
    data: RawOrdPathData<N>,
    #[cfg(target_endian = "big")]
    meta: Metadata<N>,
}

impl<const N: usize> RawOrdPath<N> {
    pub const INLINE_META_LEN: usize = {
        const fn max(lhs: usize, rhs: usize) -> usize {
            if lhs > rhs {
                lhs
            } else {
                rhs
            }
        }

        let data = max(N, size_of::<NonNull<u8>>());
        let len = Metadata::<N>::size_for(data);

        let data = size_of::<RawOrdPath<N>>() - len;
        let len = Metadata::<N>::size_for(data);

        len
    };

    pub const INLINE_DATA_LEN: usize = size_of::<RawOrdPath<N>>() - Self::INLINE_META_LEN;
    pub const INLINE_DATA_OFFSET: usize = if cfg!(target_endian = "little") {
        size_of::<Metadata<N>>() - Self::INLINE_META_LEN
    } else {
        0
    };

    pub fn new(len: usize) -> Result<Self, Error> {
        let len = match len {
            0 => 0,
            l => l + 1,
        };
        let meta = Metadata::<N>::new(len)?;
        let data = if meta.on_heap() {
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
        self.meta.len().saturating_sub(1)
    }

    #[inline]
    pub const fn spilled(&self) -> bool {
        self.meta.on_heap()
    }

    #[inline]
    pub const fn trailing_bits(&self) -> u8 {
        match self.meta.len() {
            0 => 0,
            l => unsafe { self.as_ptr().add(l - 1).read() },
        }
    }

    #[inline]
    pub fn set_trailing_bits(&mut self, bits: u8) {
        match self.meta.len() {
            0 => (),
            l => unsafe { self.as_mut_ptr().add(l - 1).write(bits) },
        };
    }

    #[inline]
    pub const fn as_ptr(&self) -> *const u8 {
        unsafe {
            if self.meta.on_heap() {
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
            if self.meta.on_heap() {
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

        if self_slice.len() > 0 && self_slice.len() <= other_slice.len() {
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

        self_slice.len() == 0 && other_slice.len() != 0
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
    fn cmp(&self, other: &Self) -> Ordering {
        let self_slice = self.as_slice();
        let other_slice = other.as_slice();

        match self_slice.len().min(other_slice.len()) {
            0 => self_slice.len().cmp(&other_slice.len()),
            l => self_slice[..l - 1]
                .cmp(&other_slice[..l - 1])
                .then_with(|| {
                    let self_mask = u8::MAX
                        << if l == self_slice.len() {
                            self.trailing_bits()
                        } else {
                            0
                        };
                    let other_mask = u8::MAX
                        << if l == other_slice.len() {
                            other.trailing_bits()
                        } else {
                            0
                        };

                    let i = l - 1;
                    let self_last = self_slice[i] & self_mask;
                    let other_last = other_slice[i] & other_mask;

                    self_last
                        .cmp(&other_last)
                        .then_with(|| self_mask.cmp(&other_mask))
                }),
        }
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
            write!(f, "{b:0>8x}")?;
        }
        Ok(())
    }
}

impl<const N: usize> UpperHex for RawOrdPath<N> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for b in self.as_slice() {
            write!(f, "{b:0>8X}")?;
        }
        Ok(())
    }
}

impl<const N: usize> Clone for RawOrdPath<N> {
    fn clone(&self) -> Self {
        unsafe {
            if self.meta.on_heap() {
                // SAFETY: Safe becuase the clone has the same length.
                let mut other = Self::new(self.len()).unwrap_unchecked();
                self.as_ptr()
                    .copy_to_nonoverlapping(other.as_mut_ptr() as *mut u8, self.len());

                other
            } else {
                Self {
                    meta: self.meta,
                    data: RawOrdPathData::new_inline(self.data.inline),
                }
            }
        }
    }
}

impl<const N: usize> Drop for RawOrdPath<N> {
    fn drop(&mut self) {
        if self.meta.on_heap() {
            unsafe {
                alloc::dealloc(
                    self.as_mut_ptr(),
                    Layout::from_size_align_unchecked(self.len(), align_of::<u8>()),
                );
            }
        }
    }
}
