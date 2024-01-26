use std::{
    alloc,
    alloc::Layout,
    mem::{align_of, size_of, MaybeUninit},
    ptr::{addr_of, NonNull},
};

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

    pub const fn new(len: usize, trailing_bits: u8) -> Self {
        assert!(len < usize::MAX >> 4);
        assert!(trailing_bits < u8::BITS as u8 - 1);

        let on_heap = len > RawOrdPath::<N>::INLINE_DATA_LEN;
        let header = ((on_heap as usize) << 3) | trailing_bits as usize;

        Self((len << 4) | header)
    }

    pub const fn new_heap(len: usize, trailing_bits: u8) -> Self {
        assert!(len < usize::MAX >> 4);
        assert!(trailing_bits < u8::BITS as u8 - 1);

        Self((len << 4) | 8 | trailing_bits as usize)
    }

    pub const fn on_heap(&self) -> bool {
        self.0 & 8 == 8
    }

    pub const fn len(&self) -> usize {
        let meta = if self.on_heap() {
            self.0
        } else {
            self.0 & Self::INLINE_META_MASK
        };

        meta >> 4
    }

    pub const fn trailing_bits(&self) -> u8 {
        self.0 as u8 & 7
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

    pub fn new(len: usize, trailing_bits: u8) -> Self {
        let meta = Metadata::<N>::new(len, trailing_bits);
        let data = if meta.on_heap() {
            let layout = Layout::array::<u8>(len).unwrap();
            let ptr = NonNull::new(unsafe { alloc::alloc(layout) }).unwrap();

            RawOrdPathData::new_heap(ptr)
        } else {
            RawOrdPathData::<N>::new()
        };

        Self { meta, data }
    }

    pub fn new_heap(data: &[u8]) -> Self {
        let ptr = unsafe { NonNull::new_unchecked(data.as_ptr() as *mut u8) };

        Self {
            meta: Metadata::<N>::new_heap(data.len(), 0),
            data: RawOrdPathData::new_heap(ptr),
        }
    }

    pub const fn len(&self) -> usize {
        self.meta.len()
    }

    pub const fn trailing_bits(&self) -> u8 {
        self.meta.trailing_bits()
    }

    pub const fn as_ptr(&self) -> *const u8 {
        unsafe {
            if self.meta.on_heap() {
                self.data.heap.as_ptr()
            } else {
                // TODO: replace by transpose when maybe_uninit_uninit_array_transpose stabilizedi
                // https://github.com/rust-lang/rust/issues/96097
                addr_of!(self.data.inline)
                    .cast::<u8>()
                    .byte_sub(Self::INLINE_DATA_OFFSET)
            }
        }
    }
}

impl<const N: usize> Clone for RawOrdPath<N> {
    fn clone(&self) -> Self {
        unsafe {
            if self.meta.on_heap() {
                Self {
                    meta: self.meta,
                    data: RawOrdPathData::new_inline(self.data.inline),
                }
            } else {
                let other = Self::new(self.len(), self.trailing_bits());
                self.as_ptr()
                    .copy_to_nonoverlapping(other.as_ptr() as *mut u8, self.len());

                other
            }
        }
    }
}

impl<const N: usize> Drop for RawOrdPath<N> {
    fn drop(&mut self) {
        if self.meta.on_heap() {
            unsafe {
                alloc::dealloc(
                    self.as_ptr() as *mut u8,
                    Layout::from_size_align_unchecked(self.len(), align_of::<u8>()),
                );
            }
        }
    }
}
