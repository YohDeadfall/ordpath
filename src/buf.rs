use std::io::{Read, Result};

pub(crate) struct BorrowedBuf<'data> {
    buf: &'data [u8],
    pos: usize,
}

impl<'data> From<&'data [u8]> for BorrowedBuf<'data> {
    fn from(value: &'data [u8]) -> Self {
        BorrowedBuf { buf: value, pos: 0 }
    }
}

impl<'data> Read for BorrowedBuf<'data> {
    fn read(&mut self, buf: &mut [u8]) -> Result<usize> {
        let consumed = buf.len().min(self.buf.len() - self.pos);
        if consumed > 0 {
            buf[..consumed].copy_from_slice(&self.buf[self.pos..self.pos + consumed]);
            self.pos += consumed;
        }

        Ok(consumed)
    }
}
