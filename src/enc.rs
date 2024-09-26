//! Types and traits used for encoding.

use std::fmt;

/// An encoding stage used for vlue compression.
#[derive(PartialEq, Eq)]
pub struct Stage {
    bits: u8,
    prefix: u8,
    prefix_bits: u8,
    ordinal_bits: u8,
    ordinal_min: i64,
}

impl Stage {
    /// Constructs a stage with the given prefix and value range.
    pub const fn new(prefix: u8, prefix_bits: u8, ordinal_bits: u8, ordinal_min: i64) -> Stage {
        assert!(prefix_bits < 8);
        assert!(ordinal_bits < 64);

        Stage {
            bits: prefix_bits + ordinal_bits,
            prefix,
            prefix_bits,
            ordinal_bits,
            ordinal_min,
        }
    }

    /// Returs the prefix identifying the stage.
    #[inline]
    pub const fn prefix(&self) -> u8 {
        self.prefix
    }

    /// Returns the number of bits used to encode the prefix.
    #[inline]
    pub const fn prefix_bits(&self) -> u8 {
        self.prefix_bits
    }

    /// Returns the lowest value which can be encoded by the stage.
    #[inline]
    pub const fn ordinal_min(&self) -> i64 {
        self.ordinal_min
    }

    /// Returns the upper value which can be encoded by the stage.
    #[inline]
    pub const fn ordinal_max(&self) -> i64 {
        self.ordinal_min + ((1 << self.ordinal_bits) - 1)
    }

    /// Returns the number of bits used to encode the value part.
    #[inline]
    pub const fn ordinal_bits(&self) -> u8 {
        self.ordinal_bits
    }

    /// Returns the total number of bits used to encode a value.
    #[inline]
    pub const fn bits(&self) -> u8 {
        self.bits
    }
}

impl fmt::Debug for Stage {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // TODO: Use field_with when it's stabilized (https://github.com/rust-lang/rust/issues/117729).
        struct Prefix<'s>(&'s Stage);

        impl<'s> fmt::Debug for Prefix<'s> {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                let prefix = self.0.prefix();
                let prefix_len = self.0.prefix_bits() as usize;

                f.write_fmt(format_args!("{prefix:0>prefix_len$b}"))
            }
        }

        let prefix = Prefix(self);

        f.debug_struct("Stage")
            .field("prefix", &prefix)
            .field("prefix_bits", &self.prefix_bits())
            .field("ordinal_bits", &self.ordinal_bits())
            .field("ordinal_min", &self.ordinal_min())
            .field("ordinal_max", &self.ordinal_max())
            .finish()
    }
}

/// An implementation of `Encoding` is responsible for providing a [`Stage`]
/// for the provided value or prefix.
pub trait Encoding {
    /// Returns a reference to the [`Stage`] corresponding to the prefix.
    fn stage_by_prefix(&self, prefix: u8) -> Option<&Stage>;

    /// Returns a reference to the [`Stage`] which range contains the value.
    fn stage_by_value(&self, value: i64) -> Option<&Stage>;
}

impl<E: Encoding + ?Sized> Encoding for &E {
    fn stage_by_prefix(&self, prefix: u8) -> Option<&Stage> {
        (*self).stage_by_prefix(prefix)
    }

    fn stage_by_value(&self, value: i64) -> Option<&Stage> {
        (*self).stage_by_value(value)
    }
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
        #[derive(Copy, Clone, Default, PartialEq, Eq, PartialOrd, Ord)]
        $v struct $t;

        impl $t {
            const STAGES: [$crate::enc::Stage; count!($($prefix,)*)] = {
                let mut stages = [
                    $($crate::enc::Stage::new($prefix, $prefix_len, $value_len, 0)),+
                ];

                let origin = stages.len() / 2;

                let mut index = origin;
                while index > 0  {
                    index -= 1;
                    stages[index] = $crate::enc::Stage::new(
                        stages[index].prefix(),
                        stages[index].prefix_bits(),
                        stages[index].ordinal_bits(),
                        stages[index + 1].ordinal_min() - stages[index].ordinal_max() - 1);
                }

                let mut index = origin;
                while index + 1 < stages.len() {
                    index += 1;
                    stages[index] = $crate::enc::Stage::new(
                        stages[index].prefix(),
                        stages[index].prefix_bits(),
                        stages[index].ordinal_bits(),
                        stages[index - 1].ordinal_max() + 1);
                }

                stages
            };

            const STAGE_LOOKUP_LEN: usize = 1 << u8::BITS as usize;
            const STAGE_LOOKUP: [u8; Self::STAGE_LOOKUP_LEN] = {
                let mut lookup = [u8::MAX; Self::STAGE_LOOKUP_LEN];
                let mut index = 0;
                while index < Self::STAGES.len() {
                    let stage = &Self::STAGES[index];
                    let prefix_offset = u8::BITS as u8 - stage.prefix_bits();
                    let prefix = stage.prefix() << prefix_offset;
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

        impl $crate::enc::Encoding for $t {
            #[inline]
            fn stage_by_prefix(&self, prefix: u8) -> ::std::option::Option<&$crate::enc::Stage> {
                Self::STAGES.get(Self::STAGE_LOOKUP[prefix as usize] as usize)
            }

            #[inline]
            fn stage_by_value(&self, value: i64) -> ::std::option::Option<&Stage> {
                Self::STAGES.binary_search_by(|stage|{
                    let result = stage.ordinal_min().cmp(&value);
                    if result.is_gt() {
                        return result;
                    }

                    let result = stage.ordinal_max().cmp(&value);
                    if result.is_lt() {
                        return result;
                    }

                    ::std::cmp::Ordering::Equal
                })
                .map(|index| &Self::STAGES[index]).ok()
            }
        }

        impl ::std::fmt::Debug for $t {
            fn fmt(&self, f: &mut ::std::fmt::Formatter<'_>) -> ::std::fmt::Result {
                f.debug_struct(std::stringify!($t)).field("stages", &Self::STAGES).finish()
            }
        }
    };
}

encoding!(pub DefaultEncoding: [
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

/// A user defined encoding.
pub struct UserDefinedEncoding<S: AsRef<[Stage]>> {
    stages_lookup: [u8; 256],
    stages: S,
}

impl<S: AsRef<[Stage]>> UserDefinedEncoding<S> {
    /// Constructs a new user defined encoding with the given stages.
    pub fn new(stages: S) -> Self {
        assert!(stages.as_ref().len() <= i8::MAX as usize);
        let mut enc = UserDefinedEncoding {
            stages_lookup: [u8::MAX; 256],
            stages,
        };

        for (index, stage) in enc.stages.as_ref().iter().enumerate() {
            let prefix_offset = u8::BITS as u8 - stage.prefix_bits();
            let prefix = stage.prefix() << prefix_offset;
            let mut data = 0;
            while data < 1 << prefix_offset {
                enc.stages_lookup[(prefix | data) as usize] = index as u8;
                data += 1;
            }
        }

        enc
    }
}

impl<S: AsRef<[Stage]>> Encoding for UserDefinedEncoding<S> {
    fn stage_by_prefix(&self, prefix: u8) -> Option<&Stage> {
        let index = self.stages_lookup[prefix as usize] as usize;
        let stage = self.stages.as_ref().get(index);
        dbg!(prefix);
        dbg!(index);
        dbg!(self.stages.as_ref());

        stage
    }

    fn stage_by_value(&self, value: i64) -> Option<&Stage> {
        let stages = self.stages.as_ref();

        stages
            .binary_search_by(|stage| {
                let result = stage.ordinal_min().cmp(&value);
                if result.is_gt() {
                    return result;
                }

                let result = stage.ordinal_max().cmp(&value);
                if result.is_lt() {
                    return result;
                }

                ::std::cmp::Ordering::Equal
            })
            .map(|index| &stages[index])
            .ok()
    }
}

impl<S: AsRef<[Stage]>> PartialEq for UserDefinedEncoding<S> {
    fn eq(&self, other: &Self) -> bool {
        self.stages.as_ref().eq(other.stages.as_ref())
    }
}

impl<S: AsRef<[Stage]>> Eq for UserDefinedEncoding<S> {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn default_encoding() {
        assert_eq!(
            DefaultEncoding::STAGES.map(|s| (s.prefix(), s.ordinal_min(), s.ordinal_max())),
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

    #[test]
    fn user_defined_encoding() {
        let actual = UserDefinedEncoding::new(DefaultEncoding::STAGES);
        let expected = DefaultEncoding::default();
        for v in 0..u8::MAX {
            assert_eq!(actual.stage_by_prefix(v), expected.stage_by_prefix(v));
        }
    }
}
