//! Types and traits used for encoding.

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

pub(crate) struct BorrowedEncoding<'e, E: Encoding>(pub &'e E);

impl<'e, E: Encoding> Encoding for BorrowedEncoding<'e, E> {
    fn stage_by_prefix(&self, prefix: u8) -> Option<&Stage> {
        self.0.stage_by_prefix(prefix)
    }

    fn stage_by_value(&self, value: i64) -> Option<&Stage> {
        self.0.stage_by_value(value)
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
        #[derive(Copy, Clone, Default, Debug)]
        $v struct $t;

        impl $t {
            const STAGES: [$crate::enc::Stage; count!($($prefix,)*)] = {
                let mut stages = [
                    $($crate::enc::Stage::new($prefix_len, $prefix, $value_len, 0)),+
                ];

                let origin = stages.len() / 2;

                let mut index = origin;
                while index > 0  {
                    index -= 1;
                    stages[index] = $crate::enc::Stage::new(
                        stages[index].prefix_len(),
                        stages[index].prefix(),
                        stages[index].value_len(),
                        stages[index + 1].value_low() - stages[index].value_high() - 1);
                }

                let mut index = origin;
                while index + 1 < stages.len() {
                    index += 1;
                    stages[index] = $crate::enc::Stage::new(
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

        impl $crate::enc::Encoding for $t {
            fn stage_by_prefix(&self, prefix: u8) -> Option<&$crate::enc::Stage> {
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

                    ::std::cmp::Ordering::Equal
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
