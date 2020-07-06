use core::fmt;
use core::marker::PhantomData;

use serde_::de::{Deserialize, Deserializer, SeqAccess, Visitor};
use serde_::ser::{Serialize, Serializer};

use crate::Vc;

/// Helpers picked from the serde repository https://github.com/serde-rs/serde.
mod helper {

    use serde_::de::{Deserialize, DeserializeSeed, Deserializer};

    /// https://github.com/serde-rs/serde/blob/9f331cc25753edd71ad7ab0ea08a430fefaa90e1/serde/src/private/de.rs#L203
    #[inline]
    pub(super) fn cautious_size_hint(hint: Option<usize>) -> usize {
        core::cmp::min(hint.unwrap_or(0), 4096)
    }

    /// https://github.com/serde-rs/serde/blob/24e6acbfaeb18af978012b904209632f012eb54d/serde/src/private/de.rs#L2634-L2650
    pub(super) struct InPlaceSeed<'a, T>(pub &'a mut T);

    impl<'a, 'de, T> DeserializeSeed<'de> for InPlaceSeed<'a, T>
    where
        T: Deserialize<'de>,
    {
        type Value = ();
        fn deserialize<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
        where
            D: Deserializer<'de>,
        {
            T::deserialize_in_place(deserializer, self.0)
        }
    }
}

impl<T> Serialize for Vc<T>
where
    T: Serialize,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.collect_seq(self)
    }
}

impl<'de, T> Deserialize<'de> for Vc<T>
where
    T: Deserialize<'de>,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct VcVisitor<T> {
            marker: PhantomData<T>,
        }
        impl<'de, T> Visitor<'de> for VcVisitor<T>
        where
            T: Deserialize<'de>,
        {
            type Value = Vc<T>;
            fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
                formatter.write_str("a sequence")
            }
            fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
            where
                A: SeqAccess<'de>,
            {
                let mut values = Vc::with_capacity(helper::cautious_size_hint(seq.size_hint()));
                while let Some(value) = seq.next_element()? {
                    values.push(value);
                }
                Ok(values)
            }
        }
        let visitor = VcVisitor {
            marker: PhantomData,
        };
        deserializer.deserialize_seq(visitor)
    }
}

#[cfg(test)]
#[cfg(not(tarpaulin_include))] // don't count for coverage
mod tests {
    use crate::Vc;
    use serde_test::{assert_tokens, Token};

    #[test]
    fn test_serde_empty_vc() {
        let my_vec: Vc<u32> = Vc::default();
        assert_tokens(&my_vec, &[Token::Seq { len: Some(0) }, Token::SeqEnd])
    }

    #[test]
    fn test_serde_non_empty() {
        let mut my_vec: Vc<u32> = Vc::default();
        my_vec.push(1);
        my_vec.push(2);
        my_vec.push(3);
        assert_tokens(
            &my_vec,
            &[
                Token::Seq { len: Some(3) },
                Token::U32(1),
                Token::U32(2),
                Token::U32(3),
                Token::SeqEnd,
            ],
        )
    }

    #[test]
    fn test_serde_while_atoning() {
        let mut my_vec: Vc<u32> = Vc::new();
        for i in 1..=8 {
            my_vec.push(i);
        }
        assert!(my_vec.is_atoning());
        assert_tokens(
            &my_vec,
            &[
                Token::Seq { len: Some(8) },
                Token::U32(1),
                Token::U32(2),
                Token::U32(3),
                Token::U32(4),
                Token::U32(5),
                Token::U32(6),
                Token::U32(7),
                Token::U32(8),
                Token::SeqEnd,
            ],
        );
    }
}
