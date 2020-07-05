use core::fmt;
use core::marker::PhantomData;

use serde_::de::{Deserialize, Deserializer, SeqAccess, Visitor};
use serde_::ser::{Serialize, Serializer};

use crate::Vc;

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

#[inline]
fn cautious_size_hint(hint: Option<usize>) -> usize {
    core::cmp::min(hint.unwrap_or(0), 4096)
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
                let mut values = Vc::with_capacity(cautious_size_hint(seq.size_hint()));
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
