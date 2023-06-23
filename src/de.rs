use serde::de::{self, SeqAccess};
use crate::serde_error::{SResult, SError};
use crate::format_specs::{FortFormat, FortField};
use crate::parsing;


pub fn from_str<'a, T>(s: &'a str, fmt: &'a FortFormat) -> SResult<T> 
where T: de::Deserialize<'a>
{
    let mut deserializer = Deserializer::from_str(s, fmt);
    let t = T::deserialize(&mut deserializer)?;
    Ok(t)
}

pub struct Deserializer<'de> {
    input: &'de str,
    fmt: std::slice::Iter<'de, FortField>,
}


impl<'de> Deserializer<'de> {
    pub fn from_str(input: &'de str, fmt: &'de FortFormat) -> Self {
        Self { input, fmt: fmt.fields.iter() }
    }

    fn next_fmt(&mut self) -> SResult<&FortField> {
        loop {
            let next_fmt = self.fmt.next();
            match next_fmt {
                Some(&FortField::Skip) => {
                    self.next_n_chars(1)?;
                    continue
                },
                Some(field) => return Ok(field),
                None => return Err(SError::FormatSpecTooShort)
            }
        }
    }

    fn next_n_chars(&mut self, n: u32) -> Result<&'de str, SError> {
        let n: usize = n.try_into().expect("Could not fit u32 into usize");
        let mut nbytes = 0;
        let mut i = 0;
        for c in self.input.chars() {
            i += 1;
            nbytes += c.len_utf8();
            if i == n { break; }
        }

        if i < n {
            return Err(SError::InputEndedEarly)
        }

        let s = &self.input[..nbytes];
        self.input = &self.input[nbytes..];
        Ok(s)
    }
}

impl<'de, 'a> de::Deserializer<'de> for &'a mut Deserializer<'de> {
    type Error = SError;

    fn deserialize_any<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de> {
        todo!()
    }

    fn deserialize_bool<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de> {
        let next_fmt = *self.next_fmt()?;
        if let FortField::Logical { width } = next_fmt {
            let substr = self.next_n_chars(width)?;
            let b = parsing::parse_logical(substr)?;
            visitor.visit_bool(b)
        } else {
            Err(SError::FormatTypeMismatch { spec_type: next_fmt, serde_type: "bool" })
        }
    }

    fn deserialize_i8<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de> {
        self.deserialize_i64(visitor)
        .map_err(|e| e.with_serde_type("i8"))
    }

    fn deserialize_i16<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de> {
            self.deserialize_i64(visitor)
            .map_err(|e| e.with_serde_type("i16"))
    }

    fn deserialize_i32<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de> {
        self.deserialize_i64(visitor)
        .map_err(|e| e.with_serde_type("i32"))
    }

    fn deserialize_i64<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de> {
        let next_fmt = *self.next_fmt()?;
        if let FortField::Integer { width, zeros: _, base } = next_fmt {
            let substr = self.next_n_chars(width)?;
            let v = match base {
                crate::format_specs::IntBase::Decimal => parsing::parse_integer(substr)?,
                crate::format_specs::IntBase::Octal => todo!(),
                crate::format_specs::IntBase::Hexadecimal => todo!(),
            };
            visitor.visit_i64(v)
        } else {
            Err(SError::FormatTypeMismatch { spec_type: next_fmt, serde_type: "i64" })
        }
    }

    fn deserialize_u8<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de> {
            self.deserialize_u64(visitor)
            .map_err(|e| e.with_serde_type("u8"))
    }

    fn deserialize_u16<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de> {
        self.deserialize_u64(visitor)
        .map_err(|e| e.with_serde_type("u16"))
    }

    fn deserialize_u32<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de> {
        self.deserialize_u64(visitor)
        .map_err(|e| e.with_serde_type("u32"))
    }

    fn deserialize_u64<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de> {
            let next_fmt = *self.next_fmt()?;
            if let FortField::Integer { width, zeros: _, base } = next_fmt {
                let substr = self.next_n_chars(width)?;
                let v = match base {
                    crate::format_specs::IntBase::Decimal => parsing::parse_unsigned_integer(substr)?,
                    crate::format_specs::IntBase::Octal => todo!(),
                    crate::format_specs::IntBase::Hexadecimal => todo!(),
                };
                visitor.visit_u64(v)
            } else {
                Err(SError::FormatTypeMismatch { spec_type: next_fmt, serde_type: "u64" })
            }
    }

    fn deserialize_f32<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de> {
        todo!()
    }

    fn deserialize_f64<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de> {
        todo!()
    }

    fn deserialize_char<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de> {
        let next_fmt = *self.next_fmt()?;
        match next_fmt {
            FortField::Char { width: None } | FortField::Char { width: Some(1) } => {
                let c = self.next_n_chars(1)?
                    .chars()
                    .next()
                    .unwrap();  // Ok to unwrap, next_n_chars returns an error if not enough characters available.
                visitor.visit_char(c)
            },
            FortField::Char { width: _ } => {
                Err(SError::FormatTypeMismatch { spec_type: next_fmt, serde_type: "char (requires 'a' or 'a1' Fortran format)" })
            },
            _ => {
                Err(SError::FormatTypeMismatch { spec_type: next_fmt, serde_type: "char" })
            }
        }
    }

    fn deserialize_str<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de> {
        todo!()
    }

    fn deserialize_string<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de> {
        todo!()
    }

    fn deserialize_bytes<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de> {
        todo!()
    }

    fn deserialize_byte_buf<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de> {
        todo!()
    }

    fn deserialize_option<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de> {
        todo!()
    }

    fn deserialize_unit<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de> {
        todo!()
    }

    fn deserialize_unit_struct<V>(
        self,
        name: &'static str,
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de> {
        todo!()
    }

    fn deserialize_newtype_struct<V>(
        self,
        name: &'static str,
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de> {
        todo!()
    }

    fn deserialize_seq<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de> {
        todo!()
    }

    fn deserialize_tuple<V>(self, len: usize, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de> {
        visitor.visit_seq(KnownLenSeq::new(self, len))
    }

    fn deserialize_tuple_struct<V>(
        self,
        name: &'static str,
        len: usize,
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de> {
        todo!()
    }

    fn deserialize_map<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de> {
        todo!()
    }

    fn deserialize_struct<V>(
        self,
        _name: &'static str,
        fields: &'static [&'static str],
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de> {
        
        // We'll assume that structures should read their fields in order from the input
        // and so deserialize them as known length sequences.
        visitor.visit_seq(KnownLenSeq::new(self, fields.len()))
    }

    fn deserialize_enum<V>(
        self,
        name: &'static str,
        variants: &'static [&'static str],
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de> {
        todo!()
    }

    fn deserialize_identifier<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de> {
        todo!()
    }

    fn deserialize_ignored_any<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de> {
        todo!()
    }
}


struct KnownLenSeq<'a, 'de: 'a> {
    de: &'a mut Deserializer<'de>,
    n: usize,
    i: usize,
}

impl<'a, 'de> KnownLenSeq<'a, 'de> {
    fn new(de: &'a mut Deserializer<'de>, n: usize) -> Self {
        Self { de, n, i: 0 }
    }
}

impl<'de, 'a> SeqAccess<'de> for KnownLenSeq<'a, 'de> {
    type Error = SError;

    fn next_element_seed<T>(&mut self, seed: T) -> Result<Option<T::Value>, Self::Error>
    where
        T: de::DeserializeSeed<'de> {
        
        if self.i == self.n {
            // Check if we've already deserialized all the elements we are supposed to
            // and stop if so.
            Ok(None)
        } else {
            // Otherwise we can just deserialize whatever the next element is
            self.i += 1;
            seed.deserialize(&mut *self.de).map(Some)
        }
    }
}

#[cfg(test)]
mod tests {
    use serde::Deserialize;

    use super::*;

    #[test]
    fn test_de_bool() -> SResult<()> {
        let ff = FortFormat::parse("(l1)")?;
        let b: bool = from_str("T", &ff)?;
        assert_eq!(b, true);
        Ok(())
    }

    #[test]
    fn test_de_integer() -> SResult<()> {
        let ff = FortFormat::parse("(i2)")?;
        let i: i8 = from_str(" 8", &ff)?;
        assert_eq!(i, 8);

        let i: i8 = from_str("-1", &ff)?;
        assert_eq!(i, -1);

        // this confirms that we only parse two characters - including the sign
        let i: i8 = from_str("-22", &ff)?;
        assert_eq!(i, -2);

        let i: i64 = from_str("42", &ff)?;
        assert_eq!(i, 42);

        let i: i64 = from_str("-7", &ff)?;
        assert_eq!(i, -7);

        let u: u8 = from_str(" 3", &ff)?;
        assert_eq!(u, 3);

        let u: u64 = from_str("26", &ff)?;
        assert_eq!(u, 26);

        // this confirms that we only parse two characters
        let u: u8 = from_str("200", &ff)?;
        assert_eq!(u, 20);

        Ok(())
    }

    #[test]
    fn test_de_tuple() -> SResult<()> {
        let ff = FortFormat::parse("(a1,1x,i2,1x,i4)")?;
        let t: (char, i32, i32) = from_str("a 16 9876", &ff)?;
        assert_eq!(t, ('a', 16, 9876));
        Ok(())
    }

    #[test]
    fn test_de_struct() -> SResult<()> {
        #[derive(Debug, PartialEq, Eq, Deserialize)]
        struct Test {
            x: i32,
            y: i32,
            c: char,
            b: bool
        }

        let ff = FortFormat::parse("(2i3,1x,a,1x,l1)")?;
        let s: Test = from_str(" 10 20 z F", &ff)?;
        assert_eq!(s, Test { x: 10, y: 20, c: 'z', b: false });

        Ok(())
    }

    #[test]
    fn test_de_struct_with_array() -> SResult<()> {
        #[derive(Debug, PartialEq, Eq, Deserialize)]
        struct Test {
            flag: bool,
            data: [i32; 8]
        }

        let ff = FortFormat::parse("(l1,1x,8i3)")?;
        let s: Test = from_str("T  10 20 30 40 50 60 70 80", &ff)?;
        assert_eq!(s, Test{ flag: true, data: [10, 20, 30, 40, 50, 60, 70, 80] });

        Ok(())
    }
}
