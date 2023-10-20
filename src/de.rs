use serde::de::{self, SeqAccess, MapAccess};
use crate::fort_error::FError;
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

pub fn from_str_with_fields<'a, T>(s: &'a str, fmt: &'a FortFormat, fields: &'a[&'a str]) -> SResult<T> 
where T: de::Deserialize<'a>
{
    let mut deserializer = Deserializer::from_str_with_fields(s, fmt, fields);
    let t = T::deserialize(&mut deserializer)?;
    Ok(t)
}

pub struct Deserializer<'de> {
    input: &'de str,
    input_idx: usize,
    fmt: &'de FortFormat,
    fmt_idx: usize,
    field_idx: usize,
    fields: Option<&'de [&'de str]>,
}


impl<'de> Deserializer<'de> {
    pub fn from_str(input: &'de str, fmt: &'de FortFormat) -> Self {
        Self { input, input_idx: 0, fmt, fmt_idx: 0, field_idx: 0, fields: None }
    }

    pub fn from_str_with_fields(input: &'de str, fmt: &'de FortFormat, fields: &'de[&'de str]) -> Self {
        Self { input, input_idx: 0, fmt, fmt_idx: 0, field_idx: 0, fields: Some(fields) }
    }

    fn advance_over_skips(&mut self) {
        loop {
            // Consume any skips (i.e. 1x, 2x) in the format, also advancing
            // the internal string. This can be modified to handle other types
            // of Fortran positioning formats in the future.
            let peeked_fmt = self.fmt.fields.get(self.fmt_idx);
            match peeked_fmt {
                Some(&FortField::Skip) => {
                    self.fmt_idx += 1;
                    let _ = self.next_n_chars(1);
                }
                _ => return,
            }
        }
    }

    fn next_fmt(&mut self) -> SResult<&FortField> {
        self.advance_over_skips();
        loop {
            let next_fmt = self.fmt.fields.get(self.fmt_idx);
            match next_fmt {
                Some(field) => {
                    self.fmt_idx += 1;
                    self.field_idx += 1;
                    return Ok(field)
                },
                None => return Err(SError::FormatSpecTooShort)
            }
        }
    }

    fn next_field(&self) -> Option<&str> {
        if let Some(fields) = self.fields {
            fields.get(self.field_idx).map(|f| *f)
        } else {
            panic!("Called next_field on a deserializer without fields")
        }
    }

    #[allow(dead_code)] // keeping this function for now in case it is needed later
    fn peek_fmt(&mut self) -> Option<&FortField> {
        self.advance_over_skips();
        self.fmt.fields.get(self.fmt_idx)
    }

    fn rewind_fmt(&mut self) {
        if self.fmt_idx == 0 {
            return;
        }

        // None of the deserializers consume characters until the format has been matched,
        // so we only need to reset the format and field indices, not the character index.
        self.fmt_idx = self.fmt_idx.saturating_sub(1);
        self.field_idx = self.field_idx.saturating_sub(1);

    }

    fn next_n_chars(&mut self, n: u32) -> Result<&'de str, SError> {
        let n: usize = n.try_into().expect("Could not fit u32 into usize");
        let mut nbytes = 0;
        let mut i = 0;
        for c in self.input[self.input_idx..].chars() {
            i += 1;
            nbytes += c.len_utf8();
            if i == n { break; }
        }

        if i < n {
            return Err(SError::InputEndedEarly)
        }

        let s = &self.input[self.input_idx..self.input_idx+nbytes];
        self.input_idx += nbytes;
        Ok(s)
    }

    #[allow(dead_code)] // keeping this function for now in case it is needed later
    fn prev_n_chars(&mut self, n: u32) {
        let n: usize = n.try_into().expect("Could not fit u32 into usize");
        let mut nbytes = 0;
        let mut i = 0;
        for c in self.input[..self.input_idx].chars().rev() {
            i += 1;
            nbytes += c.len_utf8();
            if i == n { break; }
        }

        self.input_idx -= nbytes;
    }
}

impl<'de, 'a> de::Deserializer<'de> for &'a mut Deserializer<'de> {
    type Error = SError;

    fn deserialize_any<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de> {

        // Note: this was needed to deserialize a struct with an inner flattened struct
        match self.peek_fmt() {
            None => Err(SError::FormatSpecTooShort),
            Some(FortField::Char { width: _ }) => self.deserialize_str(visitor),
            Some(FortField::Integer { width: _, zeros: _, base: _ }) => self.deserialize_i64(visitor),
            Some(FortField::Logical { width: _ }) => self.deserialize_bool(visitor),
            Some(FortField::Real { width: _, precision: _, fmt: _, scale: _ }) => self.deserialize_f64(visitor),
            Some(FortField::Skip) => panic!("Got a skip format during peak")
        }
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
        self.deserialize_f64(visitor)
        .map_err(|e| e.with_serde_type("f32"))
    }

    fn deserialize_f64<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de> {
        let next_fmt = *self.next_fmt()?;
        if let FortField::Real { width, precision: _, fmt, scale: _ } = next_fmt {
            let substr = self.next_n_chars(width)?;
            let v = fast_float::parse(substr)
                .map_err(|e| FError::ParsingError { s: substr.to_string(), t: "real", reason: format!("Invalid real number format ({e})") })?;
            visitor.visit_f64(v)
        } else {
            Err(SError::FormatTypeMismatch { spec_type: next_fmt, serde_type: "f64" })
        }
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
        let next_fmt = *self.next_fmt()?;
        if let FortField::Char { width } = next_fmt {
            let s = self.next_n_chars(width.unwrap_or(1))?;
            visitor.visit_borrowed_str(s)
        } else {
            Err(SError::FormatTypeMismatch { spec_type: next_fmt, serde_type: "&str" })
        }
        
    }

    fn deserialize_string<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de> {
        self.deserialize_str(visitor)
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
        visitor.visit_seq(UnknownLenSeq::new(self, None))
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
        
        if self.fields.is_some() {
            // Note: this was needed when deserializing a struct with a flattened inner struct
            let map_accessor = FieldSequence::new(self);
            visitor.visit_map(map_accessor)
        } else {
            todo!()
        }
    }

    fn deserialize_struct<V>(
        self,
        _name: &'static str,
        fields: &'static [&'static str],
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de> {
        
        if self.fields.is_some() {
            let map_accessor = FieldSequence::new(self);
            visitor.visit_map(map_accessor)
        } else {
            // We'll assume that structures should read their fields in order from the input
            // and so deserialize them as known length sequences.
            visitor.visit_seq(KnownLenSeq::new(self, fields.len()))
        }
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
        
        // If this deserializer was provided with field names from e.g. a table header,
        // try to use those. Otherwise, assume that an identifer is given as the next
        // string in the format.
        if let Some(fields) = self.fields {
            let this_field = fields.get(self.field_idx)
                .map(|f| *f)
                .ok_or_else(|| SError::FieldListTooShort)?;
            visitor.visit_borrowed_str(this_field)
        } else {
            // Note: as of 2023-10-20, this else clause isn't supporting a specific data
            // layout, it is just to handle the no-fields case.
            self.deserialize_str(visitor)
        }
    }

    fn deserialize_ignored_any<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de> {
        // Note: this was called in the non-flattened inner struct test with fields.
        // That suggests there *might* be a way to know whether we should advance the
        // field and format indices.
        self.deserialize_any(visitor)
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


struct UnknownLenSeq<'a, 'de: 'a> {
    de: &'a mut Deserializer<'de>,
    n: usize,
    max_n: Option<usize>
}

impl<'a, 'de> UnknownLenSeq<'a, 'de> {
    fn new(de: &'a mut Deserializer<'de>, max_n: Option<usize>) -> Self {
        Self { de, n: 0, max_n }
    }
}

impl<'de, 'a> SeqAccess<'de> for UnknownLenSeq<'a, 'de> {
    type Error = SError;

    fn next_element_seed<T>(&mut self, seed: T) -> Result<Option<T::Value>, Self::Error>
    where
        T: de::DeserializeSeed<'de> {
        
        // First check if we've already deserialized the maximum number of allowed values
        // and stop if so
        if let Some(m) = self.max_n {
            if m == self.n {
                return Ok(None)
            }
        }

        // Otherwise we try to deserialize the next value in the sequence. Some errors tell us
        // to end the sequence, others are actual errors.
        match seed.deserialize(&mut *self.de) {
            Ok(el) => Ok(Some(el)),
            Err(SError::FormatTypeMismatch { spec_type: _, serde_type: _ }) => {
                self.de.rewind_fmt();
                Ok(None)
            }, // different type than desired, stop deserialization.
            Err(SError::FormatSpecTooShort) => Ok(None), // nothing more in the format spec list, stop deserialization
            Err(SError::InputEndedEarly) => Ok(None), // no more input, stop deserialization
            Err(e) => Err(e) // other errors are actually problems
        }
    }
}

struct FieldSequence<'a, 'de: 'a> {
    de: &'a mut Deserializer<'de>,
}

impl<'a, 'de> FieldSequence<'a, 'de> {
    fn new(de: &'a mut Deserializer<'de>) -> Self {
        Self { de }
    }
}

impl<'a, 'de> MapAccess<'de> for FieldSequence<'a, 'de> {
    type Error = SError;

    fn next_key_seed<K>(&mut self, seed: K) -> Result<Option<K::Value>, Self::Error>
    where
        K: de::DeserializeSeed<'de> {
        
        if self.de.next_field().is_none() {
            return Ok(None)
        }
        
        seed.deserialize(&mut *self.de).map(Some)
    }

    fn next_value_seed<V>(&mut self, seed: V) -> Result<V::Value, Self::Error>
    where
        V: de::DeserializeSeed<'de> {
        seed.deserialize(&mut *self.de)
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
    fn test_de_float() -> SResult<()> {
        let ff = FortFormat::parse("(f8)")?;
        let r: f64 = from_str("12.45678", &ff)?;
        assert_eq!(r, 12.45678);

        let r: f64 = from_str("-23.5678", &ff)?;
        assert_eq!(r, -23.5678);

        // TODO: Need to test fortran E and D numbers, plus scaled numbers
        // Double check how fortran outputs these
        let ff = FortFormat::parse("(e8)")?;
        let r: f64 = from_str("1.34E+03", &ff)?;
        assert_eq!(r, 1.34e3);

        let r: f64 = from_str("1.34e+03", &ff)?;
        assert_eq!(r, 1.34e3);

        let r: f64 = from_str("1.34E-03", &ff)?;
        assert_eq!(r, 1.34e-3);

        let r: f64 = from_str("1.34e-03", &ff)?;
        assert_eq!(r, 1.34e-3);

        let ff = FortFormat::parse("(d8)")?;
        let r: f64 = from_str("1.34D+03", &ff)?;
        assert_eq!(r, 1.34e3);

        let r: f64 = from_str("1.34d+03", &ff)?;
        assert_eq!(r, 1.34e3);

        let r: f64 = from_str("1.34D-03", &ff)?;
        assert_eq!(r, 1.34e-3);

        let r: f64 = from_str("1.34d-03", &ff)?;
        assert_eq!(r, 1.34e-3);

        Ok(())
    }

    #[test]
    fn test_de_string() -> SResult<()> {
        let ff = FortFormat::parse("(a16)")?;
        let s: String = from_str("Hello world!    ", &ff)?;
        assert_eq!(s, "Hello world!    ");
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
    fn test_de_vec() -> SResult<()> {
        let ff = FortFormat::parse("5(i3,1x)")?;
        let v: Vec<i32> = from_str("123 456 789 246 369", &ff)?;
        assert_eq!(&v, &[123, 456, 789, 246, 369]);
        Ok(())
    }

    #[test]
    fn test_de_vec_in_tuple() -> SResult<()> {
        let ff = FortFormat::parse("(a5,1x,3i3,a5)")?;
        let t: (String, Vec<i32>, String) = from_str("Hello 12 34 56 World", &ff)?;
        assert_eq!(t, ("Hello".to_owned(), vec![12, 34, 56], "World".to_owned()));
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

    #[test]
    fn test_de_struct_with_fields() -> SResult<()> {
        #[derive(Debug, PartialEq, Deserialize)]
        struct Test {
            alpha: i32,
            beta: f64,
            gamma: String,
        }

        let ff = FortFormat::parse("(a8,1x,i4,1x,f5.3)")?;
        let fields = ["gamma", "alpha", "beta"];
        let s: Test = from_str_with_fields(
            "abcdefgh 1234 9.876", 
            &ff, 
            &fields
        )?;

        assert_eq!(s, Test{ alpha: 1234, beta: 9.876, gamma: "abcdefgh".to_string() });

        Ok(())
    }

    #[test]
    fn test_de_struct_with_inner_struct() -> SResult<()> {
        #[derive(Debug, PartialEq, Deserialize)]
        struct Inner {
            x: i32,
            y: i32,
        }

        #[derive(Debug, PartialEq, Deserialize)]
        struct Outer {
            sid: String,
            #[serde(flatten)]
            coords: Inner,
            flag: i8,
        }

        let ff = FortFormat::parse("(a2,1x,i1,1x,i3,1x,i3)")?;
        let fields = ["sid", "flag", "y", "x"];
        let s: Outer = from_str_with_fields(
            "pa 0 456 123",
            &ff,
            &fields
        )?;

        assert_eq!(s, Outer{ sid: "pa".to_string(), flag: 0, coords: Inner { x: 123, y: 456 } });

        Ok(())
    }

    #[test]
    fn test_de_inner_struct_not_flattened() -> SResult<()> {
        #[derive(Debug, PartialEq, Deserialize)]
        struct Inner {
            x: i32,
            y: i32,
        }

        #[derive(Debug, PartialEq, Deserialize)]
        struct Outer {
            sid: String,
            coords: Inner,
            flag: i8,
        }

        let ff = FortFormat::parse("(a2,1x,i1,1x,i3,1x,i3)")?;
        let fields = ["sid", "flag", "y", "x"];
        let s: SResult<Outer> = from_str_with_fields(
            "pa 0 456 123",
            &ff,
            &fields
        );

        // Note: I wrote this to test for an error because as or 2023-10-20 I'm assuming that
        // serde will try to deserialize something for the "coords" field itself, and there's
        // no way to tell the Fortran deserializer that it shouldn't advance the format & field
        // indices in that case (without using the #[serder(flatten)] tag). But this deserialization
        // calls `deserialize_ignored_any` (unclear for which field), so there may be a mechanism
        // to handle this test case correctly.
        //
        // On the other hand, using #[serde(flatten)] is clearer that the fields of an inner struct
        // should be deserialized as if they are directly in the outer struct.
        assert!(s.is_err());

        Ok(())
    }
}
