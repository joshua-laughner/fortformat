use std::{fmt::{Octal, UpperHex}, io::Write, string::FromUtf8Error};

use serde::ser;
use crate::{de::FortFormat, format_specs::{FortField, IntBase}, serde_error::{SError, SResult}};

pub fn to_string<T>(value: T, fmt: &FortFormat) -> SResult<String> 
where T: ser::Serialize
{
    let mut serializer = Serializer::new(fmt);
    value.serialize(&mut serializer)?;
    Ok(serializer.into_string()?)
}

/// Serializer for Fortran-format writers
pub struct Serializer<'f, W: Write> {
    buf: W,
    fmt: &'f FortFormat,
    fmt_idx: usize,
    fields: Option<&'f[ &'f str]>,
    field_idx: usize,
}

impl <'f> Serializer<'f, Vec<u8>> {
    pub fn new(fmt: &'f FortFormat) -> Self {
        Self { buf: vec![], fmt, fmt_idx: 0, fields: None, field_idx: 0 }
    }

    pub fn new_with_fields(fmt: &'f FortFormat, fields: &'f[&'f str]) -> Self {
        Self { buf: vec![], fmt, fmt_idx: 0, fields: Some(fields), field_idx: 0 }
    }

    pub fn into_string(self) -> Result<String, FromUtf8Error> {
        String::from_utf8(self.buf)
    }
}

impl <'f, W: Write> Serializer<'f, W> {
    pub fn new_writer(fmt: &'f FortFormat, writer: W) -> Self {
        Self { buf: writer, fmt, fmt_idx: 0, fields: None, field_idx: 0 }
    }

    pub fn new_writer_with_fields(fmt: &'f FortFormat, fields: &'f[&'f str], writer: W) -> Self {
        Self { buf: writer, fmt, fmt_idx: 0, fields: Some(fields), field_idx: 0 }
    }
}

impl<'f, W: Write> Serializer<'f, W> {
    // This shares a lot of code with the Deserializer. I tried refactoring that out
    // into an inner struct, but that ended up being more awkward because the inner
    // struct didn't know about the Deserializer's input string. Another option
    // might be a trait that requires defining advance_over_skips and methods
    // to increment indices and get formats/field names - will explore later.

    fn advance_over_skips(&mut self) {
        loop {
            // Consume any skips (i.e. 1x, 2x) in the format, also advancing
            // the internal string. This can be modified to handle other types
            // of Fortran positioning formats in the future.
            let peeked_fmt = self.fmt.fields.get(self.fmt_idx);
            match peeked_fmt {
                Some(&FortField::Skip) => {
                    self.fmt_idx += 1;
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

    fn curr_field(&mut self) -> Option<&str> {
        if let Some(fields) = self.fields {
            fields.get(self.field_idx).map(|f| *f)
        } else {
            panic!("Called next_field on a deserializer without fields")
        }
    }

    fn try_prev_field(&self) -> Option<&str> {
        if self.field_idx == 0 {
            return None;
        }

        self.fields.map(|f| f.get(self.field_idx - 1))
            .flatten()
            .map(|f| *f)
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

    fn serialize_integer<I: itoa::Integer + Octal + UpperHex>(&mut self, abs_value: I, is_neg: bool) -> SResult<()> {
        let next_fmt = *self.next_fmt()?;
        if let FortField::Integer { width, zeros, base } = next_fmt {
            // wish that this didn't require allocating a vector, but I think this is the cleanest way
            // to handle this, since we need to know the length of the serialized number before we
            // can write.
            let (s, is_dec): (Vec<u8>, bool) = match base {
                IntBase::Decimal => {
                    let mut b = itoa::Buffer::new();
                    (b.format(abs_value).as_bytes().into_iter().copied().collect(), true)
                },
                IntBase::Octal => {
                    (format!("{abs_value:o}").as_bytes().into_iter().copied().collect(), false)
                },
                IntBase::Hexadecimal => {
                    (format!("{abs_value:X}").as_bytes().into_iter().copied().collect(), false)
                },
            };
            

            let nsign = if is_neg { 1 } else { 0 };
            let nzeros = zeros.map(|n| n.saturating_sub(s.len() as u32)).unwrap_or(0);
            let nchar = nzeros + nsign + s.len() as u32;
            
            let bad_output = nchar > width || (is_neg && !is_dec);
            if bad_output {
                for _ in 0..width {
                    write!(&mut self.buf, "*")?;
                }
            } else {
                let nspace = width - nchar;
                for _ in 0..nspace {
                    write!(&mut self.buf, " ")?;
                }
                if is_neg {
                    write!(&mut self.buf, "-")?;
                }
                for _ in 0..nzeros {
                    write!(&mut self.buf, "0")?;
                }
                self.buf.write(&s)?;
            }
            
            Ok(())
        } else {
            Err(SError::FormatTypeMismatch { spec_type: next_fmt, serde_type: "integer", field_name: self.try_prev_field().map(|f| f.to_string()) })
        }
    }
}


impl<'a, 'f, W: Write> ser::Serializer for &'a mut Serializer<'f, W> {
    type Ok = ();
    type Error = SError;

    // we already store the format information on this struct so we should
    // be able to just use it for all the sequence serialization.
    type SerializeSeq = Self;
    type SerializeTuple = Self;
    type SerializeTupleStruct = Self;
    type SerializeTupleVariant = Self;
    type SerializeMap = Self;
    type SerializeStruct = Self;
    type SerializeStructVariant = Self;

    fn serialize_bool(self, v: bool) -> Result<Self::Ok, Self::Error> {
        let next_fmt = *self.next_fmt()?;
        if let FortField::Logical { width } = next_fmt {
            let b = if v { b"T" } else { b"F" };
            for _ in 0..width-1 {
                write!(&mut self.buf, " ")?;
            }
            self.buf.write(b)?;
            Ok(())
        } else {
            Err(SError::FormatTypeMismatch { spec_type: next_fmt, serde_type: "bool", field_name: self.try_prev_field().map(|f| f.to_string()) })
        }
    }

    fn serialize_i8(self, v: i8) -> Result<Self::Ok, Self::Error> {
        self.serialize_integer(v.abs(), v < 0)
    }

    fn serialize_i16(self, v: i16) -> Result<Self::Ok, Self::Error> {
        self.serialize_integer(v.abs(), v < 0)
    }

    fn serialize_i32(self, v: i32) -> Result<Self::Ok, Self::Error> {
        self.serialize_integer(v.abs(), v < 0)
    }

    fn serialize_i64(self, v: i64) -> Result<Self::Ok, Self::Error> {
        self.serialize_integer(v.abs(), v < 0)
    }

    fn serialize_i128(self, v: i128) -> Result<Self::Ok, Self::Error> {
        self.serialize_integer(v.abs(), v < 0)
    }

    fn serialize_u8(self, v: u8) -> Result<Self::Ok, Self::Error> {
        self.serialize_integer(v, false)
    }

    fn serialize_u16(self, v: u16) -> Result<Self::Ok, Self::Error> {
        self.serialize_integer(v, false)
    }

    fn serialize_u32(self, v: u32) -> Result<Self::Ok, Self::Error> {
        self.serialize_integer(v, false)
    }

    fn serialize_u64(self, v: u64) -> Result<Self::Ok, Self::Error> {
        self.serialize_integer(v, false)
    }

    fn serialize_u128(self, v: u128) -> Result<Self::Ok, Self::Error> {
        self.serialize_integer(v, false)
    }

    fn serialize_f32(self, v: f32) -> Result<Self::Ok, Self::Error> {
        todo!()
    }

    fn serialize_f64(self, v: f64) -> Result<Self::Ok, Self::Error> {
        todo!()
    }

    fn serialize_char(self, v: char) -> Result<Self::Ok, Self::Error> {
        todo!()
    }

    fn serialize_str(self, v: &str) -> Result<Self::Ok, Self::Error> {
        todo!()
    }

    fn serialize_bytes(self, v: &[u8]) -> Result<Self::Ok, Self::Error> {
        todo!()
    }

    fn serialize_none(self) -> Result<Self::Ok, Self::Error> {
        todo!()
    }

    fn serialize_some<T: ?Sized>(self, value: &T) -> Result<Self::Ok, Self::Error>
    where
        T: serde::Serialize {
        todo!()
    }

    fn serialize_unit(self) -> Result<Self::Ok, Self::Error> {
        todo!()
    }

    fn serialize_unit_struct(self, name: &'static str) -> Result<Self::Ok, Self::Error> {
        todo!()
    }

    fn serialize_unit_variant(
        self,
        name: &'static str,
        variant_index: u32,
        variant: &'static str,
    ) -> Result<Self::Ok, Self::Error> {
        todo!()
    }

    fn serialize_newtype_struct<T: ?Sized>(
        self,
        name: &'static str,
        value: &T,
    ) -> Result<Self::Ok, Self::Error>
    where
        T: serde::Serialize {
        todo!()
    }

    fn serialize_newtype_variant<T: ?Sized>(
        self,
        name: &'static str,
        variant_index: u32,
        variant: &'static str,
        value: &T,
    ) -> Result<Self::Ok, Self::Error>
    where
        T: serde::Serialize {
        todo!()
    }

    fn serialize_seq(self, len: Option<usize>) -> Result<Self::SerializeSeq, Self::Error> {
        todo!()
    }

    fn serialize_tuple(self, len: usize) -> Result<Self::SerializeTuple, Self::Error> {
        todo!()
    }

    fn serialize_tuple_struct(
        self,
        name: &'static str,
        len: usize,
    ) -> Result<Self::SerializeTupleStruct, Self::Error> {
        todo!()
    }

    fn serialize_tuple_variant(
        self,
        name: &'static str,
        variant_index: u32,
        variant: &'static str,
        len: usize,
    ) -> Result<Self::SerializeTupleVariant, Self::Error> {
        todo!()
    }

    fn serialize_map(self, len: Option<usize>) -> Result<Self::SerializeMap, Self::Error> {
        todo!()
    }

    fn serialize_struct(
        self,
        name: &'static str,
        len: usize,
    ) -> Result<Self::SerializeStruct, Self::Error> {
        todo!()
    }

    fn serialize_struct_variant(
        self,
        name: &'static str,
        variant_index: u32,
        variant: &'static str,
        len: usize,
    ) -> Result<Self::SerializeStructVariant, Self::Error> {
        todo!()
    }
}

impl<'a, 'f, W: Write> ser::SerializeSeq for &'a mut Serializer<'f, W> {
    type Ok = ();

    type Error = SError;

    fn serialize_element<T: ?Sized>(&mut self, value: &T) -> Result<(), Self::Error>
    where
        T: serde::Serialize {
        todo!()
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        todo!()
    }
}

impl <'a, 'f, W: Write> ser::SerializeTuple for &'a mut Serializer<'f, W> {
    type Ok = ();

    type Error = SError;

    fn serialize_element<T: ?Sized>(&mut self, value: &T) -> Result<(), Self::Error>
    where
        T: serde::Serialize {
        todo!()
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        todo!()
    }
}

impl <'a, 'f, W: Write> ser::SerializeTupleStruct for &'a mut Serializer<'f, W> {
    type Ok = ();

    type Error = SError;

    fn serialize_field<T: ?Sized>(&mut self, value: &T) -> Result<(), Self::Error>
    where
        T: serde::Serialize {
        todo!()
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        todo!()
    }
}

impl<'a, 'f, W: Write> ser::SerializeTupleVariant for &'a mut Serializer<'f, W> {
    type Ok = ();

    type Error = SError;

    fn serialize_field<T: ?Sized>(&mut self, value: &T) -> Result<(), Self::Error>
    where
        T: serde::Serialize {
        todo!()
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        todo!()
    }
}

impl<'a, 'f, W: Write> ser::SerializeMap for &'a mut Serializer<'f, W> {
    type Ok = ();

    type Error = SError;

    fn serialize_key<T: ?Sized>(&mut self, key: &T) -> Result<(), Self::Error>
    where
        T: serde::Serialize {
        todo!()
    }

    fn serialize_value<T: ?Sized>(&mut self, value: &T) -> Result<(), Self::Error>
    where
        T: serde::Serialize {
        todo!()
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        todo!()
    }
}

impl<'a, 'f, W: Write> ser::SerializeStruct for &'a mut Serializer<'f, W> {
    type Ok = ();

    type Error = SError;

    fn serialize_field<T: ?Sized>(
        &mut self,
        key: &'static str,
        value: &T,
    ) -> Result<(), Self::Error>
    where
        T: serde::Serialize {
        todo!()
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        todo!()
    }
}

impl<'a, 'f, W: Write> ser::SerializeStructVariant for &'a mut Serializer<'f, W> {
    type Ok = ();

    type Error = SError;

    fn serialize_field<T: ?Sized>(
        &mut self,
        key: &'static str,
        value: &T,
    ) -> Result<(), Self::Error>
    where
        T: serde::Serialize {
        todo!()
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        todo!()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ser_bool() {
        let fmt = FortFormat::parse("(l1)").unwrap();
        let s = to_string(true, &fmt).unwrap();
        assert_eq!(s, "T");
        let s = to_string(false, &fmt).unwrap();
        assert_eq!(s, "F");

        let fmt = FortFormat::parse("(l3)").unwrap();
        let s = to_string(true, &fmt).unwrap();
        assert_eq!(s, "  T");
        let s = to_string(false, &fmt).unwrap();
        assert_eq!(s, "  F");
    }

    #[test]
    fn test_ser_dec_int() {
        let fmt = FortFormat::parse("(i4)").unwrap();
        let s = to_string(42, &fmt).unwrap();
        assert_eq!(s, "  42");
        let s = to_string(-42, &fmt).unwrap();
        assert_eq!(s, " -42");
        let s = to_string(12345, &fmt).unwrap();
        assert_eq!(s, "****");

        let fmt = FortFormat::parse("(i4.3)").unwrap();
        let s = to_string(42, &fmt).unwrap();
        assert_eq!(s, " 042");
        let s = to_string(-42, &fmt).unwrap();
        assert_eq!(s, "-042");
        let s = to_string(123, &fmt).unwrap();
        assert_eq!(s, " 123");
        let s = to_string(-123, &fmt).unwrap();
        assert_eq!(s, "-123");

        let fmt = FortFormat::parse("(i3.3)").unwrap();
        let s = to_string(42, &fmt).unwrap();
        assert_eq!(s, "042");
        let s = to_string(-42, &fmt).unwrap();
        assert_eq!(s, "***");
    }

    #[test]
    fn test_octal_int() {
        let fmt = FortFormat::parse("(o5)").unwrap();
        let s = to_string(42, &fmt).unwrap();
        assert_eq!(s, "   52");
        let s = to_string(-42, &fmt).unwrap();
        assert_eq!(s, "*****");

        let fmt = FortFormat::parse("(o5.3)").unwrap();
        let s = to_string(42, &fmt).unwrap();
        assert_eq!(s, "  052");
        let s = to_string(-42, &fmt).unwrap();
        assert_eq!(s, "*****");
    }

    #[test]
    fn test_hex_int() {
        let fmt = FortFormat::parse("(z5)").unwrap();
        let s = to_string(42, &fmt).unwrap();
        assert_eq!(s, "   2A");
        let s = to_string(-42, &fmt).unwrap();
        assert_eq!(s, "*****");

        let fmt = FortFormat::parse("(z5.3)").unwrap();
        let s = to_string(42, &fmt).unwrap();
        assert_eq!(s, "  02A");
        let s = to_string(-42, &fmt).unwrap();
        assert_eq!(s, "*****");
    }
}