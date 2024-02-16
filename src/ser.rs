use std::{fmt::{Octal, UpperHex}, io::{Bytes, Write}, string::FromUtf8Error};

use ryu_floating_decimal::d2d;
use serde::ser;
use crate::{de::FortFormat, format_specs::{FortField, IntBase, RealFmt}, serde_error::{SError, SResult}};

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

    fn serialize_real(&mut self, v: f64) -> SResult<()> {
        let next_fmt = *self.next_fmt()?;
        if let FortField::Real { width, precision, fmt, scale } = next_fmt {
            let precision = precision.ok_or_else(|| SError::InvalidOutputFmt(
                next_fmt, "real number formats must include a precision for output".to_string()
            ))?;

            // TODO: apparently E and D formats can specify the number of digits in the exponent, that will
            // need added to the format spec.
            match fmt {
                RealFmt::D => self.serialize_real_exp(v, width, precision, scale, "D", None),
                RealFmt::E => self.serialize_real_exp(v, width, precision, scale, "E", None),
                RealFmt::F => todo!(),
                RealFmt::G => todo!(),
            }
        } else {
            Err(SError::FormatTypeMismatch { spec_type: next_fmt, serde_type: "float", field_name: self.try_prev_field().map(|f| f.to_string()) })
        }
    }

    fn serialize_real_exp(&mut self, v: f64, width: u32, precision: u32, scale: i32, exp_ch: &str, n_exp_digits: Option<u32>) -> SResult<()> {
        let v_is_neg = v < 0.0;
        let v = d2d(v);
        
        // This is complicated so some examples using e12.3 as the format
        // Value    | Mantissa | Exponent | Fortran   | Representation 
        // 3.14     | 314      | -2       | 0.314E+01 | (mantissa // 10^3).(mantissa % 10^3)E(exponent+3) 
        // 0.0314   | 314      | -4       | 0.314E-01 | (mantissa // 10^3).(mantissa % 10^3)E(exponent+3)
        // 3140.0   | 314      | +1       | 0.314E+04 | (mantissa // 10^3).(mantissa % 10^3)E(exponent+3)
        // 3141.59  | 314159   | -2       | 0.314E+04 | (mantissa // 10^6).(mantissa % 10^6)E(exponent+6)
        //
        // Then scaling shifts where the decimal point is: +ve moves it right, -ve left. So 3.14 formatted
        // as 1pe12.3 would look like 3.140E+00, and 2pe12.3 like 31.40E-01. With +ve scales, we end up with
        // more sig figs (e.g. 3.1415 formatted as 1pe12.3 becomes 3.141E+00). With -ve scales, we keep the
        // same number of digits after the decimal (so -2pe12.3 => 0.003E+03).
        //
        // Also as far as I can tell for spacing, a leading zero before the decimal is optional, but a negative
        // sign is not. so .314E+01 will fit in an 8-wide format, but not a 7-wide. (At 9-wide it gets the leading 0.)
        // If it's negative (-.314E+01), it needs at least 9 characters. At 10, it becomes -0.314E+01.
        let mantissa = v.mantissa;
        let mut b = itoa::Buffer::new();
        let s = b.format(mantissa);
        let m_bytes = s.as_bytes();
        
        
        let exponent = v.exponent + m_bytes.len() as i32 - scale;
        let mut b = itoa::Buffer::new();
        let s = b.format(exponent.abs());
        let e_bytes = s.as_bytes();
        
        // Include precision # digits, plus decimal point, and the exponent. If the number of digits
        // in the exponent isn't given, it will always be 4 characters wide. (If it needs three digits,
        // the 'E' or 'D' is dropped.) Otherwise it seems to be 2 for the E+ or E- and the number of digits.
        // If the exponent won't fit, this is a number we can't format, so print out the *'s and return.
        let exp_nchar = if let Some(n) = n_exp_digits {
            if e_bytes.len() > n as usize {
                for _ in 0..width {
                    self.buf.write(b"*")?;
                }
                return Ok(())
            }
            n + 2
        } else {
            if e_bytes.len() > 3 {
                for _ in 0..width {
                    self.buf.write(b"*")?;
                }
                return Ok(())
            }
            4
        };
        let min_width = if v_is_neg { precision + 2 + exp_nchar } else { precision + 1 + exp_nchar};
        if width < min_width {
            for _ in 0..width {
                self.buf.write(b"*")?;
            }
            return Ok(());
        }

        let nspaces = if width > min_width { width - min_width - 1 } else { 0 };
        for _ in 0..nspaces {
            self.buf.write(b" ")?;
        }

        if v_is_neg {
            self.buf.write(b"-")?;
        }

        if scale > 0 {
            let mut i = 0;
            for _ in 0..scale {
                let c = m_bytes.get(i..i+1).unwrap_or(b"0");
                self.buf.write(c)?;
                i += 1;
            }
            self.buf.write(b".")?;
            let n_after_decimal = if scale <= 1 { precision } else { precision - scale as u32 + 1};
            for _ in 0..n_after_decimal {
                let c = m_bytes.get(i..i+1).unwrap_or(b"0");
                self.buf.write(c)?;
                i += 1;
            }
        } else {
            if width > min_width {
                // if we have at least one extra character, write the leading zero
                self.buf.write(b"0")?;
            }
            self.buf.write(b".")?;
            let mut i = 0;
            for _ in 0..precision {
                if i < -scale {
                    self.buf.write(b"0")?;
                } else {
                    let j = (i + scale) as usize;
                    let c = m_bytes.get(j..j+1).unwrap_or(b"0");
                    self.buf.write(c)?;
                }
                i += 1;
            }
        }

        let n_digits = if e_bytes.len() < (exp_nchar as usize) - 2 {
            self.buf.write(exp_ch.as_bytes())?;
            exp_nchar - 2
        } else {
            exp_nchar - 1
        };

        if exponent < 0 {
            self.buf.write(b"-")?;
        } else {
            self.buf.write(b"+")?;
        }

        // Pad with 0s if needed
        for _ in 0..(n_digits as usize - e_bytes.len()) {
            self.buf.write(b"0")?;
        }
        self.buf.write(e_bytes)?;


        Ok(())
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
        self.serialize_real(v as f64)
    }

    fn serialize_f64(self, v: f64) -> Result<Self::Ok, Self::Error> {
        self.serialize_real(v)
    }

    fn serialize_char(self, v: char) -> Result<Self::Ok, Self::Error> {
        self.serialize_str(&v.to_string())
    }

    fn serialize_str(self, v: &str) -> Result<Self::Ok, Self::Error> {
        self.serialize_bytes(v.as_bytes())
    }

    fn serialize_bytes(self, v: &[u8]) -> Result<Self::Ok, Self::Error> {
        let next_fmt = *self.next_fmt()?;
        if let FortField::Char { width } = next_fmt {
            if let Some(width) = width {
                let w = width as usize;
                if v.len() >= w {
                    self.buf.write(&v[..w])?;
                } else {
                    for _ in 0..(w - v.len()) {
                        self.buf.write(b" ")?;
                    }
                    self.buf.write(v)?;
                }
                Ok(())
            } else {
                // With no width specified, the full string is written out with its exact length.
                self.buf.write(v)?;
                Ok(())
            }
        } else {
            Err(SError::FormatTypeMismatch { spec_type: next_fmt, serde_type: "char/str/bytes", field_name: self.try_prev_field().map(|f| f.to_string()) })
        }
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

// This will have to be a different structure; if it has known fields, then
// this will have to build a Vec<Vec<u8>> to put the elements in the correct
// order and write that to the buffer at the end. Same of SerializeMap.
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

    #[test]
    fn test_char() {
        let fmt = FortFormat::parse("(a)").unwrap();
        let s = to_string('x', &fmt).unwrap();
        assert_eq!(s, "x");

        let fmt = FortFormat::parse("(a2)").unwrap();
        let s = to_string('x', &fmt).unwrap();
        assert_eq!(s, " x");
    }

    #[test]
    fn test_str() {
        let fmt = FortFormat::parse("(a)").unwrap();
        let s = to_string("abcde", &fmt).unwrap();
        assert_eq!(s, "abcde");

        let fmt = FortFormat::parse("(a5)").unwrap();
        let s = to_string("abc", &fmt).unwrap();
        assert_eq!(s, "  abc");
        let s = to_string("abcde", &fmt).unwrap();
        assert_eq!(s, "abcde");
        let s = to_string("abcdefg", &fmt).unwrap();
        assert_eq!(s, "abcde");
    }

    #[test]
    fn test_real_e() {
        let fmt = FortFormat::parse("(e12.3)").unwrap();
        let s = to_string(0.0314, &fmt).unwrap();
        assert_eq!(s, "   0.314E-01");
        let s = to_string(3.14, &fmt).unwrap();
        assert_eq!(s, "   0.314E+01");
        let s = to_string(3140.0, &fmt).unwrap();
        assert_eq!(s, "   0.314E+04");
        let s = to_string(3141.59, &fmt).unwrap();
        assert_eq!(s, "   0.314E+04");
        let s = to_string(3.14e120, &fmt).unwrap();
        assert_eq!(s, "   0.314+121");

        let fmt = FortFormat::parse("(1pe12.3)").unwrap();
        let s = to_string(3.14, &fmt).unwrap();
        assert_eq!(s, "   3.140E+00");
        let s = to_string(3.1415, &fmt).unwrap();
        assert_eq!(s, "   3.141E+00");

        let fmt = FortFormat::parse("(2pe12.3)").unwrap();
        let s = to_string(3.14, &fmt).unwrap();
        assert_eq!(s, "   31.40E-01");

        let fmt = FortFormat::parse("(-1pe12.3)").unwrap();
        let s = to_string(3.14, &fmt).unwrap();
        assert_eq!(s, "   0.031E+02");

        let fmt = FortFormat::parse("(-2pe12.3)").unwrap();
        let s = to_string(3.14, &fmt).unwrap();
        assert_eq!(s, "   0.003E+03");

        let fmt = FortFormat::parse("(e7.3)").unwrap();
        let s = to_string(3.14, &fmt).unwrap();
        assert_eq!(s, "*******");
        let s = to_string(-3.14, &fmt).unwrap();
        assert_eq!(s, "*******");

        let fmt = FortFormat::parse("(e8.3)").unwrap();
        let s = to_string(3.14, &fmt).unwrap();
        assert_eq!(s, ".314E+01");
        let s = to_string(-3.14, &fmt).unwrap();
        assert_eq!(s, "********");

        let fmt = FortFormat::parse("(e9.3)").unwrap();
        let s = to_string(3.14, &fmt).unwrap();
        assert_eq!(s, "0.314E+01");
        let s = to_string(-3.14, &fmt).unwrap();
        assert_eq!(s, "-.314E+01");
        // Don't have these implemented yet - format parsing needs to handle the eN at the end
        // let fmt = FortFormat::parse("(e12.3e1)").unwrap();
        // let s = to_string(3.14e5, &fmt).unwrap();
        // assert_eq!(s, "    0.314E+6");
        // let s = to_string(3.14e15, &fmt).unwrap();
        // assert_eq!(s, "************");

        // let fmt = FortFormat::parse("(e12.3e5)").unwrap();
        // let s = to_string(3.14, &fmt).unwrap();
        // assert_eq!(s, "0.314E+00001");

    }

    #[test]
    fn test_real_d() {
        let fmt = FortFormat::parse("(d12.3)").unwrap();
        let s = to_string(3.14, &fmt).unwrap();
        assert_eq!(s, "   0.314D+01");
        let s = to_string(3.14e120, &fmt).unwrap();
        assert_eq!(s, "   0.314+121");

        let fmt = FortFormat::parse("(1pd12.3)").unwrap();
        let s = to_string(3.14, &fmt).unwrap();
        assert_eq!(s, "   3.140D+00");

        let fmt = FortFormat::parse("(-1pd12.3)").unwrap();
        let s = to_string(3.14, &fmt).unwrap();
        assert_eq!(s, "   0.031D+02");

        let fmt = FortFormat::parse("(-2pd12.3)").unwrap();
        let s = to_string(3.14, &fmt).unwrap();
        assert_eq!(s, "   0.003D+03");

    }
}