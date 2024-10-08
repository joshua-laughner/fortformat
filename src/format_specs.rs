//! Represent Fortran formats as Rust types.
//! 
//! Fortran formats exist in two types: fixed and list-directed.
//! Fixed formats specify the syntax and width of each field in the input string,
//! for example "(a4,1x,i5.2)". Fixed formats read or write data based on the
//! number of characters in the format. The example "(a4,1x,i5.2)" would read in
//! the first four characters as a string (a4), skip one character (1x), and read
//! in five more characters as an integer (i5). When writing, each field will always
//! take up the number of characters specified by the with (4 and 5 in the given example).
//! If a value requires more characters to write than it is provided, it will be
//! output as a series of `*`.
//! 
//! List directed formats do not have predefined widths. Instead, fields are separated
//! by whitespace, commas, or both. Strings that contain these separators must be enclosed
//! in strings to be parsed as a single element. Additionally, list directed formats cannot
//! handle octal- or hexadecial- formatted integers nor scaled floating point values.
//! 
//! The first step in working with a Fortran format string such as "(a4,1x,i5.2)"
//! is to parse it into a [`FortFormat`] with its `parse` method:
//! 
//! ```
//! # use fortformat::format_specs::FortFormat;
//! let ff = FortFormat::parse("(a4,1x,i5.2)").unwrap();
//! ```
//! 
//! List directed format is represented in a Fortran read or write statement
//! by a `*`, so parsing an `*` returns a list directed format:
//! 
//! ```
//! # use fortformat::format_specs::FortFormat;
//! let ff = FortFormat::parse("*").unwrap();
//! assert!(ff.is_list_directed());
//! ```
//! 
//! However, if you know that the format is list directed, you can
//! construct [`FortFormat::ListDirected`] directly, without parsing.
//! 
//! Once you have a [`FortFormat`] instance, it can be used for 
//! [deserialization](crate::de) or [serialization](crate::ser),
//! or you can inspect the fields directly with the `into_fields`,
//! `iter_fields`, and `iter_non_skip_fields` methods on [`FortFormat`].
use std::fmt::{Display, Write};

use itertools::Itertools;
use pest::{Parser, iterators::Pair, RuleType};

type PResult<T> = std::result::Result<T, PError>;

/// Represents an error in parsing a format string
#[derive(Debug)]
pub struct PError;

impl <R: RuleType> From<pest::error::Error<R>> for PError {
    fn from(value: pest::error::Error<R>) -> Self {
        // TODO: provide some useful information
        Self
    }
}

impl Display for PError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Format parsing error")
    }
}

/// Represents an error indexing into a list of fields
#[derive(Debug)]
pub enum FieldIndexError {
    IndexOutOfRange{index: usize, len: usize},
    IsListDirected,
}

impl Display for FieldIndexError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FieldIndexError::IndexOutOfRange { index, len } => {
                write!(f, "index {index} is out of range for a FortFormat instance with {len} fields")
            },
            FieldIndexError::IsListDirected => {
                write!(f, "cannot index into a FortFormat::ListDirected instance")
            },
        }
    }
}

impl std::error::Error for FieldIndexError {}

#[derive(Parser)]
#[grammar = "fort.pest"]
pub(crate) struct FortParser;

/// Representation of which format a float (i.e. real) number is written in.
/// 
/// Fortran can write floating point values in four formats: 
/// - `F`: non-exponential with a fixed number of digits after the decimal,
/// - `G`: non-exponential with as many digits after the decimal as possible for the specified width,
/// - `E`: exponential (e.g. 1.0E+02) for single precision numbers, and
/// - `D`: like `E` but for double precision numbers.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RealFmt {
    D,
    E,
    F,
    G
}

impl Display for RealFmt {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            RealFmt::D => "d",
            RealFmt::E => "e",
            RealFmt::F => "f",
            RealFmt::G => "g",
        };

        write!(f, "{s}")
    }
}

impl RealFmt {
    /// `true` if the format is `RealFmt::D`, `false` otherwise
    pub fn is_d(&self) -> bool {
        if let Self::D = self {
            true
        } else {
            false
        }
    }

    /// `true` if the format is `RealFmt::E`, `false` otherwise
    pub fn is_e(&self) -> bool {
        if let Self::E = self {
            true
        } else {
            false
        }
    }

    /// `true` if the format is `RealFmt::F`, `false` otherwise
    pub fn is_f(&self) -> bool {
        if let Self::F = self {
            true
        } else {
            false
        }
    }

    /// `true` if the format is `RealFmt::G`, `false` otherwise
    pub fn is_g(&self) -> bool {
        if let Self::G = self {
            true
        } else {
            false
        }
    }
}

/// Which base (10, 8, or 16) an integer format uses
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IntBase {
    Decimal,
    Octal,
    Hexadecimal
}

impl Display for IntBase {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            IntBase::Decimal => "i",
            IntBase::Octal => "o",
            IntBase::Hexadecimal => "z",
        };

        write!(f, "{s}")
    }
}


/// A representation of a full entry in a format specification, i.e. one `a`, `i`, etc.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FortField {
    /// A Fortran character (i.e. string) specification.
    /// 
    /// If the format specifier included a width (i.e. "a4"), then the inner field `width`
    /// will hold that width. If not, `width` will be `None`. Fields with no width specified
    /// can be assumed to be 1 character wide.
    Char{width: Option<u32>},

    /// A Fortran logical (i.e. boolean) specification.
    /// 
    /// All logical specifications include a width (i.e. 4 in "l4"), this will be stored
    /// as the inner `width` field.
    Logical{width: u32},

    /// A Fortran integer specification.
    /// 
    /// All integer specifications have a width (i.e. 4 in "i4" or "i4.1"). Integer specs can include
    /// a minimum number of digits; if the number of digits is less than this, the value will
    /// be front-padded by zeros. This minimum width is the `zeros` inner field. Finally,
    /// `base` indicates which base (10, 8, or 16) the integer is written in.
    Integer{width: u32, zeros: Option<u32>, base: IntBase}, // TODO: check if `p` scaling affects integers

    /// A Fortran real (i.e. floating point) specification.
    /// 
    /// All real specifications have a width (i.e. 4 in "f4" or "f4.1") which will be stored in the
    /// `width` inner field. If the specification included a precision (i.e. the 1 in "f4.1"), this will
    /// be stored in the `precision` inner field; otherwise, that will be `None`. The format style (i.e. D, 
    /// E, F, or G) will be stored in `fmt`. If any scaling from a "p" specification affects this entry, it
    /// will be stored in the `scale` value; that will be 1 if no "p" specification is in effect.
    Real{width: u32, precision: Option<u32>, fmt: RealFmt, scale: i32},

    /// A specification indicating to leave a blank space.
    Skip,

    /// Indicates that the next field may be any type and width - usually because the format
    /// was `*`, indicating a list-directed format.
    Any
}

impl FortField {
    /// Returns `true` if the field represents a positioning specifier (T, TL, TR, or X), `false` otherwise.
    pub fn is_positional(&self) -> bool {
        match self {
            FortField::Char { width: _ } => false,
            FortField::Logical { width: _ } => false,
            FortField::Integer { width: _, zeros: _, base: _ } => false,
            FortField::Real { width: _, precision: _, fmt: _, scale: _ } => false,
            FortField::Any => false,
            FortField::Skip => true,
        }
    }

    /// Returns the number of bytes required by this field. Only returns `None` if the field type is `Any`,
    /// meaning list-directed format.
    pub fn width(&self) -> Option<u32> {
        match self {
            FortField::Char { width } => Some(width.unwrap_or(1)),
            FortField::Logical { width } => Some(*width),
            FortField::Integer { width, zeros: _, base: _ } => Some(*width),
            FortField::Real { width, precision: _, fmt: _, scale: _ } => Some(*width),
            FortField::Any => None,
            FortField::Skip => Some(1),
        }
    }

    /// Return the [Polars DataType](polars::datatypes::DataType) that matches this field type.
    /// 
    /// Note that because integer format specs do not carry information about the number of bytes
    /// used, any integer format spec will map to an `Int64` DataType. Also, for simplicity, all
    /// float specs map to a `Float64` type, although this may change in the future. Positional
    /// format specs will return a `None`.
    #[cfg(feature = "dataframes")]
    pub fn polars_dtype(&self) -> Option<polars::datatypes::DataType> {
        match self {
            FortField::Char { width: _ } => Some(polars::datatypes::DataType::Utf8),
            FortField::Logical { width: _ } => Some(polars::datatypes::DataType::Boolean),
            FortField::Integer { width: _, zeros: _, base: _ } => Some(polars::datatypes::DataType::Int64),
            FortField::Real { width: _, precision: _, fmt: _, scale: _ } => Some(polars::datatypes::DataType::Float64),
            FortField::Any => unimplemented!("polars dtype for list directed format"),
            FortField::Skip => None,
        }
    }

    fn display_helper<W: std::fmt::Write>(&self, include_scale: bool, mut f: W) -> std::fmt::Result {
        match self {
            FortField::Char { width } => write!(f, "a{}", width.unwrap_or(1)),
            FortField::Logical { width } => write!(f, "l{width}"),
            FortField::Integer { width, zeros, base } => {
                if let Some(m) = zeros {
                    write!(f, "{base}{width}.{m}")
                } else {
                    write!(f, "{base}{width}")
                }
            },
            FortField::Real { width, precision, fmt, scale } => {
                let p = if scale == &0 || !include_scale { "".to_owned() } else { format!("{scale}p") };

                if let Some(m) = precision {
                    write!(f, "{p}{fmt}{width}.{m}")
                } else {
                    write!(f, "{p}{fmt}{width}")
                }
            },
            FortField::Any => write!(f, "*"),
            FortField::Skip => write!(f, "x"),
        }
    }

    fn as_str_and_scale(&self) -> (String, Option<i32>) {
        let scale = match self {
            FortField::Char { width } => None,
            FortField::Logical { width } => None,
            FortField::Integer { width, zeros, base } => None,
            FortField::Real { width, precision, fmt, scale } => Some(*scale),
            FortField::Skip => None,
            FortField::Any => None,
        };
        let mut s = String::new();
        self.display_helper(false, &mut s)
            .expect("writing to a string should not fail");
        (s, scale)
    }
}

impl Display for FortField {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.display_helper(true, f)
    }
}

/// A representation of any scalar Fortran value (logical, character, integer, or real)
/// 
/// Note that Fortran character arrays are mapped to `String`s for convenience. Since Fortran 
/// predates the Unicode standard, this makes the assumption that any formatted character output
/// would be in ASCII. If this is not true in some use cases, a new variant will need to be
/// added.
#[derive(Debug, PartialEq)]
pub enum FortValue {
    Logical(bool),
    Char(String),
    Integer(i64),
    Real(f64)
}

#[cfg(feature = "serde")]
impl<'de> serde::Deserialize<'de> for FortValue {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de> {
        deserializer.deserialize_any(crate::de::FortValueVisitor)
    }
}

#[cfg(feature = "serde")]
impl serde::Serialize for FortValue {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer {
        match self {
            FortValue::Logical(b) => b.serialize(serializer),
            FortValue::Char(s) => s.serialize(serializer),
            FortValue::Integer(i) => i.serialize(serializer),
            FortValue::Real(r) => r.serialize(serializer),
        }
    }
}

#[cfg(feature = "dataframes")]
impl From<FortValue> for polars::datatypes::AnyValue<'_> {
    fn from(value: FortValue) -> Self {
        match value {
            FortValue::Logical(b) => polars::datatypes::AnyValue::Boolean(b),
            FortValue::Char(s) => polars::datatypes::AnyValue::Utf8Owned(s.into()),
            FortValue::Integer(i) => polars::datatypes::AnyValue::Int64(i),
            FortValue::Real(f) => polars::datatypes::AnyValue::Float64(f),
        }
    }
}


/// An iterator over fields in a format string.
/// 
/// This can iterate over all fields or only non-positional ones.
/// Which set it yields will be documented by the functions that return it.
pub struct FieldIter<'i>{
    all: bool,
    fields: Option<std::slice::Iter<'i, FortField>>,
}

impl<'i> Iterator for FieldIter<'i> {
    type Item = &'i FortField;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(fields) = &mut self.fields {
            loop {
                let element = fields.next();
                if !self.all && element.map(|e| e.is_positional()).unwrap_or(false) {
                    // Keep going, we don't want to return skips or other positional
                    // values.
                } else {
                    return element;
                }
            }
        } else {
            None
        }

        
    }
}


/// A wrapper struct containing a full format string's specifiers
/// 
/// Generally the first step in handling a Fortran format string will be to
/// pass it to this struct's `parse` method:
/// 
/// ```
/// # use fortformat::format_specs::FortFormat;
/// let ff = FortFormat::parse("(a4,1x,i5.2)").unwrap();
/// ```
/// 
/// Note that the format string must include the opening and closing parentheses.
#[derive(Debug, Clone)]
pub enum FortFormat {
    Fixed(Vec<FortField>),
    ListDirected
}

impl FortFormat {
    /// Returns `true` if this is the `ListDirected` variant.
    pub fn is_list_directed(&self) -> bool {
        if let Self::ListDirected = self {
            true
        } else {
            false
        }
    }

    /// Get a reference to one of the fields in this format by index.
    /// 
    /// Note that `index` is 0-based.
    /// 
    /// # Returns
    /// `None` if the index is too large or this is a list-directed format,
    /// `Some` with a reference to the field otherwise.
    pub fn get_field(&self, index: usize) -> Option<&FortField> {
        match self {
            FortFormat::Fixed(vec) => vec.get(index),
            FortFormat::ListDirected => Some(&FortField::Any),
        }
    }

    /// Replace the existing field at `index` with a the new value `field`.
    /// 
    /// # Returns
    /// An error if `index` is greater than or equal to the number of fields (since `index`
    /// is 0-based), or if this is a list-directed format. Note the difference between this
    /// and [`Self::insert_field`], whereas `insert_field` allows `index` to equal the number
    /// of fields (to act as a push), this does not.
    pub fn set_field(&mut self, index: usize, field: FortField) -> Result<(), FieldIndexError>{
        match self {
            FortFormat::Fixed(vec) => {
                if index < vec.len() {
                    vec[index] = field;
                    Ok(())
                } else {
                    Err(FieldIndexError::IndexOutOfRange { index, len: vec.len() })
                }
            },
            FortFormat::ListDirected => Err(FieldIndexError::IsListDirected),
        }
    }

    /// Insert a new field into the format at index.
    /// 
    /// This follows the convention for [`Vec::insert`] that the new field will be at `index`
    /// and all existing fields at `index` or greater are shifted right. If `index` equals the
    /// length of the vector of fields, then this acts like [`Vec::push`], adding the new field
    /// to the end of the format.
    /// 
    /// # Returns
    /// An error if `index` is greater than the number of fields or this is a list-directed format.
    pub fn insert_field(&mut self, index: usize, field: FortField) -> Result<(), FieldIndexError> {
        match self {
            FortFormat::Fixed(vec) => {
                if index <= vec.len() {
                    vec.insert(index, field);
                    Ok(())
                } else {
                    Err(FieldIndexError::IndexOutOfRange { index, len: vec.len() })
                }
            },
            FortFormat::ListDirected => Err(FieldIndexError::IsListDirected),
        }
    }

    /// Parse a Fortran format string and return a `FortFormat` instance.
    /// 
    /// The format string must include the opening and closing parentheses. That is,
    /// `"(a)"` is valid, but `"a"` is not. Spaces, tabs, carriage returns, and newlines
    /// are all considered whitespace and ignored in parsing.
    /// 
    /// Returns an error if the format string has invalid syntax.
    pub fn parse(fmt_str: &str) -> PResult<Self> {
        if fmt_str.trim() == "*" {
            return Ok(Self::ListDirected);
        }

        let mut fields = vec![];
        let tree = FortParser::parse(Rule::format, fmt_str)?.next().unwrap();

        let mut stack: Vec<_> = tree.into_inner().rev().collect();
        let mut next_repeat: usize = 1;
        let mut curr_scale: i32 = 0;

        while stack.len() > 0 {
            let pair = stack.pop().unwrap();
            let kind = match pair.as_rule() {
                // Should never hit a format; that is the top level rule
                Rule::format => unreachable!(),
                
                // If we get a width or precision at this point (somehow), that's wrong - we should
                // only encounter widths as part of fields
                Rule::width => return Err(PError),
                Rule::prec => return Err(PError),
                Rule::signed => return Err(PError),

                // Ignore whitespace
                Rule::WHITESPACE => continue,
                
                // End of string, exit the loop
                Rule::EOI => break,

                // Set the next repeat value; we can safely parse this into a u32
                // because the rule specifies digits only
                Rule::repeat => {
                    next_repeat = pair.as_str().parse().unwrap();
                    continue;
                },

                Rule::scale => {
                    curr_scale = consume_signed_from_pair(pair).unwrap_or(0);
                    continue;
                },

                Rule::field | Rule::element => {
                    for inner in pair.into_inner().rev() {
                        stack.push(inner);
                    }
                    continue;
                },

                Rule::expr => {
                    for _ in 0..next_repeat {
                        for inner in pair.clone().into_inner().rev() {
                            stack.push(inner);
                        }   
                    }
                    next_repeat = 1;
                    continue;
                }

                Rule::skip => FortField::Skip,
                Rule::char => FortField::Char { width: consume_width_from_pair(pair) },
                Rule::logical => {
                    let width = consume_width_from_pair(pair)
                        .ok_or_else(|| PError)?;
                    FortField::Logical { width }
                },
                Rule::integer => {
                    let (width, zeros) = consume_req_width_and_prec_from_pair(pair, "integer")?;
                    FortField::Integer { width, zeros, base: IntBase::Decimal }
                },
                Rule::octal => {
                    let (width, zeros) = consume_req_width_and_prec_from_pair(pair, "octal")?;
                    FortField::Integer { width, zeros, base: IntBase::Octal }
                },
                Rule::hex => {
                    let (width, zeros) = consume_req_width_and_prec_from_pair(pair, "hexadecimal")?;
                    FortField::Integer { width, zeros, base: IntBase::Hexadecimal }
                },
                Rule::real => {
                    let (width, precision) = consume_req_width_and_prec_from_pair(pair, "f-real")?;
                    FortField::Real { width, precision, fmt: RealFmt::F, scale: curr_scale }
                },
                Rule::realorexp => {
                    let (width, precision) = consume_req_width_and_prec_from_pair(pair, "f-real")?;
                    FortField::Real { width, precision, fmt: RealFmt::G, scale: curr_scale }
                },
                Rule::exponential => {
                    let (width, precision) = consume_req_width_and_prec_from_pair(pair, "f-real")?;
                    FortField::Real { width, precision, fmt: RealFmt::E, scale: curr_scale }
                },
                Rule::expdouble => {
                    let (width, precision) = consume_req_width_and_prec_from_pair(pair, "f-real")?;
                    FortField::Real { width, precision, fmt: RealFmt::D, scale: curr_scale }
                },
            };

            for _ in 0..next_repeat {
                fields.push(kind);
            }
            next_repeat = 1;
        }
        // let fmt = if let Rule::format(f) = tree { f } else { unreachable!()};

        Ok(Self::Fixed(fields))
    }

    /// Consume the `FortFormat` instance and return the inner `Vec<FortField>`.
    /// If this is a `ListDirected` format, it will return `None`.
    pub fn into_fields(self) -> Option<Vec<FortField>> {
        match self {
            FortFormat::Fixed(vec) => Some(vec),
            FortFormat::ListDirected => None,
        }
    }

    /// Iterate over all fields in this format (including positionals)
    pub fn iter_fields(&self) -> FieldIter {
        match self {
            FortFormat::Fixed(vec) => FieldIter{fields: Some(vec.iter()), all: true},
            FortFormat::ListDirected => FieldIter { fields: None, all: true },
        }
        
    }

    /// Iterate over non-positional fields in this format
    pub fn iter_non_pos_fields(&self) -> FieldIter {
        match self {
            FortFormat::Fixed(vec) => FieldIter{fields: Some(vec.iter()), all: false},
            FortFormat::ListDirected => FieldIter { fields: None, all: false },
        }
    }

    /// Return the number of non-positional fields in this format
    pub fn non_pos_len(&self) -> usize {
        // TODO: cache this somehow?
        let n = self.iter_non_pos_fields().count();
        n
    }

    /// Return a series of tuples containing fields and the number of times they
    /// are repeated consecutively.
    /// 
    /// See [`Self::fmt_string`] for how `max_group_len` works, as this is the
    /// underlying grouping function that enables that.
    /// 
    /// # Developer note
    /// This function is private for now because enabling larger groups will
    /// require a change in the output type. After that is implemented, this
    /// can be made part of the public interface.
    fn collapsed_version(&self, max_group_len: usize) -> Vec<(u32, FortField)> {
        // For now, we won't handle repeated groups, but what I think that would involve
        // is, after we do the first reduction of adjacent identical fields, then we do a
        // number of iterations up to the max_group_len and see if grouping different sections
        // of the format string by a given group size reduces the length further.
        let it = self.iter_fields().map(|f| (1, f.to_owned()));
        if max_group_len == 0 {
            // Special case - don't group
            return it.collect();
        }

        let one_grouped = it.coalesce(|(n, prev_fmt), (m, curr_fmt)| {
            if prev_fmt == curr_fmt {
                Ok((n + 1, prev_fmt))
            } else {
                Err(( (n, prev_fmt), (m, curr_fmt) ))
            }
        });

        one_grouped.collect()

        // TODO: if max_group_len > 1, do higher-order grouping
    }

    /// Create a Fortran-compatible format string from this instance, grouping like format specifiers.
    /// 
    /// The `max_group_len` parameter controls the group size. A value of `0` will not group any
    /// terms, so every field in this format will have its own entry in the string. A value of `1`
    /// will group identical terms, for example, three "f13.8" fields in a row become "3f13.8".
    /// At present, values >1 do the same, but eventually the plan is to allow this function to
    /// find repeated sets of fields, where if (for example), grouping adjacent identical fields
    /// left you with "a2,1x,f13.8" repeated four times, then a `max_group_len >= 3` should produce
    /// "4(a2,1x,f13.8)".
    pub fn fmt_string(&self, max_group_len: usize) -> String {
        let mut fmt_str = "(".to_string();
        let mut curr_scale = 0;
        let mut first_el = true;
        for (rep, fmt_el) in self.collapsed_version(max_group_len) {
            let (el_str, next_scale) = fmt_el.as_str_and_scale();
            let include_scale = if let Some(s) = next_scale {
                if s == curr_scale {
                    false
                } else {
                    curr_scale = s;
                    true
                }
            } else {
                false
            };

            let include_rep = rep != 1 || fmt_el.is_positional();

            if first_el {
                first_el = false;
            } else {
                fmt_str.push(',');
            }

            // If we need to write the scale, e.g. "1pe13.5" and a number of repetitions
            // then we need parentheses around the format to separate the scale and the reps,
            // e.g. "10(1pe13.5)"
            if include_rep && include_scale {
                write!(&mut fmt_str, "{rep}({curr_scale}p").expect("writing to a string should not fail");
            } else if include_rep {
                write!(&mut fmt_str, "{rep}").expect("writing to a string should not fail");
            }

            write!(&mut fmt_str, "{el_str}").expect("writing to a string should not fail");
            
            if include_rep && include_scale {
                write!(&mut fmt_str, ")").expect("writing to a string should not fail");
            }
        }
        fmt_str.push(')');
        fmt_str
    }
}

fn consume_width_from_pair(pair: Pair<Rule>) -> Option<u32> {
    let mut stack: Vec<_> = pair.into_inner().rev().collect();
    consume_width(&mut stack)
}

fn consume_width(stack: &mut Vec<Pair<Rule>>) -> Option<u32> {
    if let Rule::width = stack.last()?.as_rule() {
        let w: u32 = stack.pop().unwrap().as_str().parse().unwrap();
        Some(w)
    }else {
        None
    }
}

fn _consume_prec_from_pair(pair: Pair<Rule>) -> Option<u32> {
    let mut stack: Vec<_> = pair.into_inner().rev().collect();
    consume_prec(&mut stack)
}

fn consume_prec(stack: &mut Vec<Pair<Rule>>) -> Option<u32> {
    if let Rule::prec = stack.last()?.as_rule() {
        let p: u32 = stack.pop().unwrap().as_str().parse().unwrap();
        Some(p)
    }else {
        None
    }
}

fn consume_signed_from_pair(pair: Pair<Rule>) -> Option<i32> {
    let mut stack: Vec<_> = pair.into_inner().rev().collect();
    consume_signed(&mut stack)
}

fn consume_signed(stack: &mut Vec<Pair<Rule>>) -> Option<i32> {
    if let Rule::signed = stack.last()?.as_rule() {
        let v: i32 = stack.pop().unwrap().as_str().parse().unwrap();
        Some(v)
    }else{
        None
    }
}

fn consume_width_and_prec(stack: &mut Vec<Pair<Rule>>) -> (Option<u32>, Option<u32>) {
    let width = if let Some(w) = consume_width(stack) {
        Some(w)
    }else{
        return (None, None)
    };

    let prec = consume_prec(stack);

    (width, prec)
}

fn consume_req_width_and_prec_from_pair(pair: Pair<Rule>, _kind: &str) -> PResult<(u32, Option<u32>)> {
    let mut stack: Vec<_> = pair.into_inner().rev().collect();
    consume_req_width_and_prec(&mut stack, _kind)
}

fn consume_req_width_and_prec(stack: &mut Vec<Pair<Rule>>, _kind: &str) -> PResult<(u32, Option<u32>)> {
    let (w_opt, p) = consume_width_and_prec(stack);
    let w = w_opt.ok_or_else(|| PError)?;
    Ok((w, p))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_surrounding_whitespace() -> PResult<()> {
        FortFormat::parse(" (a) \n")?;
        FortFormat::parse(" (a) \r")?;
        FortFormat::parse(" (a) \r\n")?;
        Ok(())
    }

    #[test]
    fn test_char() -> PResult<()> {
        let v = FortFormat::parse("(a)")?.into_fields().unwrap();
        assert_eq!(v.len(), 1, "Parsing '(a)' did not return exactly 1 field");
        assert_eq!(v.last().unwrap(), &FortField::Char { width: None }, "Parsing '(a)' failed");

        let v = FortFormat::parse("(a16)")?.into_fields().unwrap();
        assert_eq!(v.len(), 1, "Parsing '(a16)' did not return exactly 1 field");
        assert_eq!(v.last().unwrap(), &FortField::Char { width: Some(16) }, "Parsing '(a16)' failed");

        let e = FortFormat::parse("(a-16)");
        assert!(e.is_err(), "Parsing '(a-16)' (negative width) did not return an error");
        Ok(())
    }

    #[test]
    fn test_logical() -> PResult<()> {
        let v = FortFormat::parse("(l1)")?.into_fields().unwrap();
        assert_eq!(v.len(), 1, "Parsing '(l1)' did not return exactly 1 field");
        assert_eq!(v.last().unwrap(), &FortField::Logical { width: 1 }, "Parsing '(l1)' failed");

        let e = FortFormat::parse("(l)");
        assert!(e.is_err(), "Parsing '(l)' (no width) did not return an error");

        let e = FortFormat::parse("(l-1)");
        assert!(e.is_err(), "Parsing '(l-1)' (negative width) did not return an error");

        Ok(())
    }

    #[test]
    fn test_decimal() -> PResult<()> {
        test_integer(IntBase::Decimal)
    }

    #[test]
    fn test_octal() -> PResult<()> {
        test_integer(IntBase::Octal)
    }

    #[test]
    fn test_hex() -> PResult<()> {
        test_integer(IntBase::Hexadecimal)
    }

    fn test_integer(base: IntBase) -> PResult<()> {


        let v = FortFormat::parse(&format!("({base}8)"))?.into_fields().unwrap();
        assert_eq!(v.len(), 1, "Parsing '({base}8)' did not return exactly 1 field");
        assert_eq!(v.last().unwrap(), &FortField::Integer { width: 8, zeros: None, base }, "Parsing '({base}8)' failed");

        let v = FortFormat::parse(&format!("({base}8.6)"))?.into_fields().unwrap();
        assert_eq!(v.len(), 1, "Parsing '(i{base}.6)' did not return exactly 1 field");
        assert_eq!(v.last().unwrap(), &FortField::Integer { width: 8, zeros: Some(6), base }, "Parsing '({base}8.6)' failed");

        let e = FortFormat::parse(&format!("({base})"));
        assert!(e.is_err(), "Parsing '({base})' (no width) did not return an error");

        let e = FortFormat::parse(&format!("({base}8.)"));
        assert!(e.is_err(), "Parsing '({base}8.)' (missing precision width) did not return an error");

        Ok(())
    }

    #[test]
    fn test_float() -> PResult<()> {
        test_real(RealFmt::F)
    }

    #[test]
    fn test_double() -> PResult<()> {
        test_real(RealFmt::D)
    }

    #[test]
    fn test_exponential() -> PResult<()> {
        test_real(RealFmt::E)
    }

    #[test]
    fn test_gfloat() -> PResult<()> {
        test_real(RealFmt::G)
    }

    fn test_real(fmt: RealFmt) -> PResult<()> {
        let v = FortFormat::parse(&format!("({fmt}8)"))?.into_fields().unwrap();
        assert_eq!(v.len(), 1, "Parsing '({fmt}8)' did not return exactly 1 field");
        assert_eq!(v.last().unwrap(), &FortField::Real { width: 8, precision: None, fmt, scale: 0 }, "Parsing '({fmt}8)' failed");

        let v = FortFormat::parse(&format!("({fmt}8.6)"))?.into_fields().unwrap();
        assert_eq!(v.len(), 1, "Parsing '({fmt}8.6)' did not return exactly 1 field");
        assert_eq!(v.last().unwrap(), &FortField::Real { width: 8, precision: Some(6), fmt, scale: 0 }, "Parsing '({fmt}8.6)' failed");

        let v = FortFormat::parse(&format!("(2p{fmt}8.6)"))?.into_fields().unwrap();
        assert_eq!(v.len(), 1, "Parsing '(2p{fmt}8.6)' did not return exactly 1 field");
        assert_eq!(v.last().unwrap(), &FortField::Real { width: 8, precision: Some(6), fmt, scale: 2 }, "Parsing '(2p{fmt}8.6)' failed");

        let e = FortFormat::parse(&format!("({fmt})"));
        assert!(e.is_err(), "Parsing '({fmt})' (no width) did not return an error");

        let e = FortFormat::parse(&format!("({fmt}8.)"));
        assert!(e.is_err(), "Parsing '({fmt}8.)' (missing precision width) did not return an error");

        Ok(())
    }

    #[test]
    fn test_scales() -> PResult<()> {
        let s = "(f7.2 2p f8.3 -3p f5.1 f6 0p f10.3)";
        let v = FortFormat::parse(s)?.into_fields().unwrap();
        let expected = vec![
            FortField::Real { width: 7, precision: Some(2), fmt: RealFmt::F, scale: 0 },
            FortField::Real { width: 8, precision: Some(3), fmt: RealFmt::F, scale: 2 },
            FortField::Real { width: 5, precision: Some(1), fmt: RealFmt::F, scale: -3 },
            FortField::Real { width: 6, precision: None, fmt: RealFmt::F, scale: -3 },
            FortField::Real { width: 10, precision: Some(3), fmt: RealFmt::F, scale: 0 },
        ];
        assert_eq!(v, expected, "Parsing {s} failed");
        Ok(())
    }

    #[test]
    fn test_elided_scale() -> PResult<()> {
        let v = FortFormat::parse("(-2pf13.5)")?.into_fields().unwrap();
        let expected = [FortField::Real { width: 13, precision: Some(5), fmt: RealFmt::F, scale: -2 }];
        assert_eq!(v, expected);
        Ok(())
    }

    #[test]
    fn test_simple_repeats() -> PResult<()> {
        let s = "(3i8 2f7.2)";
        let v = FortFormat::parse(s)?.into_fields().unwrap();
        let expected = vec![
            FortField::Integer { width: 8, zeros: None, base: IntBase::Decimal },
            FortField::Integer { width: 8, zeros: None, base: IntBase::Decimal },
            FortField::Integer { width: 8, zeros: None, base: IntBase::Decimal },
            FortField::Real { width: 7, precision: Some(2), fmt: RealFmt::F, scale: 0 },
            FortField::Real { width: 7, precision: Some(2), fmt: RealFmt::F, scale: 0 },
        ];
        assert_eq!(v, expected, "Parsing {s} failed");
        Ok(())
    }

    #[test]
    fn test_sequence() -> PResult<()> {
        let s = "(a32 2x l4 i8 f10.3 e11.4 d12.5 g7.2)";
        let v = FortFormat::parse(s)?.into_fields().unwrap();
        let expected = vec![
            FortField::Char { width: Some(32) },
            FortField::Skip,
            FortField::Skip,
            FortField::Logical { width: 4 },
            FortField::Integer { width: 8, zeros: None, base: IntBase::Decimal },
            FortField::Real { width: 10, precision: Some(3), fmt: RealFmt::F, scale: 0 },
            FortField::Real { width: 11, precision: Some(4), fmt: RealFmt::E, scale: 0 },
            FortField::Real { width: 12, precision: Some(5), fmt: RealFmt::D, scale: 0 },
            FortField::Real { width: 7, precision: Some(2), fmt: RealFmt::G, scale: 0 },
        ];

        assert_eq!(v, expected, "Parsing {s} failed");
        Ok(())
    }

    #[test]
    fn test_nested_one_level() -> PResult<()> {
        let s = "(a32 2(1x f7.4))";
        let v = FortFormat::parse(s)?.into_fields().unwrap();
        let expected = vec![
            FortField::Char { width: Some(32) },
            FortField::Skip,
            FortField::Real { width: 7, precision: Some(4), fmt: RealFmt::F, scale: 0 },
            FortField::Skip,
            FortField::Real { width: 7, precision: Some(4), fmt: RealFmt::F, scale: 0 },
        ];

        assert_eq!(v, expected, "Parsing {s} failed");
        Ok(())
    }

    #[test]
    fn test_nested_two_level() -> PResult<()> {
        let s = "(3(a8 1x 2(i4 1x f7.4 1x)))";
        let v = FortFormat::parse(s)?.into_fields().unwrap();
        let expected = vec![
            FortField::Char { width: Some(8) },
            FortField::Skip,

            FortField::Integer { width: 4, zeros: None, base: IntBase::Decimal },
            FortField::Skip,
            FortField::Real { width: 7, precision: Some(4), fmt: RealFmt::F, scale: 0 },
            FortField::Skip,

            FortField::Integer { width: 4, zeros: None, base: IntBase::Decimal },
            FortField::Skip,
            FortField::Real { width: 7, precision: Some(4), fmt: RealFmt::F, scale: 0 },
            FortField::Skip,
        ];

        let expected = expected.repeat(3);

        assert_eq!(v, expected, "Parsing {s} failed");
        Ok(())
    }

    #[test]
    fn test_grouping_by_one() -> PResult<()> {
        let s = "(4i3,1x,a8,2x,2a4,1x,f13.8)";
        let ff = FortFormat::parse(&s)?;
        let grouped = ff.collapsed_version(1);
        let expected = vec![
            (4, FortField::Integer { width: 3, zeros: None, base: IntBase::Decimal }),
            (1, FortField::Skip),
            (1, FortField::Char { width: Some(8) }),
            (2, FortField::Skip),
            (2, FortField::Char { width: Some(4) }),
            (1, FortField::Skip),
            (1, FortField::Real { width: 13, precision: Some(8), fmt: RealFmt::F, scale: 0 })
        ];
        assert_eq!(grouped, expected);
        Ok(())
    }

    #[test]
    fn test_grouped_fmt_str() -> PResult<()> {
        let sorig = "(4i3,1x,a8,2x,2a4,1x,f13.8)";
        let ff = FortFormat::parse(&sorig)?;
        let stest = ff.fmt_string(1);
        assert_eq!(sorig, stest);
        Ok(())
    }

    #[test]
    fn test_grouped_fmt_str_with_scale() -> PResult<()> {
        let sorig = "(4i3,2x,42(1pe13.8))";
        let ff = FortFormat::parse(&sorig)?;
        let stest = ff.fmt_string(1);
        assert_eq!(sorig, stest);
        Ok(())
    }

    #[test]
    fn ggg_runlog_format() -> PResult<()> {
        let s = "(a1,a57,1x,2i4,f8.4,f8.3,f9.3,2f8.3,1x,f6.4,f8.3,f7.3,f7.2,3(1x,f5.4),2i9,1x,f14.11,i9,i3,1x,f5.3,i5,1x,a2,2(f6.1,f8.2,f5.1),f7.1,f7.4,f6.1,f6.0,f10.3,f7.0,f7.3)";
        FortFormat::parse(s)?;
        Ok(())
    }

    #[test]
    fn test_set_field() {
        let mut ff1 = FortFormat::parse("(i2)").unwrap();
        assert_eq!(ff1.get_field(0), Some(&FortField::Integer { width: 2, zeros: None, base: IntBase::Decimal }));

        ff1.set_field(0, FortField::Char { width: Some(9) }).unwrap();
        assert_eq!(ff1.get_field(0), Some(&FortField::Char { width: Some(9) }));

        let res = ff1.set_field(1, FortField::Skip);
        assert!(res.is_err());

        let mut ff2 = FortFormat::ListDirected;
        let res = ff2.set_field(0, FortField::Skip);
        assert!(res.is_err());
    }

    #[test]
    fn test_insert_field() {
        let mut ff = FortFormat::parse("(i2,f13.8)").unwrap();
        assert_eq!(ff.get_field(0), Some(&FortField::Integer { width: 2, zeros: None, base: IntBase::Decimal }));
        assert_eq!(ff.get_field(1), Some(&FortField::Real { width: 13, precision: Some(8), fmt: RealFmt::F, scale: 0 }));

        // Test insertion at the beginning
        ff.insert_field(0, FortField::Char { width: Some(9) }).unwrap();
        assert_eq!(ff.get_field(0), Some(&FortField::Char { width: Some(9) }));
        assert_eq!(ff.get_field(1), Some(&FortField::Integer { width: 2, zeros: None, base: IntBase::Decimal }));
        assert_eq!(ff.get_field(2), Some(&FortField::Real { width: 13, precision: Some(8), fmt: RealFmt::F, scale: 0 }));

        // Test adding to the end
        let mut ff = FortFormat::parse("(i2,f13.8)").unwrap();
        ff.insert_field(2, FortField::Char { width: Some(9) }).unwrap();
        assert_eq!(ff.get_field(0), Some(&FortField::Integer { width: 2, zeros: None, base: IntBase::Decimal }));
        assert_eq!(ff.get_field(1), Some(&FortField::Real { width: 13, precision: Some(8), fmt: RealFmt::F, scale: 0 }));
        assert_eq!(ff.get_field(2), Some(&FortField::Char { width: Some(9) }));

        // Test that adding past the end produces an error
        let mut ff = FortFormat::parse("(i2,f13.8)").unwrap();
        let res = ff.set_field(3, FortField::Skip);
        assert!(res.is_err());

        // Test that adding to a list directed format produces an error
        let mut ff = FortFormat::ListDirected;
        let res = ff.set_field(0, FortField::Skip);
        assert!(res.is_err());
    }
}