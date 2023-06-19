use std::fmt::Display;

use pest::{Parser, iterators::Pair, RuleType};

type Result<T> = std::result::Result<T, ParseError>;

#[derive(Debug)]
pub struct ParseError;

impl <R: RuleType> From<pest::error::Error<R>> for ParseError {
    fn from(_value: pest::error::Error<R>) -> Self {
        Self
    }
}

#[derive(Parser)]
#[grammar = "fort.pest"]
pub struct FortParser;

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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FortField {
    Char{width: Option<u32>},
    Logical{width: u32},
    Integer{width: u32, zeros: Option<u32>, base: IntBase},
    Real{width: u32, precision: Option<u32>, fmt: RealFmt, scale: i32},
    Skip
}

pub enum FortValue {
    Char(String),
    Integer(i64),
    Real(f64)
}

#[derive(Debug, Clone)]
pub struct FortFormat {
    pub fields: Vec<FortField>
}

impl FortFormat {
    pub fn parse(fmt_str: &str) -> Result<Self> {
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
                Rule::width => return Err(ParseError),
                Rule::prec => return Err(ParseError),
                Rule::signed => return Err(ParseError),

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
                    println!("curr_scale = {curr_scale}");
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
                        .ok_or_else(|| ParseError)?;
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

        Ok(Self { fields })
    }

    pub fn into_fields(self) -> Vec<FortField> {
        self.fields
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

fn consume_req_width_and_prec_from_pair(pair: Pair<Rule>, _kind: &str) -> Result<(u32, Option<u32>)> {
    let mut stack: Vec<_> = pair.into_inner().rev().collect();
    consume_req_width_and_prec(&mut stack, _kind)
}

fn consume_req_width_and_prec(stack: &mut Vec<Pair<Rule>>, _kind: &str) -> Result<(u32, Option<u32>)> {
    let (w_opt, p) = consume_width_and_prec(stack);
    let w = w_opt.ok_or_else(|| ParseError)?;
    Ok((w, p))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_char() -> Result<()> {
        let v = FortFormat::parse("(a)")?.into_fields();
        assert_eq!(v.len(), 1, "Parsing '(a)' did not return exactly 1 field");
        assert_eq!(v.last().unwrap(), &FortField::Char { width: None }, "Parsing '(a)' failed");

        let v = FortFormat::parse("(a16)")?.into_fields();
        assert_eq!(v.len(), 1, "Parsing '(a16)' did not return exactly 1 field");
        assert_eq!(v.last().unwrap(), &FortField::Char { width: Some(16) }, "Parsing '(a16)' failed");

        let e = FortFormat::parse("(a-16)");
        assert!(e.is_err(), "Parsing '(a-16)' (negative width) did not return an error");
        Ok(())
    }

    #[test]
    fn test_logical() -> Result<()> {
        let v = FortFormat::parse("(l1)")?.into_fields();
        assert_eq!(v.len(), 1, "Parsing '(l1)' did not return exactly 1 field");
        assert_eq!(v.last().unwrap(), &FortField::Logical { width: 1 }, "Parsing '(l1)' failed");

        let e = FortFormat::parse("(l)");
        assert!(e.is_err(), "Parsing '(l)' (no width) did not return an error");

        let e = FortFormat::parse("(l-1)");
        assert!(e.is_err(), "Parsing '(l-1)' (negative width) did not return an error");

        Ok(())
    }

    #[test]
    fn test_decimal() -> Result<()> {
        test_integer(IntBase::Decimal)
    }

    #[test]
    fn test_octal() -> Result<()> {
        test_integer(IntBase::Octal)
    }

    #[test]
    fn test_hex() -> Result<()> {
        test_integer(IntBase::Hexadecimal)
    }

    fn test_integer(base: IntBase) -> Result<()> {


        let v = FortFormat::parse(&format!("({base}8)"))?.into_fields();
        assert_eq!(v.len(), 1, "Parsing '({base}8)' did not return exactly 1 field");
        assert_eq!(v.last().unwrap(), &FortField::Integer { width: 8, zeros: None, base }, "Parsing '({base}8)' failed");

        let v = FortFormat::parse(&format!("({base}8.6)"))?.into_fields();
        assert_eq!(v.len(), 1, "Parsing '(i{base}.6)' did not return exactly 1 field");
        assert_eq!(v.last().unwrap(), &FortField::Integer { width: 8, zeros: Some(6), base }, "Parsing '({base}8.6)' failed");

        let e = FortFormat::parse(&format!("({base})"));
        assert!(e.is_err(), "Parsing '({base})' (no width) did not return an error");

        let e = FortFormat::parse(&format!("({base}8.)"));
        assert!(e.is_err(), "Parsing '({base}8.)' (missing precision width) did not return an error");

        Ok(())
    }

    #[test]
    fn test_float() -> Result<()> {
        test_real(RealFmt::F)
    }

    #[test]
    fn test_double() -> Result<()> {
        test_real(RealFmt::D)
    }

    #[test]
    fn test_exponential() -> Result<()> {
        test_real(RealFmt::E)
    }

    #[test]
    fn test_gfloat() -> Result<()> {
        test_real(RealFmt::G)
    }

    fn test_real(fmt: RealFmt) -> Result<()> {
        let v = FortFormat::parse(&format!("({fmt}8)"))?.into_fields();
        assert_eq!(v.len(), 1, "Parsing '({fmt}8)' did not return exactly 1 field");
        assert_eq!(v.last().unwrap(), &FortField::Real { width: 8, precision: None, fmt, scale: 0 }, "Parsing '({fmt}8)' failed");

        let v = FortFormat::parse(&format!("({fmt}8.6)"))?.into_fields();
        assert_eq!(v.len(), 1, "Parsing '({fmt}8.6)' did not return exactly 1 field");
        assert_eq!(v.last().unwrap(), &FortField::Real { width: 8, precision: Some(6), fmt, scale: 0 }, "Parsing '({fmt}8.6)' failed");

        let v = FortFormat::parse(&format!("(2p{fmt}8.6)"))?.into_fields();
        assert_eq!(v.len(), 1, "Parsing '(2p{fmt}8.6)' did not return exactly 1 field");
        assert_eq!(v.last().unwrap(), &FortField::Real { width: 8, precision: Some(6), fmt, scale: 2 }, "Parsing '(2p{fmt}8.6)' failed");

        let e = FortFormat::parse(&format!("({fmt})"));
        assert!(e.is_err(), "Parsing '({fmt})' (no width) did not return an error");

        let e = FortFormat::parse(&format!("({fmt}8.)"));
        assert!(e.is_err(), "Parsing '({fmt}8.)' (missing precision width) did not return an error");

        Ok(())
    }

    #[test]
    fn test_scales() -> Result<()> {
        let s = "(f7.2 2p f8.3 -3p f5.1 f6 0p f10.3)";
        let v = FortFormat::parse(s)?.into_fields();
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
    fn test_simple_repeats() -> Result<()> {
        let s = "(3i8 2f7.2)";
        let v = FortFormat::parse(s)?.into_fields();
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
    fn test_sequence() -> Result<()> {
        let s = "(a32 2x l4 i8 f10.3 e11.4 d12.5 g7.2)";
        let v = FortFormat::parse(s)?.into_fields();
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
    fn test_nested_one_level() -> Result<()> {
        let s = "(a32 2(1x f7.4))";
        let v = FortFormat::parse(s)?.into_fields();
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
    fn test_nested_two_level() -> Result<()> {
        let s = "(3(a8 1x 2(i4 1x f7.4 1x)))";
        let v = FortFormat::parse(s)?.into_fields();
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
}