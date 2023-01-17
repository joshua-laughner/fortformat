extern crate pest;
#[macro_use]
extern crate pest_derive;

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

#[derive(Debug, Clone, Copy)]
pub enum RealFmt {
    D,
    E,
    F,
    G
}

#[derive(Debug, Clone, Copy)]
pub enum IntBase {
    Decimal,
    Octal,
    Hexadecimal
}

#[derive(Debug, Clone, Copy)]
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

// pub fn parse_demo() {
//     let raw = std::fs::read_to_string("numbers.csv").expect("Could not read file");
//     let data = CSVParser::parse(Rule::file, &raw)
//         .expect("Unsuccessful parse")
//         .next()
//         .unwrap();

//     let mut field_sum: f64 = 0.0;
//     let mut record_count: u64 = 0;

//     for record in data.into_inner() {
//         match record.as_rule() {
//             Rule::record => {
//                 record_count += 1;
                
//                 for field in record.into_inner() {
//                     field_sum += field.as_str().parse::<f64>().unwrap();
//                 }
//             },
//             Rule::EOI => (),
//             _ => unreachable!(),
//         }
//     }

//     println!("Sum of fields: {field_sum}");
//     println!("Number of records: {record_count}");
// }

#[cfg(test)]
mod tests {
    use super::*;

    // #[test]
    // fn test_demo() {
    //     parse_demo();
    //     assert!(true);
    // }
}