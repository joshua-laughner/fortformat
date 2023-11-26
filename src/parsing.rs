use pest::Parser;
use crate::fort_error::{FResult, FError};

#[derive(Parser)]
#[grammar = "values.pest"]
pub(crate) struct ValueParser;

pub(crate) fn parse_logical(s: &str) -> FResult<bool> {
    let val = get_expr(s, Rule::logical_expr, Rule::logical_value)?;
    match val.as_str() {
        ".true." | "t" => Ok(true),
        ".false." | "f" => Ok(false),
        _ => Err(FError::ParsingError { s: s.to_owned(), t: "logical", reason: "String is not a valid logical value".to_owned() })
    }
}

pub(crate) fn parse_integer(s: &str) -> FResult<i64> {
    let val = get_expr(s, Rule::integer_decimal_expr, Rule::integer_decimal_value)?;
    Ok(val.parse().unwrap())
}

pub(crate) fn parse_unsigned_integer(s: &str) -> FResult<u64> {
    let val = get_expr(s, Rule::unsigned_int_decimal_expr, Rule::unsigned_int_decimal_value)?;
    Ok(val.parse().unwrap())
}


/// Get the value expression out of a string, ignoring leading whitespace.
/// 
/// `s` is the string to extract the value from. `top_rule` is the "expr" rule from the Pest 
/// grammar that should match the whole string `s`, including whitespace. `inner_rule` is the
/// rule for the value only that we want to extract from the string. 
fn get_expr(s: &str, top_rule: Rule, inner_rule: Rule) -> FResult<String> {
    let expr = ValueParser::parse(top_rule, s)
        .map_err(|e| FError::from_pest(e, s.to_owned(), "logical"))?.next().unwrap();

    // Here, expr should be the whole expression - potentially with leading whitespace. This line
    // gets the sequence of inner tokens - usually whitespace and the value token.
    let mut stack: Vec<_> = expr.into_inner().rev().collect();

    while !stack.is_empty() {
        let pair = stack.pop().unwrap();
        match (pair.as_rule(), inner_rule) {
            // Ignore whitespace
            (Rule::WHITESPACE, _) => continue,

            // These rules should never be matched here - the expr ones should only be at the top of the
            // tree (and so we've already passed them). Other ones, like `sign`, are only components of the
            // value rules, and since we return before going inside the value rules, we shouldn't reach
            // these components either.
            (Rule::logical_expr, _) => unreachable!(),
            (Rule::integer_decimal_expr, _) => unreachable!(),
            (Rule::unsigned_int_decimal_expr, _) => unreachable!(),
            (Rule::sign, _) => unreachable!(),

            // These pairs of match arms give us an easy way to check if the expression is the type we expected and
            // return an error if not, which saves duplicating that code in the parsing functions.
            (Rule::logical_value, Rule::logical_value) => return Ok(pair.as_str().to_ascii_lowercase()),
            (Rule::logical_value, _) => return Err(FError::ParsingError { s: s.to_owned(), t: "logical", reason: "Did not find a valid logical expression".to_owned() }),

            (Rule::integer_decimal_value, Rule::integer_decimal_value) => return Ok(pair.as_str().to_owned()),
            (Rule::integer_decimal_value, _) => return Err(FError::ParsingError { s: s.to_owned(), t: "integer", reason: "Did not find a valid decimal integer expression".to_owned() }),

            (Rule::unsigned_int_decimal_value, Rule::unsigned_int_decimal_value) => return Ok(pair.as_str().to_owned()),
            (Rule::unsigned_int_decimal_value, _) => return Err(FError::ParsingError { s: s.to_owned(), t: "integer", reason: "Did not find a valid unsigned decimal integer expression".to_owned() }),
        }
    }

    Err(FError::EmptyExpression(s.to_owned()))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_logical_parsing() -> FResult<()> {
        // From the Oracle docs (https://docs.oracle.com/cd/E19957-01/805-4939/z40007437a2e/index.html),
        // both the standard logical values .TRUE. and .FALSE. should be valid, plus any string starting with
        // "T" or "F". Because fortran is case insensitive, we allow upper or lower case.
        assert_eq!(parse_logical(".true.")?, true, ".true. failed to parse");
        assert_eq!(parse_logical(".TRUE.")?, true, ".TRUE. failed to parse");
        assert_eq!(parse_logical(".false.")?, false, ".false. failed to parse");
        assert_eq!(parse_logical(".FALSE.")?, false, ".FALSE. failed to parse");
        assert_eq!(parse_logical("  .true.")?, true, ".true. with leading spaces failed to parse");
        assert_eq!(parse_logical("  .false.")?, false, ".false. with leading spaces failed to parse");
        assert_eq!(parse_logical("T")?, true, "'T' failed to parse");
        assert_eq!(parse_logical("F")?, false, "'F' failed to parse");
        assert_eq!(parse_logical(" T")?, true, "' T' failed to parse");
        assert_eq!(parse_logical(" F")?, false, "' F' failed to parse");
        assert_eq!(parse_logical("Tommy")?, true, "'Tommy' failed to parse");
        assert_eq!(parse_logical("Felicia")?, false, "'Felicia' failed to parse");
        assert_eq!(parse_logical(" Tommy")?, true, "' Tommy' failed to parse");
        assert_eq!(parse_logical(" Felicia")?, false, "' Felicia' failed to parse");
        assert_eq!(parse_logical("that")?, true, "'that' failed to parse");
        assert_eq!(parse_logical("fence")?, false, "'fence' failed to parse");
        assert_eq!(parse_logical(" that")?, true, "' that' failed to parse");
        assert_eq!(parse_logical(" fence")?, false, "' fence' failed to parse");


        assert!(parse_logical(".true").is_err(), "Parsing '.true' as a logical did not return an error");
        assert!(parse_logical(".false").is_err(), "Parsing '.false' as a logical did not return an error");
        assert!(parse_logical("bob").is_err(), "Parsing 'bob' as a logical did not return an error");
        Ok(())
    }

    #[test]
    fn test_decimal_integer_parsing() -> FResult<()> {
        assert_eq!(parse_integer("1")?, 1, "Parsing '1' failed");
        assert_eq!(parse_integer("-2")?, -2, "Parsing '-2' failed");
        assert_eq!(parse_integer("+42")?, 42, "Parsing '+42' failed");
        assert_eq!(parse_integer("-999999")?, -999999, "Parsing '-999999' failed");
        assert!(parse_integer("x").is_err(), "Parsing 'x' did not give an error");
        Ok(())
    }

    
}