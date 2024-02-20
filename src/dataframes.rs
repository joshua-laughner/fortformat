//! Read Fortran-formatted data directly as a `DataFrame`.
use std::io::{BufReader, BufRead};

use polars::frame::row::Row;
use polars::prelude::{AnyValue, DataFrame, Field, Schema};

use crate::format_specs::FortValue;
use crate::{format_specs::FortFormat, serde_common::{DResult, DError}};


/// Read a table with a known Fortran format and column names into a dataframe
/// 
/// This requires that you have a buffered reader (`f`) position so that the next line read will be the 
/// first row of the data. Each line must be written in the Fortran format specified by `fmt` and will
/// be put into a dataframe with column names `colnames`.
/// 
/// This will return an error if:
/// - `fmt` has fewer non-positional fields than `colnames` has elements (`SError::FormatSpecTooShort`),
/// - reading any lines from `f` fails (`SError::TableReadError`),
/// - deserialization of a line fails (multiple possible variants), or
/// - any line does not have the same number of elements as `colnames` (`SError::TableLineEndedEarly`)
/// 
/// # Notes
/// If performance is crucial, take care to benchmark your use case for this function. It constructs the
/// DataFrame row by row, which Polars warns will be slow compared to column-by-column. This also necessarily
/// reads in the entirety of `f`, which may be a significant amount of memory. If you only need to use
/// one row of data at a time with arbitrary field names and value types, consider deserializing each row to a
/// [`HashMap`](std::collections::HashMap) of [`FortValue`]s instead.
pub fn read_to_dataframe<R: std::io::Read, S: AsRef<str>>(f: BufReader<R>, fmt: &FortFormat, colnames: &[S]) -> DResult<DataFrame> {
    if fmt.non_pos_len() < colnames.len() {
        return Err(DError::FormatSpecTooShort)
    }

    // For the dataframe column schema, we can infer the datatypes from the Fortran format
    // (though only a handful will be used, as we can't differentiate easily between different
    // bit sizes of numeric types). Any skips in the format will be returned as `None`, as they
    // have no corresponding column in the dataframe.
    let col_iter = fmt.iter_non_pos_fields().zip(colnames.iter())
        .filter_map(|(f, n)| {
            if let Some(dt) = f.polars_dtype() {
                Some(Field::new(n.as_ref(), dt))
            } else {
                None
            }
        });
    let schema = Schema::from_iter(col_iter);

    let mut rows = vec![];
    for (line_num, line) in f.lines().enumerate() {
        let line = line.map_err(|e| DError::TableReadError(e, line_num + 1))?;
        let values: Vec<FortValue> = crate::de::from_str(&line, fmt)?;
        let this_row: Vec<AnyValue> = values.into_iter().map(|v| v.into()).collect();
        if this_row.len() != colnames.len() {
            return Err(DError::TableLineEndedEarly { line_num: line_num + 1, ncol: colnames.len() })
        }
        rows.push(Row::new(this_row));
    }

    
    Ok(DataFrame::from_rows_and_schema(&rows, &schema).unwrap())
}

#[cfg(test)]
mod tests {
    use super::*;
    use polars::prelude::*;
    use stringreader::StringReader;

    #[test]
    fn test_to_dataframe() -> DResult<()> {
        let table = StringReader::new("Alpha T 1234  9.5\nBeta  F -678 -1.5");
        let table = BufReader::new(table);
        let ff = FortFormat::parse("(a5,1x,l1,1x,i4,1x,f4.1)")?;
        let df = read_to_dataframe(table, &ff, &["Name", "Flag", "ID", "Score"])?;

        // Can't use the df! macro because it makes the integer column an i32 instead of i64
        let ex_schema = Schema::from_iter([
            Field::new("Name", DataType::Utf8),
            Field::new("Flag", DataType::Boolean),
            Field::new("ID", DataType::Int64),
            Field::new("Score", DataType::Float64),
        ]);

        let ex_rows = vec![
            Row::new(vec![AnyValue::Utf8Owned("Alpha".into()), AnyValue::Boolean(true), AnyValue::Int64(1234), AnyValue::Float64(9.5)]),
            Row::new(vec![AnyValue::Utf8Owned("Beta".into()), AnyValue::Boolean(false), AnyValue::Int64(-678), AnyValue::Float64(-1.5)]),
        ];

        let expected = DataFrame::from_rows_and_schema(&ex_rows, &ex_schema).unwrap();
        assert_eq!(df.column("Name").unwrap(), expected.column("Name").unwrap());
        assert_eq!(df.column("Flag").unwrap(), expected.column("Flag").unwrap());
        assert_eq!(df.column("ID").unwrap(), expected.column("ID").unwrap());
        assert_eq!(df.column("Score").unwrap(), expected.column("Score").unwrap());
        Ok(())
    }

    #[test]
    fn test_line_short() -> DResult<()> {
        let table = StringReader::new("Alpha T 1234\nBeta  F -678 -1.5");
        let table = BufReader::new(table);
        let ff = FortFormat::parse("(a5,1x,l1,1x,i4,1x,f4.1)")?;
        let err = read_to_dataframe(table, &ff, &["Name", "Flag", "ID", "Score"]).unwrap_err();

        if let DError::TableLineEndedEarly { line_num, ncol } = err {
            assert_eq!(line_num, 1);
            assert_eq!(ncol, 4);
        } else {
            assert!(false, "Wrong error type");
        }
        Ok(())
    }
}