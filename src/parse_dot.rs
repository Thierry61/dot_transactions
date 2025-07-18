#[cfg(test)]
use crate::SAT_FRACTION;

use crate::{Addresses, ParsedContent, PartialScriptElements, Sat, Secondary, Transaction, Wallet};

use chrono::NaiveDate;
use nom::{
    IResult, Parser,
    branch::alt,
    bytes::{complete::take_until, tag},
    character::{
        complete::{alphanumeric0, alphanumeric1, line_ending, multispace0, multispace1},
        digit1, one_of,
    },
    combinator::{cond, map_res, opt, peek},
    multi::many1,
    sequence::delimited,
};
use nom_language::error::{VerboseError, VerboseErrorKind};
use std::collections::BTreeMap;

// Generate a nom error with a specific message and input sliced on 25 chars
fn generate_error<'a>(input: &'a str, msg: &'static str) -> VerboseError<&'a str> {
    let len = usize::min(25, input.len());
    let kind = VerboseErrorKind::Context(msg);
    let truncated_input = &input[..len];
    VerboseError {
        errors: vec![(truncated_input, kind)],
    }
}

// Parse date in either DD-MM-YYYY or YYYY-MM-DD format
fn parse_date(input: &str) -> IResult<&str, NaiveDate, VerboseError<&str>> {
    let orig_input = input;
    let (input, day) = map_res(digit1(), str::parse::<u32>).parse_complete(input)?;
    let (input, _) = tag("-").parse_complete(input)?;
    let (input, month) = map_res(digit1(), str::parse::<u32>).parse_complete(input)?;
    let (input, _) = tag("-").parse_complete(input)?;
    let (input, year) = map_res(digit1(), str::parse::<u32>).parse_complete(input)?;

    let (year, day) = if day > 31 {
        if year > 31 {
            let err = generate_error(orig_input, "Invalid day value in date");
            return Err(nom::Err::Error(err));
        };
        // day is greater than 31 but not year => swap day and year
        (day as i32, year)
    } else {
        (year as i32, day)
    };
    let date = NaiveDate::from_ymd_opt(year, month, day);
    match date {
        Some(date) => Ok((input, date)),
        None => {
            let err = generate_error(orig_input, "Invalid date");
            Err(nom::Err::Error(err))
        }
    }
}

#[test]
fn test_parse_date() {
    assert_eq!(
        parse_date("25-04-2025|"),
        Ok(("|", NaiveDate::from_ymd_opt(2025, 4, 25).unwrap()))
    );
    assert_eq!(
        parse_date("2025-04-25|"),
        Ok(("|", NaiveDate::from_ymd_opt(2025, 4, 25).unwrap()))
    );
    assert_eq!(
        parse_date("26-04-2025}"),
        Ok(("}", NaiveDate::from_ymd_opt(2025, 4, 26).unwrap()))
    );
    assert_eq!(
        parse_date("27-04-2025"),
        Ok(("", NaiveDate::from_ymd_opt(2025, 4, 27).unwrap()))
    );
    assert_eq!(
        parse_date("29-02-2024"),
        Ok(("", NaiveDate::from_ymd_opt(2024, 2, 29).unwrap()))
    );
    assert_eq!(
        parse_date("x"),
        Err(nom::Err::Error(VerboseError {
            errors: vec![("x", VerboseErrorKind::Nom(nom::error::ErrorKind::Digit))]
        }))
    );
    assert_eq!(
        parse_date("29x"),
        Err(nom::Err::Error(VerboseError {
            errors: vec![("x", VerboseErrorKind::Nom(nom::error::ErrorKind::Tag))]
        }))
    );
    assert_eq!(
        parse_date("32-04-2025"),
        Err(nom::Err::Error(VerboseError {
            errors: vec![(
                "32-04-2025",
                VerboseErrorKind::Context("Invalid day value in date")
            )]
        }))
    );
    assert_eq!(
        parse_date("01-13-2025"),
        Err(nom::Err::Error(VerboseError {
            errors: vec![("01-13-2025", VerboseErrorKind::Context("Invalid date"))]
        }))
    );
    assert_eq!(
        parse_date("29-02-2025"),
        Err(nom::Err::Error(VerboseError {
            errors: vec![("29-02-2025", VerboseErrorKind::Context("Invalid date"))]
        }))
    );
}

// Parse amount with mandatory dot separator between integral and fractional parts
// (to be sure there is no confusion between bitcoins or sats)
fn parse_amount(fraction: u8, input: &str) -> IResult<&str, Sat, VerboseError<&str>> {
    let (input, integral_part) = map_res(digit1(), str::parse::<Sat>).parse_complete(input)?;
    let (input, _) = tag(".").parse_complete(input)?;
    let (input, fractional_part) = map_res(digit1(), |out: &str| {
        // Right pad fractional part with 0's
        let padded = format!("{out:0<fraction$}", fraction = fraction as usize);
        padded.parse::<Sat>()
    })
    .parse_complete(input)?;
    // Combine integral part converted to sats and fractional part
    let amount = integral_part * Sat::pow(10, fraction as u32) + fractional_part;
    Ok((input, amount))
}

// Generate an amount parser (closure capturing fraction parameter)
fn gen_parse_amount(fraction: u8) -> impl FnMut(&str) -> IResult<&str, Sat, VerboseError<&str>> {
    move |input: &str| parse_amount(fraction, input)
}

#[test]
fn test_parse_amount() {
    assert_eq!(parse_amount(SAT_FRACTION, "0.1|"), Ok(("|", 1000_0000)));
    assert_eq!(parse_amount(2, "0.1|"), Ok(("|", 10)));
    assert_eq!(
        gen_parse_amount(SAT_FRACTION)("1.2|"),
        Ok(("|", 1_2000_0000))
    );
    assert_eq!(parse_amount(SAT_FRACTION, "2.03}"), Ok(("}", 2_0300_0000)));
    assert_eq!(
        parse_amount(SAT_FRACTION, "31.0041"),
        Ok(("", 31_0041_0000))
    );
    assert_eq!(
        parse_amount(SAT_FRACTION, "42.000052"),
        Ok(("", 42_0000_5200))
    );
    assert_eq!(
        gen_parse_amount(SAT_FRACTION)("53.00000063"),
        Ok(("", 53_0000_0063))
    );
}

// Parse header in label. It can be either:
// - a simple date
// - a date + fees (wrapped in { ... | ... } structure)
fn parse_header(
    fraction: u8,
    input: &str,
) -> IResult<&str, (NaiveDate, Option<Sat>), VerboseError<&str>> {
    let opt_char = input.chars().next();
    let with_fees = if let Some(char) = opt_char {
        char == '{'
    } else {
        let err = generate_error(input, "Empty input");
        return Err(nom::Err::Error(err));
    };
    let (input, _) = cond(with_fees, tag("{")).parse_complete(input)?;
    let (input, date) = parse_date(input)?;
    // Optional fees
    let (input, fees) = cond(
        with_fees,
        delimited(tag("|"), gen_parse_amount(fraction), tag("}")),
    )
    .parse_complete(input)?;
    Ok((input, (date, fees)))
}

#[test]
fn test_parse_header() {
    assert_eq!(
        parse_header(SAT_FRACTION, "25-04-2025|"),
        Ok(("|", (NaiveDate::from_ymd_opt(2025, 4, 25).unwrap(), None)))
    );
    assert_eq!(
        parse_header(SAT_FRACTION, "{25-04-2025|0.00001}|"),
        Ok((
            "|",
            (NaiveDate::from_ymd_opt(2025, 4, 25).unwrap(), Some(1000))
        ))
    );
}

// Parse a row cell in a transaction label.
// A row has 2 cells wrapped in { ... | ... } structure:
// - an input cell which can be empty or a (port, amount) pair
// - an output cell which can be the same or a fees amount
#[derive(Debug, PartialEq)]
enum RowCell<'a> {
    // Empty cell
    Empty,
    // Regular cell (transaction port + amount)
    PortAndAmount((&'a str, Sat)),
    // Fees cell (only possible in output cell)
    Fees(Sat),
}
fn parse_cell(fraction: u8, input: &str) -> IResult<&str, RowCell, VerboseError<&str>> {
    let orig_input = input;
    // Input cell begins with '{', output cell begins with '|'
    let (input, first_char) = one_of("|{").parse_complete(input)?;
    let is_input = first_char == '{';
    let opt_char = input.chars().next();
    let (input, row_part) = match opt_char {
        Some('&') => {
            // Empty cell is a sequence of &nbsp;
            let (input, _) = many1(tag("&nbsp;")).parse(input)?;
            (input, RowCell::Empty)
        }
        Some('<') => {
            // Regular cell (port + amount in < ... > ... format)
            let (input, port) =
                delimited(tag("<"), alphanumeric1, tag(">")).parse_complete(input)?;
            let (input, _) = multispace1(input)?;
            // Test if there is really an amount
            // It could be something like (batched)&nbsp; when withdrawing from an exchange
            // in which case a 0 amount is returned for batched input management
            let is_amount = peek(digit1::<&str, VerboseError<&str>>())
                .parse_complete(input)
                .is_ok();
            if is_amount {
                let (input, amount) = parse_amount(fraction, input)?;
                (input, RowCell::PortAndAmount((port, amount)))
            } else {
                let (input, _) = take_until("|").parse_complete(input)?;
                (input, RowCell::PortAndAmount((port, 0)))
            }
        }
        Some(_) if !is_input => {
            // Fees cell (only possible in output cell)
            let (input, fees) = parse_amount(fraction, input)?;
            (input, RowCell::Fees(fees))
        }
        _ => {
            let err = generate_error(orig_input, "Empty or unexpected input");
            return Err(nom::Err::Error(err));
        }
    };
    // Input cell ends with '|' but we don't consume it so that it can be tested in output cell
    // Output cell ends with '}' and we consume it
    let (input, _) = cond(!is_input, tag("}")).parse_complete(input)?;
    Ok((input, row_part))
}

#[test]
fn test_parse_cell() {
    assert_eq!(
        parse_cell(SAT_FRACTION, "{<in0> 1.2|"),
        Ok(("|", RowCell::PortAndAmount(("in0", 1_2000_0000))))
    );
    assert_eq!(
        parse_cell(SAT_FRACTION, "{&nbsp;|"),
        Ok(("|", RowCell::Empty))
    );
    assert_eq!(
        parse_cell(
            SAT_FRACTION,
            "{&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;|"
        ),
        Ok(("|", RowCell::Empty))
    );
    assert_eq!(
        parse_cell(SAT_FRACTION, "|<out1> 1.00002}"),
        Ok(("", RowCell::PortAndAmount(("out1", 1_0000_2000))))
    );
    assert_eq!(
        parse_cell(SAT_FRACTION, "|0.00002003}"),
        Ok(("", RowCell::Fees(2003)))
    );
    assert_eq!(
        parse_cell(SAT_FRACTION, "{0.00002003|345678901234567"),
        Err(nom::Err::Error(VerboseError {
            errors: vec![(
                "{0.00002003|3456789012345",
                VerboseErrorKind::Context("Empty or unexpected input")
            )]
        }))
    );
}

// Parse label string and generate (date, fee, local inputs, local outputs) tuple
// (local means that the str part references a transaction port like in0, out0, ...)
fn parse_transaction_label(
    fraction: u8,
    input: &str,
) -> IResult<&str, (NaiveDate, Sat, PartialScriptElements, PartialScriptElements), VerboseError<&str>>
{
    let orig_input = input;
    let mut inputs = Vec::new();
    let mut outputs = Vec::new();
    let mut mandatory_fees = true;
    let (input, _) = tag("\"").parse_complete(input)?;
    let (mut running_input, (date, mut global_fees)) = parse_header(fraction, input)?;
    loop {
        let input = running_input;
        let opt_char = input.chars().next();
        match opt_char {
            Some('"') => break,
            Some('|') => {
                // Parse input cell
                let (input, _) = tag("|").parse_complete(input)?;
                let (input, row_cell) = parse_cell(fraction, input)?;
                // No need to test all cases:
                // - Empty cells do nothing
                // - Input cells cannot contain fees
                if let RowCell::PortAndAmount(port_and_amount) = row_cell {
                    inputs.push(port_and_amount);
                    if port_and_amount.1 == 0 {
                        // Fees unneeded with batched inputs
                        mandatory_fees = false;
                    }
                }
                // Parse output cell
                let cell_input = input;
                let (input, row_cell) = parse_cell(fraction, input)?;
                match row_cell {
                    RowCell::PortAndAmount(port_and_amount) => outputs.push(port_and_amount),
                    RowCell::Fees(fees) => {
                        if global_fees.is_some() {
                            let err = generate_error(cell_input, "Fees defined twice");
                            return Err(nom::Err::Error(err));
                        }
                        global_fees = Some(fees);
                    }
                    RowCell::Empty => {}
                }
                running_input = input;
            }
            Some(_) => {
                let err = generate_error(input, "Unexpected char in label");
                return Err(nom::Err::Error(err));
            }
            None => {
                let err = generate_error(input, "Unexpected end of label");
                return Err(nom::Err::Error(err));
            }
        }
    }
    let (input, _) = tag("\"").parse(running_input)?;
    let fees = if let Some(fees) = global_fees {
        fees
    } else {
        if mandatory_fees {
            let err = generate_error(orig_input, "Fees not defined");
            return Err(nom::Err::Error(err));
        }
        0
    };
    if mandatory_fees {
        // Test that inputs = outputs + fees
        let sum_inputs: Sat = inputs.iter().map(|el| el.1).sum();
        let sum_outputs: Sat = outputs.iter().map(|el| el.1).sum();
        if sum_inputs != sum_outputs + fees {
            let err = generate_error(
                orig_input,
                "Sum of inputs is different from sum of outputs + fees",
            );
            return Err(nom::Err::Error(err));
        }
    }
    Ok((input, (date, fees, inputs, outputs)))
}

#[test]
fn test_parse_transaction_label() {
    let input1 = "\"19-05-2019|{<in0> 0.0101|<out0> 0.02}|{<in1> 0.01|<out1> 0.03}|{<in2> 0.02|<out2> 0.05}|{<in3> 0.03|&nbsp;}|{<in4> 0.03|0.0001}\"";
    let input2 = "\"{19-05-2019|0.0001}|{<in0> 0.0101|<out0> 0.02}|{<in1> 0.01|<out1> 0.03}|{<in2> 0.02|<out2> 0.05}|{<in3> 0.03|&nbsp;}|{<in4> 0.03|&nbsp;}\"";
    let common_res = (
        NaiveDate::from_ymd_opt(2019, 5, 19).unwrap(),
        1_0000,
        vec![
            ("in0", 101_0000),
            ("in1", 100_0000),
            ("in2", 200_0000),
            ("in3", 300_0000),
            ("in4", 300_0000),
        ],
        vec![("out0", 200_0000), ("out1", 300_0000), ("out2", 500_0000)],
    );
    assert_eq!(
        parse_transaction_label(SAT_FRACTION, input1),
        Ok(("", common_res.clone()))
    );
    assert_eq!(
        parse_transaction_label(SAT_FRACTION, input2),
        Ok(("", common_res))
    );
    assert_eq!(
        parse_transaction_label(
            SAT_FRACTION,
            "\"{19-05-2019|0.0001}|{<in0> 0.01|<out0> 0.02}|{<in1> 0.01|0.0001}\""
        ),
        Err(nom::Err::Error(VerboseError {
            errors: vec![(
                "|0.0001}\"",
                VerboseErrorKind::Context("Fees defined twice")
            )]
        }))
    );
    assert_eq!(
        parse_transaction_label(SAT_FRACTION, "\"19-05-2019|{<in0> 0.01|<out0> 0.01}\""),
        Err(nom::Err::Error(VerboseError {
            errors: vec![(
                "\"19-05-2019|{<in0> 0.01|<",
                VerboseErrorKind::Context("Fees not defined")
            )]
        }))
    );
}

// Parse keyword assignment
fn parse_assign_keyword<'a>(
    input: &'a str,
    keyword: &str,
) -> IResult<&'a str, (), VerboseError<&'a str>> {
    let (input, _) = multispace0(input)?;
    let (input, _) = tag(keyword).parse_complete(input)?;
    let (input, _) = multispace0(input)?;
    let (input, _) = tag("=").parse_complete(input)?;
    let (input, _) = multispace0(input)?;
    Ok((input, ()))
}

// Parse transaction content
// It consist of:
// - [ tooltip = ... href = ... label = ... ] structure,
// - a list of links (one by line)
// - one empty line
fn parse_transaction<'a>(
    fraction: u8,
    input: &'a str,
    transaction_name: &str,
) -> IResult<&'a str, Transaction<'a>, VerboseError<&'a str>> {
    let (input, _) = tag("[").parse_complete(input)?;

    // Get tooltip (but ignore it)
    let (input, _) = parse_assign_keyword(input, "tooltip")?;
    let (input, _) = delimited(tag("\""), take_until("\""), tag("\"")).parse_complete(input)?;
    let (input, _) = multispace0(input)?;

    // Get href and extract transaction id
    let (input, _) = parse_assign_keyword(input, "href")?;
    let (input, href) = delimited(tag("\""), take_until("\""), tag("\"")).parse_complete(input)?;
    let (input, _) = multispace0(input)?;
    let id = if let Some(id) = href.rfind('/') {
        // Id is everything after the last / separator
        &href[id + 1..]
    } else {
        // No / separator => Id if the whole href value
        href
    };

    // Parse label to get transaction details
    let (input, _) = parse_assign_keyword(input, "label")?;
    let (input, (date, fees, inputs, outputs)) = parse_transaction_label(fraction, input)?;
    let (input, _) = multispace0(input)?;
    let (input, _) = tag("];").parse_complete(input)?;
    let (input, _) = multispace0(input)?;

    // Amounts indexed by transaction port
    let amount_by_inputs: BTreeMap<_, _> = inputs.into_iter().collect();
    let amount_by_outputs: BTreeMap<_, _> = outputs.into_iter().collect();

    let mut inputs = vec![];
    let mut outputs = vec![];
    let mut running_input = input;

    // Parse transaction lines
    loop {
        let mut is_input = None;
        let mut global_wallet = None;
        let mut global_amount = None;
        let mut global_port = None;

        // Source
        let orig_input = running_input;
        let (input, wallet) =
            delimited(tag("\""), take_until("\""), tag("\"")).parse_complete(running_input)?;
        // Port is optional. No port means the whole wallet is emptied (dust collection)
        // The aim is to reduce the number of arrows in the dot diagram for such a transaction
        // (only one arrow from the wallet instead of one arrow for each port)
        let (input, port) =
            delimited(opt(tag(":")), alphanumeric0, tag(" -> ")).parse_complete(input)?;
        if wallet == transaction_name {
            // Get amount from referenced port
            if let Some(&amount) = amount_by_outputs.get(port) {
                global_amount = Some(amount);
            } else {
                let err = generate_error(orig_input, "Referenced port doesn't exist");
                return Err(nom::Err::Error(err));
            }
        } else {
            // Memorize direction, wallet name and wallet port
            is_input = Some(true);
            global_wallet = Some(wallet);
            global_port = Some(port);
        }

        // Destination
        let orig_input = input;
        let (input, wallet) =
            delimited(tag("\""), take_until("\""), tag("\"")).parse_complete(input)?;
        let (input, port) =
            delimited(tag(":"), alphanumeric1, line_ending).parse_complete(input)?;
        if wallet == transaction_name {
            if global_amount.is_some() {
                let err = generate_error(orig_input, "Two local ports in the line");
                return Err(nom::Err::Error(err));
            }
            // Get amount from referenced port
            if let Some(&amount) = amount_by_inputs.get(port) {
                global_amount = Some(amount);
            } else {
                let err = generate_error(orig_input, "Referenced port doesn't exist");
                return Err(nom::Err::Error(err));
            }
        } else {
            if is_input.is_some() {
                let err = generate_error(orig_input, "Global port used twice in the line");
                return Err(nom::Err::Error(err));
            }
            // Memorize direction, wallet name and wallet port
            is_input = Some(false);
            global_wallet = Some(wallet);
            global_port = Some(port);
        }
        // Safety:
        // - is_input is defined otherwise we would get "Two local ports in the line" error
        // - global_amount is defined otherwise we would get "Global port used twice in the line" error
        // - global_wallet and global port are defined together with is_input
        if is_input.unwrap() {
            inputs.push((
                global_wallet.unwrap(),
                global_port.unwrap(),
                global_amount.unwrap(),
            ));
        } else {
            outputs.push((
                global_wallet.unwrap(),
                global_port.unwrap(),
                global_amount.unwrap(),
            ));
        }

        // Needed to test end of line, both '\n' and '\r\n'
        let is_end_of_line = peek(line_ending::<&str, VerboseError<&str>>)
            .parse_complete(input)
            .is_ok();

        // Lines are terminated by the end of file or by an empty line or by final closing brace
        if input.is_empty() || is_end_of_line || input.starts_with('}') {
            let transaction = Transaction {
                id,
                date,
                fees,
                inputs,
                outputs,
            };
            return Ok((input, transaction));
        }

        // Consume spaces at the beginning of the line
        let (input, _) = multispace0(input)?;
        running_input = input;
    }
}

#[test]
fn test_parse_transaction() {
    // Random transaction from blockchain
    let name = "08-07-2025 21:14:03";
    let input = r#"[
        tooltip = "Licence for videos"
        href = "http://192.168.110.121:3002/tx/a3be98318db361c0c369aaa452782d561060867c00fc1fbd01ed61d218fdbfd2"
        label = "08-07-2025|{<in0> 0.00145687|<out0> 0.00000388}|{&nbsp;|<out1> 0.00142933}|{&nbsp;|0.00002366}"
    ];
    "Blockchain mobile":r0 -> "08-07-2025 21:14:03":in0
    "08-07-2025 21:14:03":out0 -> "Blockchain mobile":d0
    "08-07-2025 21:14:03":out1 -> "Blockchain mobile":r1
"#;
    let output = Transaction {
        id: "a3be98318db361c0c369aaa452782d561060867c00fc1fbd01ed61d218fdbfd2",
        date: NaiveDate::from_ymd_opt(2025, 7, 8).unwrap(),
        fees: 2366,
        inputs: vec![("Blockchain mobile", "r0", 145687)],
        outputs: vec![
            ("Blockchain mobile", "d0", 388),
            ("Blockchain mobile", "r1", 142933),
        ],
    };
    assert_eq!(
        parse_transaction(SAT_FRACTION, input, name),
        Ok(("", output))
    );
}

// Like delimited parser but include delimiters in the result
fn my_delimited<'a>(
    begin: &'a str,
    end: &'a str,
    input: &'a str,
) -> IResult<&'a str, &'a str, VerboseError<&'a str>> {
    let (final_input, (res1, res2, res3)) =
        (tag(begin), take_until(end), tag(end)).parse_complete(input)?;
    Ok((final_input, &input[..res1.len() + res2.len() + res3.len()]))
}

// Generate my delimited parser (closure capturing begin and end parameters)
fn gen_my_delimited<'a>(
    begin: &'a str,
    end: &'a str,
) -> impl FnMut(&'a str) -> IResult<&'a str, &'a str, VerboseError<&'a str>> {
    move |input: &str| my_delimited(begin, end, input)
}

// Parse label string and generate an address vector
fn parse_wallet_label(input: &str) -> IResult<&str, Addresses, VerboseError<&str>> {
    // Wallet name in label is ignored (though is the one displayed in dot diagram)
    let (input, _) = tag("\"").parse_complete(input)?;
    let (input, _) = take_until("|")(input)?;
    let mut addresses = BTreeMap::new();
    let mut running_input = input;
    loop {
        let input = running_input;
        let opt_char = input.chars().next();
        match opt_char {
            Some('"') => {
                let (input, _) = tag("\"").parse_complete(input)?;
                return Ok((input, addresses));
            }
            Some('|') => {
                // Port + address in < ... > ... format
                let (input, port) =
                    delimited(tag("|<"), alphanumeric1, tag(">")).parse_complete(input)?;
                let (input, _) = multispace1(input)?;
                // Real address or any expression between parenthesis, like: (batched transactions)
                let (input, address) =
                    alt((alphanumeric1, gen_my_delimited("(", ")"))).parse_complete(input)?;
                if addresses.insert(port, address).is_some() {
                    let err = generate_error(input, "duplicate port in wallet label");
                    return Err(nom::Err::Error(err));
                }
                running_input = input;
            }
            Some(_) => {
                let err = generate_error(input, "Unexpected char in wallet label");
                return Err(nom::Err::Error(err));
            }
            None => {
                let err = generate_error(input, "Unexpected end of wallet label");
                return Err(nom::Err::Error(err));
            }
        }
    }
}

// Parse wallet definition
// It consist of [ color = ... fontcolor = ... tooltip = ... label = ... ] structure
fn parse_wallet(input: &str) -> IResult<&str, Wallet, VerboseError<&str>> {
    let (input, _) = tag("[").parse_complete(input)?;

    // Get color, fontcolor and tooltip parameters (but ignore them)
    let (input, _) = parse_assign_keyword(input, "color")?;
    let (input, _) = digit1().parse_complete(input)?;
    let (input, _) = multispace0(input)?;
    let (input, _) = parse_assign_keyword(input, "fontcolor")?;
    let (input, _) = digit1().parse_complete(input)?;
    let (input, _) = multispace0(input)?;
    let (input, _) = parse_assign_keyword(input, "tooltip")?;
    let (input, _) = delimited(tag("\""), take_until("\""), tag("\"")).parse_complete(input)?;
    let (input, _) = multispace0(input)?;

    // Parse label
    let (input, _) = parse_assign_keyword(input, "label")?;
    let (input, addresses) = parse_wallet_label(input)?;
    let wallet = Wallet { addresses };

    let (input, _) = multispace0(input)?;
    let (input, _) = tag("];").parse_complete(input)?;
    let (input, _) = multispace0(input)?;

    Ok((input, wallet))
}

#[test]
fn test_parse_wallet() {
    let input = r#"[
        color = 1
        fontcolor = 2
        tooltip = "Blockchain.info mobile wallet"
        label = "Blockchain mobile (sup. info)|<r0> bc1pqyhcucpcwddxqznedr4k50atejw275u370l4kc9c3u3dufewyzgsjn723g|<r1> bc1pee8gm5yzf3pxkvpdkgjpmc5p03rf7cxdzvqewz24jpn8jhx85ddql9sqqr|<d0> bc1prwaqqzdky253mwhx2lxnrh2eucpfu5n3ekt47cqppxym2xdjkqqqvk46dh"
    ];
"#;
    let output = Wallet {
        addresses: BTreeMap::from([
            (
                "r0",
                "bc1pqyhcucpcwddxqznedr4k50atejw275u370l4kc9c3u3dufewyzgsjn723g",
            ),
            (
                "r1",
                "bc1pee8gm5yzf3pxkvpdkgjpmc5p03rf7cxdzvqewz24jpn8jhx85ddql9sqqr",
            ),
            (
                "d0",
                "bc1prwaqqzdky253mwhx2lxnrh2eucpfu5n3ekt47cqppxym2xdjkqqqvk46dh",
            ),
        ]),
    };
    assert_eq!(parse_wallet(input), Ok(("", output)));
}

// There are 8 kinds of dot elements.
// 3 of them are interpreted:
// - Transactions: string beginning with a date followed by [
// - Wallets: string not beginning with a date followed by [
// - Merged wallets: string followed by ->
// 5 of them are ignored:
// - Comments: #
// - beginning of graph: digraph g {
// - end of graph: }
// - graphviz parameter: identifier = "string"
// - graphviz block: identifier [ ... ]
#[derive(Debug, PartialEq)]
enum DotElement<'a> {
    Transaction(Transaction<'a>),
    Wallet((&'a str, Wallet<'a>)),
    Merged((&'a str, Secondary<'a>)),
    EndOfInput,
}

// Parse a single interpreted dot element
fn parse_next_element(fraction: u8, input: &str) -> IResult<&str, DotElement, VerboseError<&str>> {
    let mut running_input = input;
    loop {
        let (input, _) = multispace0(running_input)?;
        let opt_char = input.chars().next();
        match opt_char {
            // End of file
            None => return Ok((input, DotElement::EndOfInput)),
            // End of digraph block
            Some('}') => {
                running_input = &input[1..];
            }
            // Ignored comment
            Some('#') => {
                let (input, _) = take_until("\n")(input)?;
                running_input = input;
            }
            // Interpreted dot element
            Some('"') => {
                let merged_name = input;
                let (input, name) =
                    delimited(tag("\""), take_until("\""), tag("\"")).parse_complete(input)?;
                let (_, is_transaction) =
                    opt((digit1(), tag("-"), digit1(), tag("-"), digit1())).parse_complete(name)?;
                let (input, _) = multispace0(input)?;
                // Is this a transaction name ?
                if is_transaction.is_some() {
                    let (input, transaction) = parse_transaction(fraction, input, name)?;
                    return Ok((input, DotElement::Transaction(transaction)));
                }
                // Not a transaction, so this a wallet name
                let (input, is_merged_wallet) = opt(tag("->")).parse_complete(input)?;
                // Is this a merge wallet ?
                if is_merged_wallet.is_some() {
                    let (input, _) = multispace0(input)?;
                    // Get the wallet alias
                    let (input, name2) =
                        delimited(tag("\""), take_until("\""), tag("\"")).parse_complete(input)?;
                    // Ignore the block content (including its tooltip)
                    let (input, _) = take_until("];")(input)?;
                    let input = &input[2..];
                    // Get merged name reference: "primary name" -> "secondary name"
                    let merged_name = &merged_name[..1 + name.len() + 1 + 4 + 1 + name2.len() + 1];
                    // Return secondary name + merged name
                    let secondary = Secondary {
                        name: name2,
                        merged_name,
                    };
                    return Ok((input, DotElement::Merged((name, secondary))));
                }
                // Not a merged wallet, so this is a wallet definition to parse
                let (input, wallet) = parse_wallet(input)?;
                return Ok((input, DotElement::Wallet((name, wallet))));
            }
            // Ignored dot element
            Some(_) => {
                let (input, identifier) = alphanumeric1(input)?;
                // digraf declaration
                if identifier == "digraph" {
                    let (input, _) = take_until("{")(input)?;
                    running_input = &input[1..];
                    continue;
                }
                let (input, _) = multispace0(input)?;
                let opt_char2 = input.chars().next();
                match opt_char2 {
                    // Single line parameter
                    Some('=') => {
                        let (input, _) = take_until("\n")(input)?;
                        running_input = input;
                    }
                    // Block, possibly on several lines
                    Some('[') => {
                        let (input, _) = take_until("];")(input)?;
                        running_input = &input[2..];
                    }
                    Some(_) => {
                        let err = generate_error(input, "Unexpected dot element");
                        return Err(nom::Err::Error(err));
                    }
                    None => {
                        let err = generate_error(input, "Truncated dot element");
                        return Err(nom::Err::Error(err));
                    }
                }
            }
        }
    }
}

#[test]
fn test_parse_next_element() {
    let input = r#"
digraph g {
    fontname="Helvetica,Arial,sans-serif"
    graph [
        # Replace default "g" tooltip. Cannot be empty.
        tooltip = "BTC transactions history"
        rankdir = "LR"
        ranksep = "1.5"
    ];
    node [
        fontname="Consolas,monospace"
        colorscheme = paired10
        fontsize = "7.5"
        shape = "record"
        # So that url are displayed in a new tab
        target = "_blank"
    ];
    edge [
        colorscheme = paired10
        penwidth = 0.5
        arrowsize = 0.7
    ];
    # Comment
}
"#;
    assert_eq!(
        parse_next_element(SAT_FRACTION, input),
        Ok(("", DotElement::EndOfInput))
    );
}

// Parse whole dot file
pub fn parse_dot_file(fraction: u8, input: &str) -> anyhow::Result<ParsedContent> {
    let mut running_input = input;
    let mut res = ParsedContent::default();

    loop {
        let opt_el = parse_next_element(fraction, running_input);
        match opt_el {
            Err(err) => {
                // Conversion from VerboseError to anyhow error
                // but we need to build a new string to prevent
                // "borrowed data escapes outside of function" error
                let err = err.to_string();
                anyhow::bail!(err);
            }
            Ok((input, el)) => {
                match el {
                    DotElement::Transaction(transaction) => {
                        res.transactions.push(transaction);
                    }
                    DotElement::Wallet((name, wallet)) => {
                        if res.wallets.insert(name, wallet).is_some() {
                            anyhow::bail!("Duplicate wallet definition {name}");
                        }
                    }
                    DotElement::Merged((name, secondary)) => {
                        if res.merged_wallets.insert(name, secondary).is_some() {
                            anyhow::bail!("Wallet {name} merge twice");
                        }
                    }
                    DotElement::EndOfInput => break,
                }
                running_input = input;
            }
        }
    }
    Ok(res)
}

#[test]
fn test_parse_dot_file() {
    let input = r#""Blockchain mobile" [
        color = 1
        fontcolor = 2
        tooltip = "Blockchain.info mobile wallet"
        label = "Blockchain mobile (sup. info)|<r0> bc1pqyhcucpcwddxqznedr4k50atejw275u370l4kc9c3u3dufewyzgsjn723g|<r1> bc1pee8gm5yzf3pxkvpdkgjpmc5p03rf7cxdzvqewz24jpn8jhx85ddql9sqqr|<d0> bc1prwaqqzdky253mwhx2lxnrh2eucpfu5n3ekt47cqppxym2xdjkqqqvk46dh"
    ];

    "MasterXchange" -> "Poloniex" [
        color = 5
        tooltip = "Move from MasterXchange to Poloniex"
    ];

    "08-07-2025 21:14:03" [
        tooltip = "Licence for videos"
        href = "http://192.168.110.121:3002/tx/a3be98318db361c0c369aaa452782d561060867c00fc1fbd01ed61d218fdbfd2"
        label = "08-07-2025|{<in0> 0.00145687|<out0> 0.00000388}|{&nbsp;|<out1> 0.00142933}|{&nbsp;|0.00002366}"
    ];
    "Blockchain mobile":r0 -> "08-07-2025 21:14:03":in0
    "08-07-2025 21:14:03":out0 -> "Blockchain mobile":d0
    "08-07-2025 21:14:03":out1 -> "Blockchain mobile":r1
}
"#;
    let wallet = Wallet {
        addresses: BTreeMap::from([
            (
                "r0",
                "bc1pqyhcucpcwddxqznedr4k50atejw275u370l4kc9c3u3dufewyzgsjn723g",
            ),
            (
                "r1",
                "bc1pee8gm5yzf3pxkvpdkgjpmc5p03rf7cxdzvqewz24jpn8jhx85ddql9sqqr",
            ),
            (
                "d0",
                "bc1prwaqqzdky253mwhx2lxnrh2eucpfu5n3ekt47cqppxym2xdjkqqqvk46dh",
            ),
        ]),
    };
    let transaction = Transaction {
        id: "a3be98318db361c0c369aaa452782d561060867c00fc1fbd01ed61d218fdbfd2",
        date: NaiveDate::from_ymd_opt(2025, 7, 8).unwrap(),
        fees: 2366,
        inputs: vec![("Blockchain mobile", "r0", 145687)],
        outputs: vec![
            ("Blockchain mobile", "d0", 388),
            ("Blockchain mobile", "r1", 142933),
        ],
    };

    let secondary = Secondary {
        name: "Poloniex",
        merged_name: r#""MasterXchange" -> "Poloniex""#,
    };
    let output = ParsedContent {
        wallets: BTreeMap::from([("Blockchain mobile", wallet)]),
        merged_wallets: BTreeMap::from([("MasterXchange", secondary)]),
        transactions: vec![transaction],
    };

    // unwrap needed because anyhow::Error doesn't implement PartialEq
    assert_eq!(parse_dot_file(SAT_FRACTION, input).unwrap(), output);
}
