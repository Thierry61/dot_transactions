use anyhow::{Context, Result};
use chrono::NaiveDate;
use clap::{Parser, Subcommand};
use std::{collections::BTreeMap, path::PathBuf};

mod parse_dot;
use parse_dot::parse_dot_file;

mod wallets;
use wallets::{analyze_wallet, sum_wallets};

mod check;
use check::check;

// Default number of fractional digits (adapted to bitcoin network)
const SAT_FRACTION_STR: &str = "8";
const SAT_FRACTION: u8 = 8;

/// Analyze wallets and transactions defined in a .dot file
#[derive(Parser, Debug)]
#[command(version, about, long_about = None)]
struct Cli {
    /// Input dot file
    r#in: PathBuf,

    /// Number of fractional digits
    #[arg(short, long, default_value(SAT_FRACTION_STR))]
    fraction: u8,

    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand, Debug)]
enum Commands {
    /// Compute wallets balances
    Sum,

    /// Analyze a specific wallet / port
    Analyze {
        /// Wallet name
        #[arg(short, long)]
        wallet: String,

        /// Port identifier or *
        #[arg(short, long, default_value("*"))]
        port: String,
    },

    /// Check transactions and wallets
    Check {
        /// Base url of bitcoin explorer API,
        /// for example: http://127.0.0.1/api/tx/
        #[arg(short, long)]
        url: String,
    },
}

/// Base unit
type Sat = i64;

/// Elements in transactions input or output list
/// List of (wallet name, global wallet port, amount) tuples
type ScriptElements<'a> = Vec<(&'a str, &'a str, Sat)>;

/// List of (local transaction port, amount) pairs
type PartialScriptElements<'a> = Vec<(&'a str, Sat)>;

/// Wallet addresses indexed by wallet port name
type Addresses<'a> = BTreeMap<&'a str, &'a str>;

/// Secondary name for explicitly merged wallet
/// There are 2 kinds of merged wallet:
/// - with an explicit link in dot file ("primary" -> "secondary")
/// - with an implicit link when 2 wallets have the same based name followed by "receive" and "change" suffix
///
/// This structure is used in the first case
/// The second case is not stored in the parsed content structure
/// but is computed eventually by the consumers of the structure
///
/// Note the conventions are:
/// - implicitly merged wallets are used for personal wallets
/// - explicitly merged wallets and regular wallets are for external wallets
#[derive(Debug, Default, PartialEq)]
struct Secondary<'a> {
    /// Secondary name
    name: &'a str,

    /// Merged name ("primary name" -> "secondary name")
    /// This field could have been omitted and reconstructed from primary/secondary names
    /// but this would need strings instead of &str and would create difficulties regarding
    /// borrow checker.
    /// With this field, everything has the same lifetime as the dot file content.
    merged_name: &'a str,
}

/// Wallet structure.
/// Note that the wallet name is not inside the structure but is the key of the structure in a BTreeMap.
#[derive(Debug, Default, PartialEq)]
struct Wallet<'a> {
    /// Addresses (list of (wallet port, address) pairs)
    addresses: Addresses<'a>,
}

/// Transaction structure
#[derive(Debug, Default, PartialEq)]
struct Transaction<'a> {
    /// Transaction ID
    id: &'a str,

    /// Transaction date (in the label part)
    date: NaiveDate,

    /// Transaction fees
    fees: Sat,

    /// Inputs (list of (wallet name, wallet port, amount) tuples)
    inputs: ScriptElements<'a>,

    /// Outputs (list of (wallet name, wallet port, amount) tuples)
    outputs: ScriptElements<'a>,
}

/// Result of parsing input dot file
#[derive(Debug, Default, PartialEq)]
struct ParsedContent<'a> {
    /// Wallet list indexed by wallet name
    wallets: BTreeMap<&'a str, Wallet<'a>>,

    /// Merge wallets indexed by primary name
    merged_wallets: BTreeMap<&'a str, Secondary<'a>>,

    /// Transaction list
    transactions: Vec<Transaction<'a>>,
}

fn main() -> Result<()> {
    let cli = Cli::parse();

    // Open dot file
    let content = std::fs::read_to_string(&cli.r#in)
        .with_context(|| format!("Could not read file `{}`", cli.r#in.display()))?;

    // Parse content
    let input = &content[..];
    let res = parse_dot_file(cli.fraction, input)?;

    // Select and execute subcommands
    match &cli.command {
        Commands::Sum => {
            // Compute sum of each wallet
            sum_wallets(cli.fraction, &res)?;
        }
        Commands::Analyze { wallet, port } => {
            // Analyze a specific port or all ports of a wallet
            analyze_wallet(cli.fraction, &res, wallet, port)?;
        }
        Commands::Check { url } => {
            // Check transactions and wallets
            check(cli.fraction, &res, url)?;
        }
    }

    Ok(())
}
