use crate::{ParsedContent, SAT_FRACTION, Sat, Transaction};

use anyhow::{Context, Result, bail};
use chrono::NaiveDate;
use std::{cmp::max, collections::BTreeMap};

// Format amount on 13 characters padded on left with blanks and on right with 0s
// It is expressed in sats with possibly:
// - an underscore to mark KSats unit
// - a dot to mark bitcoin unit
fn format_amount(fraction: u8, amount: Sat) -> String {
    let sign = if amount < 0 { '-' } else { ' ' };
    let amount = amount.abs();
    let sats = format!("{amount}");
    let len = sats.len();
    // Possibly add . separator
    let res = if len > fraction as usize {
        format!(
            "{}.{}",
            &sats[..len - fraction as usize],
            &sats[len - fraction as usize..]
        )
    } else {
        sats
    };
    // Possibly add _ at the 5th decimal of bitcoin amount (equivalent to 1€ in july 2025)
    const SEPA_POSITION: usize = 3;
    let res = if fraction == SAT_FRACTION && res.len() > SEPA_POSITION {
        let len = res.len();
        format!(
            "{}_{}",
            &res[..len - SEPA_POSITION],
            &res[len - SEPA_POSITION..]
        )
    } else {
        res
    };
    let res = format!("{sign}{res}");
    format!("{res:>13}")
}

#[test]
fn test_format_amount() {
    assert_eq!(format_amount(SAT_FRACTION, 9912345678), " 99.12345_678");
    assert_eq!(format_amount(SAT_FRACTION, 912345678), "  9.12345_678");
    assert_eq!(format_amount(SAT_FRACTION, 12345678), "    12345_678");
    assert_eq!(format_amount(SAT_FRACTION, 45678), "       45_678");
    assert_eq!(format_amount(SAT_FRACTION, 5678), "        5_678");
    assert_eq!(format_amount(SAT_FRACTION, 678), "          678");
    assert_eq!(format_amount(SAT_FRACTION, 8), "            8");
    assert_eq!(format_amount(SAT_FRACTION, -9912345678), "-99.12345_678");
    assert_eq!(format_amount(SAT_FRACTION, -912345678), " -9.12345_678");
    assert_eq!(format_amount(SAT_FRACTION, -12345678), "   -12345_678");
    assert_eq!(format_amount(SAT_FRACTION, -45678), "      -45_678");
    assert_eq!(format_amount(SAT_FRACTION, -5678), "       -5_678");
    assert_eq!(format_amount(SAT_FRACTION, -678), "         -678");
    assert_eq!(format_amount(SAT_FRACTION, -8), "           -8");
}

// Wallet balance structure
#[derive(Default)]
struct Balance {
    // Wallet balance
    bal: Sat,
    // Maximum date of all transactions impacting the wallet
    max_date: NaiveDate,
}

// Print balances
fn print_balances(fraction: u8, len: usize, header: &str, vec: &mut Vec<(&&str, &Balance)>) {
    if len != 0 {
        println!("{header}:");
        // Sort by max date
        vec.sort_by(|a, b| a.1.max_date.cmp(&b.1.max_date));
        for (n, bal) in vec {
            let amount = format_amount(fraction, bal.bal);
            println!("\t{n:<len$}: {amount} <= {}", bal.max_date);
        }
        println!();
    }
}

// Compute sum of each wallet
pub fn sum_wallets(fraction: u8, parsed_content: &ParsedContent) -> Result<()> {
    // Merged wallet definitions indexed by individual wallet
    // For implicit associations (same basename followed by "receive" and "change"):
    // - "ACCOUNT 1 receive" => "ACCOUNT 1"
    // - "ACCOUNT 1 change"  => "ACCOUNT 1"
    // For explicit associations (in dot file):
    // - "MasterXchange" => "MasterXchange -> Poloniex"
    // - "Poloniex"      => "MasterXchange -> Poloniex"
    let mut merged_wallets = BTreeMap::<&str, &str>::new();
    // Merged wallet balances
    let mut merged_balances = BTreeMap::<&str, Balance>::new();
    // Regular wallet (non merged) balances
    let mut regular_balances = BTreeMap::<&str, Balance>::new();

    // Compute explicit merged wallets
    for (&n, s) in &parsed_content.merged_wallets {
        let n2 = s.name;
        let p = s.merged_name;
        if merged_wallets.insert(n, p).is_some() {
            bail!("'{n}' wallet merged twice")
        }
        if merged_wallets.insert(n2, p).is_some() {
            bail!("'{n}' wallet merged twice")
        }
        if merged_balances.insert(p, Balance::default()).is_some() {
            bail!("'{p}' merged wallet defined twice")
        }
    }

    // Compute implicit merged wallets
    for &n in parsed_content.wallets.keys() {
        if n.ends_with(" change") || n.ends_with(" receive") {
            // Safety:
            // Preceding test implies there is a space in the wallet name
            let last_space = n.rfind(" ").unwrap();
            let p = &n[..last_space];
            if merged_wallets.insert(n, p).is_some() {
                bail!("{n} wallet merged twice")
            }
            // Merged name is normally used twice, so return value is ignored
            let _ = merged_balances.insert(p, Balance::default());
        } else {
            // Regular wallet if not merged
            if !merged_wallets.contains_key(n)
                && regular_balances.insert(n, Balance::default()).is_some()
            {
                bail!("{n} regular wallet defined twice")
            }
        }
    }

    // In presence of a batched input (implemented with a nul amount in parse_dot_file fn)
    // the output amounts of the same transaction must be subtracted from the external wallet
    // Note: to correctly manage this case the inputs must be selected before the outputs
    struct ExternalWallet<'a> {
        // External wallet name
        name: &'a str,
        // To select which BTreeMap to subtract from (merged_balances or regular_balances)
        is_merged: bool,
    }

    // Compute balances
    // Note that port name is ignored, which takes care of empty input port
    // in case of dust collection
    for t in &parsed_content.transactions {
        let mut external_wallet = None;
        for (n, amount, is_output) in t
            .inputs
            .iter()
            .map(|&(n, _, amount)| (n, amount, false))
            .chain(t.outputs.iter().map(|&(n, _, amount)| (n, amount, true)))
        {
            // Add or subtract amount depending on direction
            let amount = (if is_output { 1 } else { -1 }) * amount;
            if let Some(&p) = merged_wallets.get(n) {
                if let Some(old_bal) = merged_balances.get_mut(p) {
                    old_bal.bal += amount;
                    old_bal.max_date = max(old_bal.max_date, t.date);
                    if !is_output && amount == 0 {
                        // This a batched input so memorize wallet name
                        external_wallet = Some(ExternalWallet {
                            name: p,
                            is_merged: true,
                        });
                    }
                } else {
                    bail!("Undefined merged wallet '{p}'")
                }
            } else if let Some(old_bal) = regular_balances.get_mut(n) {
                old_bal.bal += amount;
                old_bal.max_date = max(old_bal.max_date, t.date);
                if !is_output && amount == 0 {
                    // This a batched input so memorize wallet name
                    external_wallet = Some(ExternalWallet {
                        name: n,
                        is_merged: false,
                    });
                }
            } else {
                bail!("Undefined regular wallet '{n}'")
            }
            if is_output && let Some(ref external_wallet) = external_wallet {
                // This transaction contains a batched input, so subtract the output amount
                let external_name = external_wallet.name;
                if external_wallet.is_merged {
                    if let Some(old_bal) = merged_balances.get_mut(external_name) {
                        old_bal.bal -= amount;
                        old_bal.max_date = max(old_bal.max_date, t.date);
                    } else {
                        bail!("Undefined merged external wallet '{external_name}'")
                    }
                } else if let Some(old_bal) = regular_balances.get_mut(external_name) {
                    old_bal.bal -= amount;
                    old_bal.max_date = max(old_bal.max_date, t.date);
                } else {
                    bail!("Undefined regular external wallet '{external_name}'")
                }
            }
        }
    }

    // Store wallet balances in mutable vectors so that they can be reordered by max_date
    let mut vec1: Vec<_> = merged_balances
        .iter()
        .filter(|(n, _)| !n.contains("->"))
        .collect();
    let mut vec2: Vec<_> = merged_balances
        .iter()
        .filter(|(n, _)| n.contains("->"))
        .collect();
    let mut vec3: Vec<_> = regular_balances.iter().collect();

    // Maximum wallet name length
    let len1 = vec1.iter().map(|(n, _)| n.len()).max().unwrap_or_default();
    let len2 = vec2.iter().map(|(n, _)| n.len()).max().unwrap_or_default();
    let len3 = vec3.iter().map(|(n, _)| n.len()).max().unwrap_or_default();
    let len = [len1, len2, len3].into_iter().max().unwrap_or_default();

    // Print all wallet balances
    print_balances(fraction, len, "Personal wallets", &mut vec1);
    let personal_balance: Sat = vec1.iter().map(|(_, bal)| bal.bal).sum();
    println!(
        "Total personal balance: {}",
        format_amount(fraction, personal_balance)
    );
    println!();
    print_balances(fraction, len, "External merged wallets", &mut vec2);
    print_balances(fraction, len, "External regular wallets", &mut vec3);

    Ok(())
}

// Analyze a specific port
fn analyze_port(
    fraction: u8,
    wallet: &str,
    port: &str,
    addr: &str,
    transactions: &[Transaction],
) -> Result<(Option<Sat>, Sat)> {
    let mut sum_inputs = 0;
    let mut sum_outputs = 0;
    // An empty port means that the whole wallet is emptied (dust collection)
    // When we encounter them we set current port amount to 0.
    // Additionally we check that the amount associated with the empty port
    // is equal to the final wallet balance.
    let mut dust_collection = None;
    for t in transactions {
        // Subtract output if there is a nul input amount in the same transaction
        // to manage batched input from external wallets
        let mut is_batched = false;
        for input in t.inputs.iter().filter_map(|&(w, p, amount)| {
            if w == wallet && p == port {
                Some(amount)
            } else {
                if w == wallet && p.is_empty() {
                    dust_collection = Some(amount);
                }
                None
            }
        }) {
            sum_inputs += input;
            if input == 0 {
                is_batched = true;
            }
        }
        for output in t.outputs.iter().filter_map(|&(w, p, amount)| {
            if w == wallet && p == port {
                Some(amount)
            } else if is_batched {
                Some(-amount)
            } else {
                None
            }
        }) {
            sum_outputs += output;
        }
    }
    // Manage dust collection (memorize returned balance before resetting it to 0)
    let balance = sum_outputs - sum_inputs;
    if dust_collection.is_some() {
        // Set balance to 0
        sum_inputs = sum_outputs;
    }
    // Note that a transaction input is an outflow from the address
    // and that a transaction output is an inflow into the address
    // hence apparent inversion for balance
    let balance_str = format_amount(fraction, sum_outputs - sum_inputs);
    let sum_inputs = format_amount(fraction, sum_inputs);
    let sum_outputs = format_amount(fraction, sum_outputs);
    println!("{addr:<42} {port:<4}: {sum_outputs} - {sum_inputs} = {balance_str}");
    Ok((dust_collection, balance))
}

// Analyze a specific port or all ports of a wallet
pub fn analyze_wallet(
    fraction: u8,
    parsed_content: &ParsedContent,
    wallet_name: &str,
    port_or_star: &str,
) -> Result<()> {
    let wallet = parsed_content
        .wallets
        .get(wallet_name)
        .context(format!("Wallet '{wallet_name}' not found"))?;

    if port_or_star == "*" {
        // Variables managing dust collection
        // (to check that the dust collected value is equal to the final wallet balance)
        let mut running_dust_collection = None;
        let mut wallet_balance = 0;
        for (i, (&port, &addr)) in wallet.addresses.iter().enumerate() {
            let (dust_collection, balance) = analyze_port(
                fraction,
                wallet_name,
                port,
                addr,
                &parsed_content.transactions,
            )?;
            wallet_balance += balance;
            if i == 0 {
                running_dust_collection = dust_collection;
            } else if running_dust_collection != dust_collection {
                bail!("Dust collected value should be same for all ports (port: {port})")
            }
        }
        // Check that the collected dust is equal to final wallet balance
        if let Some(dust_collection) = running_dust_collection {
            if dust_collection != wallet_balance {
                let dust_collection_str = format_amount(fraction, dust_collection);
                let wallet_balance_str = format_amount(fraction, wallet_balance);
                bail!(
                    "Dust collected value ({dust_collection_str}) should be equal to final wallet balance {wallet_balance_str}"
                )
            }
            // Reset wallet balance before displaying it
            wallet_balance = 0;
        }
        let wallet_balance_str = format_amount(fraction, wallet_balance);
        let dust_collection_str =
            format_amount(fraction, running_dust_collection.unwrap_or_default());
        println!("Wallet balance:  {wallet_balance_str}");
        println!("Dust collection: {dust_collection_str}");
    } else {
        let &addr = wallet.addresses.get(port_or_star).context(format!(
            "Port '{port_or_star}' not found in Wallet '{wallet_name}"
        ))?;
        // Ignore returned value because we cannot check dust collection in single port analysis
        let _ = analyze_port(
            fraction,
            wallet_name,
            port_or_star,
            addr,
            &parsed_content.transactions,
        )?;
    }

    Ok(())
}
