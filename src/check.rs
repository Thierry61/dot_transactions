use std::collections::BTreeMap;
use std::iter::zip;

use crate::{ParsedContent, SAT_FRACTION, Sat};

use anyhow::{Context, Result, bail};
use serde::Deserialize;
use serde::de;

// Sat values are defined in json response as f64 which have 15-16 significant decimal digits
fn convert_sat(fraction: u8, fvalue: f64) -> Sat {
    let integral = fvalue.floor();
    let decimal = ((fvalue - integral) * f64::powf(10f64, fraction as f64)).round() as Sat;
    let integral = integral as Sat;
    integral * Sat::pow(10, fraction as u32) + decimal
}

// Test that f64 is enough to represent the whole range of bitcoin values
#[test]
fn test_bitcoin_value() {
    let fraction = SAT_FRACTION;
    let one_sat: f64 = f64::powf(10.0, -(fraction as f64));

    // Test max bitcoin values
    // Cf. https://www.binance.com/en-JP/square/post/361745
    let max_f64: f64 = 20_999_999.97690_000;
    let max_sat: Sat = 20_999_999_97690_000 as Sat;
    assert_eq!(convert_sat(fraction, max_f64), max_sat);
    assert_eq!(convert_sat(fraction, max_f64 + one_sat), max_sat + 1);

    // Test min values
    let min_f64: f64 = 0.0;
    let min_sat: Sat = 0;
    assert_eq!(convert_sat(fraction, min_f64), min_sat);
    assert_eq!(convert_sat(fraction, min_f64 + one_sat), min_sat + 1);
}

/// For serde: deserialize a f64 into a Sat.
pub fn deserialize_sat<'de, D>(d: D) -> Result<Sat, D::Error>
where
    D: de::Deserializer<'de>,
{
    let fvalue = f64::deserialize(d)?;
    // Unsure how to pass fraction as parameter instead of using hard constant
    // but anyway the check command only works for bitcoin
    Ok(convert_sat(SAT_FRACTION, fvalue))
}

// Subset of transaction data
#[derive(Debug, Deserialize, PartialEq)]
struct Script {
    // To manage missing field in case of batched input or omni protocol
    #[serde(default)]
    address: String,
}
#[derive(Debug, Deserialize, PartialEq)]
struct Vin {
    // To manage non snake case attribute in json
    #[serde(rename = "scriptSig")]
    script_sig: Script,
    // To convert f64 to sat
    #[serde(deserialize_with = "deserialize_sat")]
    value: Sat,
}
#[derive(Debug, Deserialize, PartialEq)]
struct Vout {
    #[serde(deserialize_with = "deserialize_sat")]
    value: Sat,
    #[serde(rename = "scriptPubKey")]
    script_pub_key: Script,
}
#[derive(Debug, Deserialize, PartialEq)]
struct Fee {
    #[serde(deserialize_with = "deserialize_sat")]
    amount: Sat,
}
#[derive(Debug, Deserialize, PartialEq)]
struct TransactionDetails {
    vin: Vec<Vin>,
    vout: Vec<Vout>,
    fee: Fee,
}

fn get_transaction_details(url: &str, id: &str) -> Result<TransactionDetails> {
    let url = format!("{url}{id}");
    let details = reqwest::blocking::get(url)?.json::<TransactionDetails>()?;
    Ok(details)
}

#[test]
fn test_get_transaction_details() {
    // Random transaction from blockchain
    let details = get_transaction_details(
        "http://192.168.110.121:3002/api/tx/",
        "a3be98318db361c0c369aaa452782d561060867c00fc1fbd01ed61d218fdbfd2",
    )
    .unwrap();
    let expected_details = TransactionDetails {
        vin: vec![Vin {
            script_sig: Script {
                address: "bc1pqyhcucpcwddxqznedr4k50atejw275u370l4kc9c3u3dufewyzgsjn723g"
                    .to_string(),
            },
            value: 145687,
        }],
        vout: vec![
            Vout {
                value: 388,
                script_pub_key: Script {
                    address: "bc1prwaqqzdky253mwhx2lxnrh2eucpfu5n3ekt47cqppxym2xdjkqqqvk46dh"
                        .to_string(),
                },
            },
            Vout {
                value: 142933,
                script_pub_key: Script {
                    address: "bc1pee8gm5yzf3pxkvpdkgjpmc5p03rf7cxdzvqewz24jpn8jhx85ddql9sqqr"
                        .to_string(),
                },
            },
        ],
        fee: Fee { amount: 2366 },
    };
    assert_eq!(details, expected_details);
}

pub fn check(fraction: u8, parsed_content: &ParsedContent, url: &str) -> Result<()> {
    if fraction != SAT_FRACTION {
        bail!("Only bitcoin transactions can be checked")
    }
    // Wallet names + ports indexed by addresses
    // Initially: all defined addresses in dot file
    // At the end of program: only unused addresses
    let mut remaining_addresses: BTreeMap<_, _> = parsed_content
        .wallets
        .iter()
        .flat_map(|(&wallet_name, w)| {
            w.addresses
                .iter()
                .map(move |(&port, &addr)| (addr, (wallet_name, port)))
        })
        .collect();
    for t in &parsed_content.transactions {
        let id = t.id;
        if id.starts_with('(') {
            // Not a real transaction (like Wallet Of Satoshi internal stuff)
            continue;
        }
        let details = get_transaction_details(url, id)
            .context(format!("Error while getting details of transaction '{id}'"))?;
        // Count of inputs in blockchain
        let vin_len = details.vin.len();
        // Count of inputs in dot file
        let tin_len = t.inputs.len();
        // Test dust collection case (only one input with an empty port)
        // and batched inputs (only one input with a nul amount)
        let mut repeat_in = Vec::new();
        let (dust, batched, tin) =
            if tin_len == 1 && (t.inputs[0].1.is_empty() || t.inputs[0].2 == 0) {
                // In this case we repeat the first element so that the 2 zipped iterators have the same length
                let mut repeat_tmp = vec![t.inputs[0]; vin_len];
                // Move local vector to outer scope
                repeat_in.append(&mut repeat_tmp);
                (t.inputs[0].1.is_empty(), t.inputs[0].2 == 0, &repeat_in)
            } else {
                (false, false, &t.inputs)
            };
        if !dust && !batched && vin_len != tin_len {
            eprintln!(
                "Invalid input count for transaction '{id}': blockchain={vin_len}, dot file={tin_len}"
            );
        }
        // Input accumulator
        let mut sum_input = 0;
        for (vin, &(wallet_name, wallet_port, amount)) in zip(details.vin, tin) {
            sum_input += vin.value;
            let vin_address = vin.script_sig.address;
            if !dust && !batched {
                if let Some(wallet) = parsed_content.wallets.get(wallet_name) {
                    if vin.value != amount {
                        eprintln!(
                            "Invalid amount for transaction '{id}', wallet '{wallet_name} and port {wallet_port}: blockchain={}, dot file={amount}",
                            vin.value
                        );
                    }
                    if !wallet_port.is_empty() {
                        if let Some(&address) = wallet.addresses.get(wallet_port) {
                            if address == vin_address {
                                // Ignore non existent address because an address may be used several times
                                // and at the second usage it won't exist anymore in remaining_addresses
                                let _ = remaining_addresses.remove(&address);
                            } else {
                                eprintln!(
                                    "Invalid address for transaction '{id}' and wallet '{wallet_name}': blockchain={vin_address}, dot file={address}"
                                );
                            }
                        } else {
                            eprintln!(
                                "Missing address for transaction '{id}', address {vin_address}, wallet '{wallet_name}' and port={wallet_port}"
                            );
                        }
                    } else {
                        eprintln!(
                            "Empty wallet port for transaction '{id}', address {vin_address}, wallet '{wallet_name}'"
                        );
                    }
                } else {
                    eprintln!("Missing wallet '{wallet_name}' referenced by transaction '{id}'")
                }
            }
        }
        // Count of outputs in blockchain
        let vout_len = details.vout.len();
        // Count of outputs in dot file
        let tout_len = t.outputs.len();
        // Test batched transaction
        let mut repeat_out = Vec::new();
        let tout = if batched {
            // In this case we repeat the first element so that the 2 zipped iterators have the same length
            let mut repeat_tmp = vec![t.outputs[0]; vout_len];
            // Move local vector to outer scope
            repeat_out.append(&mut repeat_tmp);
            &repeat_out
        } else {
            &t.outputs
        };
        if !batched && vout_len != tout_len {
            eprintln!(
                "Invalid input count for transaction '{id}': blockchain={vout_len}, dot file={tout_len}"
            );
        }
        // Output accumulator
        let mut sum_output = 0;
        let mut our_output = 0;
        for (vout, &(wallet_name, wallet_port, amount)) in zip(details.vout, tout) {
            sum_output += vout.value;
            let vout_address = vout.script_pub_key.address;
            if let Some(wallet) = parsed_content.wallets.get(wallet_name) {
                if !wallet_port.is_empty() {
                    if let Some(&address) = wallet.addresses.get(wallet_port) {
                        if address == vout_address {
                            if vout.value == amount {
                                our_output += vout.value;
                            } else {
                                eprintln!(
                                    "Invalid amount for transaction '{id}', wallet '{wallet_name} and port {wallet_port}: blockchain={}, dot file={amount}",
                                    vout.value
                                );
                            }
                            // Ignore non existent address because an address may be used several times
                            // and at the second usage it won't exist anymore in remaining_addresses
                            let _ = remaining_addresses.remove(&address);
                        } else {
                            // For batched input there are many outputs that are not ours
                            if !batched {
                                eprintln!(
                                    "Invalid address for transaction '{id}' and wallet '{wallet_name}': blockchain={vout_address}, dot file={address}"
                                );
                            }
                        }
                    } else {
                        eprintln!(
                            "Missing address for transaction '{id}', address {vout_address}, wallet '{wallet_name}' and port={wallet_port}"
                        );
                    }
                } else {
                    eprintln!(
                        "Empty wallet port for transaction '{id}', address {vout_address}, wallet '{wallet_name}'"
                    );
                }
            } else {
                eprintln!("Missing wallet '{wallet_name}' referenced by transaction '{id}'")
            }
        }
        if batched {
            if our_output == 0 {
                eprintln!("Our output is missing in batched transaction '{id}'")
            }
        } else if our_output != sum_output {
            eprintln!(
                "Invalid output sum for non batched transaction '{id}': total output: {sum_output}, our output: {our_output}"
            )
        }
        let computed_fees = sum_input - sum_output;
        let fees = details.fee.amount;
        if computed_fees != fees {
            // Very unlikely error (it would mean that blockchain explorer is broken)
            eprintln!(
                "Invalid fees in blockchain transaction '{id}': computed={computed_fees}, real fees={fees}"
            );
        }
        if !batched {
            let dot_file_fees = t.fees;
            if dot_file_fees != fees {
                eprintln!(
                    "Invalid fees in dot file transaction '{id}': dot file={dot_file_fees}, real fees={fees}"
                );
            }
        }
    }
    for (address, (wallet_name, port)) in remaining_addresses {
        if !address.starts_with('(') {
            eprintln!("Unused address {address} defined as \"{wallet_name}\":{port}");
        }
    }
    println!("Analysis completed.");
    Ok(())
}
