Analyze wallets and transactions defined in a [Graphviz dot](https://graphviz.org/) file.

# Usage

**dot-transactions [OPTIONS] \<IN> \<COMMAND>**

**<u>Commands:</u>**
```
  sum      Compute wallets balances
  analyze  Analyze a specific wallet / port
  check    Check transactions and wallets
  help     Print this message or the help of the given subcommand(s)
```
**<u>Arguments:</u>**
```
  <IN>  Input dot file
```
**<u>Options:</u>**
```
  -f, --fraction <FRACTION>  Number of fractional digits [default: 8]
  -h, --help                 Print help
  -V, --version              Print version
```

By default the program analyzes bitcoin transactions with 8 digits in fractional part of all amounts
(sat unit), but other currencies can be managed by providing an alternate value to `-f/--fraction` option,
typically 2 for cent unit.

Note that all computations are exact in integer domain (no rounding errors are possible).
More precisely 64 bits integers are used, which can store up to 19 digits amounts.
This is large enough to express:
- all bitcoin amounts in sats: 21 millions x 100 millions (16 digits)
- any reasonable fiat amounts in cents, including 1000 times the US debt: 1000 x 40 trillions x 100 (19 digits)

# sum command

List wallets and generate for each wallet:
- its final balance
- the maximum date of all transactions impacting the wallet

Wallets are grouped under 3 categories:
- personal wallets
- external merged wallets
- external regular wallets

This command doesn't have additional options.

# analyze command

List all addresses of a specific wallet and generate for each address:
- port identifier (in wallet label in dot file)
- total inflow into the address
- total outflow from the address
- final balance

This command has 2 additional options:
```
  -w, --wallet <WALLET>  Wallet name
  -p, --port <PORT>      Port identifier or * [default: *]
```

`-w/--wallet` indicates the name of the wallet to be analyzed and `-p/--port` (optional) limits
analysis to the single address specified by the port identifier.

# check command

Check that all transactions and wallets defined in the dot file are correct
(transactions, addresses and amounts exist in the bitcoin blockchain).

This command has an additional option:
```
-u, --url <URL>  Base url of bitcoin explorer API, for example: http://127.0.0.1/api/tx/
```

`-u, --url` specifies the url of the bitcoin explorer (preferably your own for better privacy).

TODO: describe the dot file syntax to define wallets and transactions.
