# 🌿 Sap

_A small, simple and sweet argument parser for Rust_

[![Crates.io](https://img.shields.io/crates/v/sap.svg)](https://crates.io/crates/sap)
[![Documentation](https://docs.rs/sap/badge.svg)](https://docs.rs/sap)
[![License](https://img.shields.io/crates/l/sap.svg)](LICENSE)

Sap is a minimal, zero-dependency Unix command-line argument parser for Rust. It
exposes an iterator-based API that handles GNU-style options and gives you full
control over how each argument is consumed.

## Features

- **GNU-style option parsing**: short (`-a`), long (`--verbose`), and combined
  options (`-abc`)
- **Value handling**: options with values via `--name=value` or as a separate
  following argument
- **POSIX compliance**: `--` separator and `-` (stdin) are handled correctly
- **Zero dependencies**: no external crates
- **Iterator-based**: works with any iterator yielding `ArgLike` items (`&str`,
  `String`, `OsStr`, etc.), so you can parse args from the environment, a `Vec`,
  or a test fixture without conversion
- **Error handling**: errors carry the offending argument and the parser
  transitions to a defined poisoned state

## Quick Start

Add Sap to your `Cargo.toml`:

```toml
[dependencies]
sap = "0.2.0"
```

## Usage

### Basic Example

```rust
use sap::{Parser, Argument};

// Parse from command line arguments
let mut parser = Parser::from_env().unwrap();

while let Some(arg) = parser.forward().unwrap() {
    match arg {
        Argument::Short('v') => println!("Verbose mode enabled"),
        Argument::Long("help") => println!("Help requested"),
        Argument::Long("file") => {
            if let Some(filename) = parser.value()? {
                println!("Processing file: {}", filename);
            }
        }
        Argument::Value(val) => println!("Positional argument: {}", val),
        Argument::Stdio => println!("Reading from stdin"),
    }
}
```

### Parsing Custom Arguments

```rust
use sap::{Parser, Argument};

// Parse from any iterator of string-like values
let mut parser = Parser::from_arbitrary(["myprogram", "-v", "--file=input.txt"]).unwrap();

while let Some(arg) = parser.forward().unwrap() {
    match arg {
        Argument::Short('v') => println!("Verbose mode enabled"),
        Argument::Long("file") => {
            if let Some(filename) = parser.value()? {
                println!("Processing file: {}", filename);
            }
        }
        Argument::Value(val) => println!("Positional argument: {}", val),
        _ => {}
    }
}
```

## Argument Types

Sap recognizes four types of arguments:

- **`Argument::Short(char)`** - Short options like `-v`, `-x`, and combined ones
  like `-abc`
- **`Argument::Long(&str)`** - Long options like `--verbose`, `--file`,
  including values like `--file=foo.txt`
- **`Argument::Value(Cow<str>)`** - Positional arguments and operands
- **`Argument::Stdio`** - The special `-` argument (stdin/stdout)

## Complete Example

Here's an example showing a typical CLI application:

```rust
use sap::{Parser, Argument, Result};

fn main() -> Result<()> {
    let mut parser = Parser::from_env()?;
    let mut verbose = false;
    let mut output_file = None;
    let mut input_files = Vec::new();

    while let Some(arg) = parser.forward()? {
        match arg {
            Argument::Short('v') | Argument::Long("verbose") => {
                verbose = true;
            }
            Argument::Short('h') | Argument::Long("help") => {
                print_help(parser.name());
                return Ok(());
            }
            Argument::Short('o') | Argument::Long("output") => {
                output_file = parser.value()?;
                if output_file.is_none() {
                    eprintln!("Error: --output requires a value");
                    std::process::exit(1);
                }
            }
            Argument::Value(file) => {
                input_files.push(file.into_owned());
            }
            Argument::Stdio => {
                input_files.push("-".to_string());
            }
            unknown => {
                eprintln!("Error: {}", unknown.unexpected());
                std::process::exit(1);
            }
        }
    }

    if verbose {
        println!("Verbose mode enabled");
        if let Some(ref output) = output_file {
            println!("Output file: {}", output);
        }
        println!("Input files: {:?}", input_files);
    }

    Ok(())
}

fn print_help(program_name: &str) {
    println!("Usage: {} [OPTIONS] [FILES...]", program_name);
    println!("Options:");
    println!("  -v, --verbose    Enable verbose output");
    println!("  -o, --output     Specify output file");
    println!("  -h, --help       Show this help message");
}
```

## Real-World Examples

[**puppyutils**](https://github.com/puppyutils/puppyutils) is a collection of
Unix utilities written in Rust that uses sap as its argument parser. Sap was
originally built for that project, so the source is a good reference for real
usage.

## treesap: derive-macro interface

[treesap](https://crates.io/crates/treesap) is a companion crate that lets you
declare your CLI arguments as a plain Rust struct instead of writing a manual
parsing loop. It is built on top of `sap` and exposes a `#[derive(Parser)]`
macro that generates a `parse()` method for you.

> **treesap is a work in progress.** Not all field types and attributes are
> implemented yet. See the [treesap README](treesap/README.md) for the current
> status.

```toml
[dependencies]
sap = "0.2.0"
treesap = "0.1.0"
```

```rust
use treesap::Parser;

#[derive(Debug, Parser)]
struct Args {
    verbose: bool,
    dry_run: bool,
}

fn main() -> sap::Result<()> {
    let args = Args::parse()?;

    if args.verbose {
        println!("verbose mode enabled");
    }

    if args.dry_run {
        println!("dry-run: no changes will be made");
    }

    Ok(())
}
```

## Acknowledgments

Special thanks to [Esther](https://github.com/esther-ff) who wrote the original
parser design for this library <3

## License

This project is licensed under the
[Apache-2.0 License](http://www.apache.org/licenses/LICENSE-2.0). For more
information, please see the [LICENSE](LICENSE) file.
