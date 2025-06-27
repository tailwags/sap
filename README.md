# 🌿 Sap

_A small, sweet argument parser for Rust_

[![Crates.io](https://img.shields.io/crates/v/sap.svg)](https://crates.io/crates/sap)
[![Documentation](https://docs.rs/sap/badge.svg)](https://docs.rs/sap)
[![License](https://img.shields.io/crates/l/sap.svg)](LICENSE)

Sap is a minimal, zero-dependency Unix command-line argument parser for Rust. It provides full control over argument parsing with an iterator-based API that handles GNU-style options while maintaining simplicity and flexibility.

## ✨ Features

- **GNU-style option parsing**: Support for short (`-a`), long (`--verbose`), and combined options (`-abc`)
- **Flexible value handling**: Options with values via `--name=value` or separate arguments
- **POSIX compliance**: Handle `--` separator and `-` (stdin) arguments correctly
- **Zero dependencies**: Pure Rust implementation with no external crates
- **Iterator-based**: Works with any `Iterator<Item = Into<String>>` for maximum flexibility
- **Comprehensive error handling**: Descriptive error messages for invalid input

## 🚀 Quick Start

Add Sap to your `Cargo.toml`:

```toml
[dependencies]
sap = "0.0.4"
```

## 📖 Usage

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
            if let Some(filename) = parser.value() {
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
            if let Some(filename) = parser.value() {
                println!("Processing file: {}", filename);
            }
        }
        Argument::Value(val) => println!("Positional argument: {}", val),
        _ => {}
    }
}
```

## 🎯 Argument Types

Sap recognizes four types of arguments:

- **`Argument::Short(char)`** - Short options like `-v`, `-x`, and combined ones like `-abc`
- **`Argument::Long(&str)`** - Long options like `--verbose`, `--file`, including values like `--file=foo.txt`
- **`Argument::Value(Cow<str>)`** - Positional arguments and operands
- **`Argument::Stdio`** - The special `-` argument (stdin/stdout)

## 📚 Complete Example

Here's a more comprehensive example showing a typical CLI application:

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
                output_file = parser.value();
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
                eprintln!("Error: {}", unknown.into_error(parser.value()));
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

## 🤝 Acknowledgments

Special thanks to [Esther](https://github.com/esther-ff) who wrote the original parser design for this library <3

## License

This project is licensed under the
[Apache-2.0 License](http://www.apache.org/licenses/LICENSE-2.0). For more
information, please see the [LICENSE](LICENSE) file.
