use anyhow::Result;
use treesap::Parser;

#[derive(Debug, Parser)]
struct Args {
    #[arg(short, long)]
    verbose: bool,
}

fn main() -> Result<()> {
    let args = Args::parse()?;

    dbg!(args);

    Ok(())
}
