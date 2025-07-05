use clap::Parser;

#[cfg(debug_assertions)]
const VERSION: &str = "0.2.5 debug";

#[cfg(not(debug_assertions))]
const VERSION: &str = "0.2.5 release";

#[derive(Parser, Debug)]
#[command(author, version = Some(VERSION), about, long_about = None)]
pub struct CliArgs {
    /// Input file. For input from stdin, use "STDIN".
    pub input: String,

    #[arg(short, long)]
    pub output: Option<String>,
}

impl CliArgs {
    pub fn new() -> Self {
        Self::parse()
    }
}
