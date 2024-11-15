use clap::Parser;

#[cfg(debug_assertions)]
const VERSION: &str = "0.2.2 debug";

#[cfg(not(debug_assertions))]
const VERSION: &str = "0.2.2 release";


#[derive(Parser, Debug)]
#[command(author, version = Some(VERSION), about, long_about = None)]
pub struct CliArgs {
    pub input: String,

    #[arg(short, long)]
    pub output: Option<String>,
}

impl CliArgs {
    pub fn new() -> Self {
        Self::parse()
    }
}