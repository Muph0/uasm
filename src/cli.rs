use clap::Parser;

#[derive(Parser, Debug)]
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