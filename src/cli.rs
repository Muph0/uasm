use std::path::PathBuf;

use clap::Parser;

#[cfg(debug_assertions)]
const VERSION: &str = "0.2.5 debug";

#[cfg(not(debug_assertions))]
const VERSION: &str = "0.2.5 release";

#[derive(Parser, Debug)]
#[command(author, version = Some(VERSION), about, long_about = None)]
pub struct CliArgs {
    /// Input file. For input from standard input, use "STDIN".
    pub input: Option<String>,

    #[arg(short, long)]
    pub output: Option<String>,

    /// Add a directory to the include search path. Can be specified multiple times.
    #[arg(short = 'I', long = "include")]
    pub include_paths: Vec<PathBuf>,

    /// Pre-load a named architecture definition (looks for <name>.arch or <name>.s in include paths).
    #[arg(long)]
    pub arch: Option<String>,

    /// List available architecture definitions found in include paths.
    #[arg(long)]
    pub arch_list: bool,
}

impl CliArgs {
    pub const STDIN_VAL: &str = "STDIN";
    pub fn new() -> Self {
        Self::parse()
    }
    pub fn is_stdin(&self) -> bool {
        self.input.as_deref() == Some(Self::STDIN_VAL)
    }
    pub fn input_file(&self) -> &str {
        self.input.as_deref().unwrap_or("")
    }

    /// Build the effective list of include paths: explicit -I paths + UNAS_INC env var.
    pub fn effective_include_paths(&self) -> Vec<PathBuf> {
        let mut paths = self.include_paths.clone();
        if let Ok(env_val) = std::env::var("UNAS_INC") {
            for p in std::env::split_paths(&env_val) {
                if !paths.contains(&p) {
                    paths.push(p);
                }
            }
        }
        paths
    }
}
