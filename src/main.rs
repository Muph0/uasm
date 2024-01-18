#![allow(unused)]

mod cli;
mod asm;

use std::{env, path::Path};

use asm::Assembler;
use cli::CliArgs;

fn print_error(msg: &str) {
    println!("\x1B[1;31merror:\x1B[0m {}", msg);
}

fn main() {
    let args = CliArgs::new();

    let mut asm = Assembler::new();

    if let Err(err) = asm.accept_file(&args.input) {
        print_error("parsing failed.");
        std::process::exit(1);
        return;
    }

    let outfile: String = args.output.as_ref().map(|s| s.clone()).unwrap_or_else(||
        Path::new(&args.input).with_extension("bin").to_str().unwrap().to_string()
    );
    asm.write_output(&outfile);
}
