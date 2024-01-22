#![allow(unused)]

mod asm;
mod cli;
mod error;
mod expr;

use std::{env, path::Path, fs::File, io::{BufWriter, Write}, fmt::Display};

use asm::{Assembler};
use cli::CliArgs;
use error::AsmError;

fn print_error<T: Display>(msg: T) {
    println!("\x1B[1;31merror:\x1B[0m {}", msg);
}

fn main() {
    let args = CliArgs::new();

    match run(args) {
        Ok(_) => (),
        Err(e) => {
            print_error(e);
            std::process::exit(1);
        },
    }
}
fn run(args: CliArgs) -> Result<(), AsmError> {

    let mut asm = Assembler::new();

    match asm.parse(&args.input) {
        Err(errors) => {

            for err in &errors {
                print_error(err);
            }

            return Err("Parsing failed".into());
        }
        Ok(program) => {
            let outfile: String = args.output.as_ref().map(|s| s.clone()).unwrap_or_else(|| {
                Path::new(&args.input)
                    .with_extension("bin")
                    .to_str()
                    .unwrap()
                    .to_string()
            });

            let mut file = File::create(outfile)?;
            let mut writer = BufWriter::new(file);
            writer.write_all(program)?;
            writer.flush()?;
        }
    };

    Ok(())
}
