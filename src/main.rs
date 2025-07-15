#![allow(unused)]

mod asm;
mod cli;
mod error;
mod expr;

#[cfg(test)]
pub mod asm_tests_red;
mod from_bytes;
mod lines;

use std::{
    env,
    fmt::Display,
    fs::File,
    io::{stderr, stdout, BufWriter, Write},
    path::Path,
};

use asm::Assembler;
use cli::CliArgs;
use error::AsmError;

fn print_error<T: Display>(msg: T) {
    writeln!(stderr().lock(), "\x1B[1;31merror:\x1B[0m {}", msg);
}

fn main() {
    env_logger::builder()
        .filter_level(log::LevelFilter::Info)
        .format_target(false)
        .format_timestamp(None)
        .init();
    log::debug!("Logger initialized.");

    let args = CliArgs::new();

    match run(args) {
        Ok(_) => (),
        Err(e) => {
            print_error(e);
            std::process::exit(1);
        }
    }
}
fn run(args: CliArgs) -> Result<(), AsmError> {
    let mut asm = Assembler::new();

    match asm.parse(&args) {
        Err(errors) => {
            log::trace!("Parsing finished with errors");

            for err in &errors {
                print_error(err);
            }

            return Err("Parsing failed".into());
        }
        Ok(program) => {
            log::info!("Parsing finished OK.");
            let outfile: String = args.output.as_ref().map(|s| s.clone()).unwrap_or_else(|| {
                Path::new(&args.input)
                    .with_extension("bin")
                    .to_str()
                    .unwrap()
                    .to_string()
            });

            if args.is_stdin() {
                stdout().lock().write_all(program)?;
            } else {
                let mut file = File::create(outfile)?;
                let mut writer = BufWriter::new(file);
                writer.write_all(program)?;
                writer.flush()?;
            }
        }
    };

    Ok(())
}
