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
    fs::{self, File},
    io::{stderr, stdout, BufRead, BufReader, BufWriter, Write},
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

    if args.arch_list {
        list_architectures(&args);
        return;
    }

    if args.input.is_none() {
        print_error("No input file specified. Use --help for usage.");
        std::process::exit(1);
    }

    match run(args) {
        Ok(_) => (),
        Err(e) => {
            print_error(e);
            std::process::exit(1);
        }
    }
}

fn list_architectures(args: &CliArgs) {
    let include_paths = args.effective_include_paths();
    if include_paths.is_empty() {
        log::warn!("No include paths specified. Use -I or set UNAS_INC.");
        return;
    }

    for dir in &include_paths {
        let entries = match fs::read_dir(dir) {
            Ok(e) => e,
            Err(_) => continue,
        };

        for entry in entries.flatten() {
            let path = entry.path();
            let ext = path.extension().and_then(|e| e.to_str());
            if !matches!(ext, Some("arch" | "s")) {
                continue;
            }

            let stem = match path.file_stem().and_then(|s| s.to_str()) {
                Some(s) => s.to_string(),
                None => continue,
            };

            // Check if file contains .architecture directive matching the file stem
            let file = match File::open(&path) {
                Ok(f) => f,
                Err(_) => continue,
            };

            let reader = BufReader::new(file);
            for line in reader.lines().flatten() {
                let trimmed = line.trim();
                if let Some(rest) = trimmed.strip_prefix(".architecture") {
                    let name = rest.split_whitespace().next().unwrap_or("");
                    if name == stem {
                        println!("{}", stem);
                        break;
                    }
                }
            }
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
            if program.is_empty() {
                log::warn!("Compilation produced empty output, no file written.");
                return Ok(());
            }

            log::info!("Parsing finished OK.");
            let input_file = args.input_file();
            let outfile: String = args.output.as_ref().map(|s| s.clone()).unwrap_or_else(|| {
                Path::new(input_file)
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
