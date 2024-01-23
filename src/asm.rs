use bitvec::prelude::*;
use log::*;
use std::collections::HashMap;
use std::fmt::{Display, Write};
use std::fs::File;
use std::io::{BufRead, BufReader, BufWriter, Error, Write as OtherWrite};
use std::num::ParseIntError;
use std::ops::Range;
use std::path::PathBuf;
use std::string::ParseError;
use std::{default, fs};

use crate::error::{AsmError, LocError};
use crate::print_error;

pub type AsmResult<T> = Result<T, AsmError>;

const CHAR_QUOTE: char = '"';

const TOK_MACRO_MARK: &str = ".";
const TOK_ARCH: &str = "architecture";
const TOK_USE: &str = "use";
const TOK_END: &str = "end";
const TOK_INCLUDE: &str = "include";
const TOK_BYTES: &str = "db";
const TOK_MNEM: &str = "mnem";
const TOK_SYMBOL: &str = "symbol";
const TOK_RELATIVE: &str = "R";
const TOK_LABEL_MARK: &str = ":";
const TOK_RANGE_SEP: &str = ":";
const TOK_SYMVAL_MARK: &str = ":";
const TOK_SYMTYPE_MARK: &str = ":";
const TOK_MINUS: &str = "-";
const TOK_REWRITE: &str = "->";
const TOK_PARAM_MARK: &str = "$";
const TOK_SIZE_OPEN: &str = "[";
const TOK_SIZE_CLOSE: &str = "]";
const TOK_LIMIT_OPEN: &str = "(";
const TOK_LIMIT_CLOSE: &str = ")";

const SYMBOL_INT: SymbolTypeId = SymbolTypeId(0);
const SYMBOL_LABEL: SymbolTypeId = SymbolTypeId(1);

struct Arch {
    name: String,
    symbol_table: Vec<SymbolType>,
    instructions: Vec<Instr>,
}
impl Arch {
    fn new(name: &str) -> Self {
        Self {
            name: name.to_string(),
            symbol_table: vec![
                SymbolType {
                    name: "int".to_string(),
                    size: None,
                    variants: Default::default(),
                },
                SymbolType {
                    name: "label".to_string(),
                    size: None,
                    variants: Default::default(),
                },
            ],
            instructions: Vec::new(),
        }
    }
    fn add_symbol(&mut self, symbol: SymbolType) {
        self.symbol_table.push(symbol)
    }
    fn get_symbol(&self, id: SymbolTypeId) -> &SymbolType {
        &self.symbol_table[id.0]
    }
    fn get_symbol_mut(&mut self, id: SymbolTypeId) -> &mut SymbolType {
        &mut self.symbol_table[id.0]
    }
    fn get_symbol_by_name(&self, name: &str) -> Option<(&SymbolType, SymbolTypeId)> {
        let id = self.symbol_table.iter().position(|s| s.name == name);
        id.map(|id| (&self.symbol_table[id], SymbolTypeId(id)))
    }
    fn get_ir(&self, id: InstrId) -> &Instr {
        &self.instructions[id.0]
    }
    fn get_instr_by_name(&self, name: &str) -> Option<(&Instr, InstrId)> {
        let id = self.instructions.iter().position(|s| s.mnemonic == name);
        id.map(|id| (&self.instructions[id], InstrId(id)))
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
struct ArchId(usize);

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
struct SymbolTypeId(usize);
impl SymbolTypeId {
    pub fn deref(self, arch: &Arch) -> &SymbolType {
        arch.get_symbol(self)
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
struct InstrId(usize);

#[derive(Debug)]
struct SymbolType {
    name: String,
    size: Option<usize>,
    variants: HashMap<String, usize>,
}
impl SymbolType {
    fn get_variant(&self, token: &str) -> Option<&usize> {
        self.variants.get(token)
    }
}
struct Instr {
    mnemonic: String,
    params: Vec<Param>,
    encoding: Vec<Encode>,
}
struct SizedInt<T> {
    value: T,
    size: usize,
}
impl<T> SizedInt<T> {
    fn new(size: usize, value: T) -> Self {
        Self { value, size }
    }
}

#[derive(Debug, PartialEq, Eq)]
enum Param {
    Symbol {
        name: String,
        symbol_id: SymbolTypeId,
        limit: Option<Range<isize>>,
    },
    Token {
        value: String,
    },
}
impl Param {
    pub fn name(&self) -> Option<&str> {
        match self {
            Param::Symbol { name, .. } => Some(name),
            Param::Token { .. } => None,
        }
    }
    pub fn size(&self, symbol_table: &Vec<SymbolType>) -> Option<usize> {
        match self {
            Param::Symbol {
                symbol_id: symbol, ..
            } => symbol_table[symbol.0].size,
            Param::Token { value, .. } => None,
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
enum Encode {
    Bits {
        value: usize,
        size: usize,
    },
    Param {
        id: usize,
        part: Range<usize>,
        rel: bool,
    },
}

/// An unresolved label to be resolved later
struct LabelRequest {
    /// Where to write
    offset_bits: usize,
    /// Which part of the label to write here.
    part: Range<usize>,
    label: String,
}

#[derive(Debug, Clone)]
enum ParsedParam {
    Value(isize),
    UnresolvedLabel { label: String },
}

pub struct Assembler {
    architectures: Vec<Arch>,
    current_arch: usize,
    block: CodeBlock,
    arch_names: HashMap<String, ArchId>,

    lineno: usize,
    file_stack: Vec<String>,
    program: Vec<u8>,
    labels: HashMap<String, usize>,
    label_requests: HashMap<String, Vec<LabelRequest>>,
}
impl Assembler {
    pub fn new() -> Self {
        Self {
            architectures: Vec::new(),
            current_arch: usize::MAX,
            block: CodeBlock::Program,
            arch_names: Default::default(),

            lineno: 0,
            file_stack: vec!["command-line".to_string()],
            program: Vec::new(),
            labels: Default::default(),
            label_requests: Default::default(),
        }
    }
    pub fn parse<'a>(&'a mut self, filename: &str) -> Result<&'a [u8], Vec<LocError>> {
        let res = self.accept_file(filename);

        let unmet_labels: Vec<_> = self
            .label_requests
            .values()
            .flat_map(|v| v.iter())
            .map(|req| self.err(req.label.clone()))
            .collect();

        if !unmet_labels.is_empty() {
            return Err(unmet_labels);
        }

        Ok(&self.program)
    }

    fn accept_file(&mut self, filename: &str) -> Result<(), Vec<LocError>> {
        let file = File::open(filename).map_err(|e| {
            let msg = format!(
                "Can't open file \"{filename}\" in \"{}\"",
                std::env::current_dir()
                    .ok()
                    .as_ref()
                    .and_then(|p| p.to_str())
                    .unwrap_or("<unknown>")
            );
            self.errs(AsmError::from(e).wrap(msg))
        })?;

        let reader = BufReader::new(file);
        let mut errors = Vec::<LocError>::new();
        let mut lineno = 0;

        for line in reader.lines() {
            lineno += 1;
            self.lineno = lineno;
            let line_str = line.map_err(|e| self.err(e))?;

            if let Err(mut e) = self.accept_line(&line_str) {
                errors.append(&mut e)
            }
        }

        if errors.is_empty() {
            Ok(())
        } else {
            Err(errors)
        }
    }
    pub fn write_output(&mut self, filename: &str) -> AsmResult<()> {
        let mut file = File::create(filename)?;
        let mut writer = BufWriter::new(file);
        writer.write_all(&self.program)?;
        writer.flush()?;

        Ok(())
    }
    fn accept_line(&mut self, line: &str) -> Result<(), Vec<LocError>> {
        let token = read_token_peek(line);
        if token.is_empty() {
            return Ok(());
        }

        match self.block {
            CodeBlock::Program => self.accept_program_line(line),
            CodeBlock::Architecture => self.accept_arch_line(line),
        }
    }

    fn arch(&self) -> AsmResult<&Arch> {
        if self.current_arch < self.architectures.len() {
            Ok(&self.architectures[self.current_arch])
        } else {
            Err("Can't encode instructions when no architecture is selected.".into())
        }
    }
    fn arch_mut(&mut self) -> &mut Arch {
        &mut self.architectures[self.current_arch]
    }
    fn add_arch(&mut self, arch: Arch) {
        let id = self.architectures.len();
        self.current_arch = id;
        self.arch_names.insert(arch.name.clone(), ArchId(id));
        self.architectures.push(arch);
    }

    fn accept_program_line(&mut self, mut line: &str) -> Result<(), Vec<LocError>> {
        debug!("Program line: {}", line);
        let mut token = read_token(&mut line);
        if token == TOK_MACRO_MARK {
            return self.accept_program_directive(line);
        }

        if is_identifier(token) {
            let next = read_token_peek(&line);
            if next == TOK_LABEL_MARK {
                self.read_exact(TOK_LABEL_MARK, &mut line);
                self.accept_program_label(token).map_err(|e| self.err(e))?;
                token = read_token(&mut line);

                if token.is_empty() {
                    return Ok(());
                }
            }
        }

        if is_identifier(token) {
            let ir = self
                .arch()
                .map_err(|e| self.err(e))?
                .get_instr_by_name(token);
            // TODO: repeat until match
            if let Some((_, ir)) = ir {
                let code = self
                    .accept_program_instr(ir, line)
                    .map_err(|e| self.err(e))?;

                // convert to bytes
                let bytes = code.len() / 8;
                for i in 0..bytes {
                    let byte: u8 = code[0 + i * 8..8 + i * 8].load();
                    self.program.push(byte);
                }
                return Ok(());
            } else {
                return Err(self.errs("Unknown mnemonic \"{token}\"."));
            }
        }

        let empty = Vec::new();
        let irs = self
            .arch()
            .map(|a| &a.instructions)
            .unwrap_or(&empty)
            .iter()
            .map(|ir| ir.mnemonic.as_str());
        let mut options: Vec<_> = irs.collect();
        options.insert(0, TOK_MACRO_MARK);
        Err(self
            .err(format!(
                "Unknown token \"{}\", expected one of {}",
                token,
                options.join(", ")
            ))
            .into())
    }
    fn accept_program_directive(&mut self, mut line: &str) -> Result<(), Vec<LocError>> {
        debug!("Program directive: {}", line);

        let options = [TOK_ARCH, TOK_USE, TOK_INCLUDE];
        let token = self
            .read_one_of(&options, &mut line)
            .map_err(|e| self.err(e.wrap_str("Unknown macro")))?;

        match token {
            2 => self.accept_directive_include(line),
            default => match token {
                0 => self.start_architecture_block(line),
                1 => self.accept_directive_use(line),
                default => Err("Handler for this macro not implemented".into()),
            }
            .map_err(|e| self.errs(e)),
        }
    }
    fn accept_directive_use(&mut self, mut line: &str) -> AsmResult<()> {
        let token = self.read_identifier(&mut line)?;
        if let Some(arch) = self.arch_names.get(token) {
            self.current_arch = arch.0;
        } else {
            return Err(format!("Unknown architecture \"{token}\".").into());
        }
        self.read_eol(&mut line)
    }
    fn accept_directive_include(&mut self, mut line: &str) -> Result<(), Vec<LocError>> {
        let filename = self.read_str_lit(&mut line).map_err(|e| self.err(e))?;

        warn!("Including file {filename}.");
        self.accept_file(filename)
    }
    fn accept_program_label(&mut self, label: &str) -> AsmResult<()> {
        debug!("Label: {}", label);

        let value = self.program.len();

        let symbol = self.arch_mut().get_symbol_mut(SYMBOL_LABEL);
        symbol.variants.insert(label.to_string(), value);

        // resolve requests under this label
        let requests = self.label_requests.remove(label);
        if let Some(requests) = requests {
            for req in requests {
                // rewrite
                let program_bits = BitSlice::<u8, Msb0>::from_slice_mut(&mut self.program);
                let offset = req.offset_bits;
                let part = req.part;
                trace!("{:?}", program_bits);
                program_bits[offset..offset + part.len()].store_be(value >> part.start);
                trace!("{:?}", program_bits);
            }
        }

        Ok(())
    }
    fn accept_program_instr(
        &mut self,
        ir_id: InstrId,
        mut line: &str,
    ) -> AsmResult<BitVec<usize, Msb0>> {
        let mut parsed_params = Vec::<ParsedParam>::new();

        let ir = self.arch()?.get_ir(ir_id);
        for expect_param in &ir.params {
            match expect_param {
                Param::Token { value } => {
                    self.read_exact(value.as_str(), &mut line);
                }
                Param::Symbol {
                    name,
                    symbol_id,
                    limit,
                } => {
                    let parsed = self.read_symbol_value(*symbol_id, limit.clone(), &mut line)?;
                    parsed_params.push(parsed);
                }
            }
        }

        // generate binary code
        let mut code: BitVec<usize, Msb0> = BitVec::with_capacity(1);
        let mut label_requests = Vec::new();
        for frag in &ir.encoding {
            match frag {
                Encode::Bits { value, size } => {
                    debug!("Appending const {:03X}:{} to {}", value, size, code);
                    let end = code.len();
                    code.resize(end + size, false);
                    code[end..end + size].store_be(*value);
                }
                Encode::Param { id, part, rel } => {
                    if *id >= parsed_params.len() {
                        return Err(format!(
                            "A parameter #{id} expected, but only parsed total of {}",
                            parsed_params.len()
                        )
                        .into());
                    }

                    let parsed = parsed_params[*id].clone();
                    let end = code.len();

                    let mut value = match parsed {
                        ParsedParam::Value(value) => value,
                        ParsedParam::UnresolvedLabel { label } => {
                            label_requests.push(LabelRequest {
                                offset_bits: self.program.len() * 8 + end,
                                part: part.clone(),
                                label,
                            });
                            -1
                        }
                    } - iff(*rel, self.program.len() as isize, 0);

                    debug!("Appending param {:03X}:{} to {}", value, part.len(), code);
                    code.resize(end + part.len(), false);
                    code[end..end + part.len()].store_be(value >> part.start);
                }
            }
        }

        for req in label_requests {
            self.add_label_req(req);
        }

        debug!("Converted instruction: {}", code);
        assert!(code.len() % 8 == 0);

        Ok(code)
    }

    fn start_architecture_block(&mut self, mut line: &str) -> AsmResult<()> {
        self.block = CodeBlock::Architecture;
        self.current_arch = self.architectures.len();
        let name = self.read_identifier(&mut line)?;
        self.architectures.push(Arch::new(name));
        Ok(())
    }
    fn accept_arch_line(&mut self, mut line: &str) -> Result<(), Vec<LocError>> {
        let token = self
            .read_one_of(&[TOK_SYMBOL, TOK_MNEM, TOK_MACRO_MARK], &mut line)
            .map_err(|e| self.err(e))?;

        match token {
            0 => self.accept_symbol_line(line),
            1 => self.accept_mnem_line(line),
            2 => self.accept_arch_directive(line),
            _ => todo!("Command branch not implemented"),
        }
        .map_err(|e| vec![self.err(e)])
    }
    fn accept_symbol_line(&mut self, mut my_line: &str) -> AsmResult<()> {
        let line = &mut my_line;
        let name = self.read_identifier(line)?;
        let size = self.read_size_opt(line)?;

        self.read_exact("=", line)?;
        let mut variants = HashMap::<String, usize>::new();

        let mut auto_inc = 0;
        loop {
            let variant = self.read_identifier(line)?;
            let value = match self.read_exact(TOK_SYMVAL_MARK, line) {
                Ok(_) => self.read_number_literal(line)?,
                Err(_) => auto_inc,
            };
            auto_inc = value + 1;

            if variants.contains_key(variant) {
                return Err(AsmError::new(&format!(
                    "Duplicate variant '{variant}' in symbol '{name}'"
                )));
            }
            variants.insert(variant.to_string(), value as _);
            if line.trim().is_empty() {
                break;
            }

            self.read_exact("|", line)?;
        }

        {
            let symbol = SymbolType {
                name: name.to_string(),
                size,
                variants,
            };
            debug!("symbol {:?}", symbol);
            self.arch_mut().add_symbol(symbol);
        }
        Ok(())
    }
    fn accept_mnem_line(&mut self, mut my_line: &str) -> AsmResult<()> {
        let line = &mut my_line;
        let mnem = read_token(line);

        let mut params = Vec::<Param>::new();
        let mut param_ids = Vec::<Option<usize>>::new();
        {
            let mut i = 0;
            loop {
                let token = read_token_peek(*line);
                match token {
                    "" => {
                        return Err(format!(
                            "Expected '->' followed by instruction encoding but found end of line"
                        )
                        .into())
                    }
                    TOK_REWRITE => break,
                    _ => (),
                };
                let param = self.read_param(line)?;
                match &param {
                    Param::Symbol { .. } => {
                        param_ids.push(Some(i));
                        i += 1;
                    }
                    Param::Token { .. } => param_ids.push(None),
                }
                params.push(param);
            }
        }

        self.read_exact(TOK_REWRITE, line)?;
        let size = self.read_size_opt(line);

        let mut encoding = Vec::<Encode>::new();
        loop {
            let token = read_token(line);
            if token.is_empty() {
                break;
            }
            let enc = match token {
                "$" => {
                    let name = self.read_identifier(line)?;

                    // NOTE: param ids skip tokens, so always ord >= id
                    let param_ord = params
                        .iter()
                        .position(|p| p.name() == Some(name))
                        .ok_or(format!("Unknown parameter '${name}'"))?;

                    let param: &Param = &params[param_ord];
                    let (symbol_id, x) = match param {
                        Param::Symbol {
                            symbol_id, limit, ..
                        } => (symbol_id, limit),
                        _ => panic!("\"{name}\" must be a symbol param."),
                    };
                    let param_id = param_ids[param_ord].unwrap();
                    let param_size = param.size(&self.arch()?.symbol_table);

                    let part = self
                        .read_brackets_opt(TOK_SIZE_OPEN, TOK_SIZE_CLOSE, line, |s, line| {
                            s.read_urange(line, true)
                        })?
                        .or(param_size.map(|s| 0..s));

                    let rel = read_token_peek(&line) == TOK_RELATIVE;
                    if rel {
                        read_token(line);
                    }

                    let part = match part {
                        Some(range) => range,
                        None => {
                            let tname = &self.arch()?.get_symbol(*symbol_id).name;
                            return Err(format!(
                                "Type {tname} of parameter ${name} is unsized and no explicit size was provided. Use ${name}[i:j] to specify, what bits should be encoded"
                            )
                            .into());
                        }
                    };
                    Encode::Param {
                        id: param_id,
                        part,
                        rel,
                    }
                }
                _ => {
                    let bits = usize::from_str_radix(token, 2)?;
                    Encode::Bits {
                        value: bits,
                        size: token.len(),
                    }
                }
            };
            encoding.push(enc);
        }

        self.arch_mut().instructions.push(Instr {
            mnemonic: mnem.to_string(),
            params,
            encoding,
        });
        Ok(())
    }
    fn accept_arch_directive(&mut self, mut my_line: &str) -> AsmResult<()> {
        self.read_exact(TOK_END, &mut my_line)?;
        self.read_exact(&self.arch()?.name, &mut my_line)?;
        self.read_eol(my_line)?;

        self.block = CodeBlock::Program;
        Ok(())
    }

    fn read_param(&self, parent_line: &mut &str) -> AsmResult<Param> {
        let mut line = *parent_line;
        let token = read_token(&mut line);

        let param = match token {
            "$" => {
                let param_name = self.read_identifier(&mut line)?;
                self.read_exact(TOK_SYMTYPE_MARK, &mut line)?;

                let symbol_name = self.read_identifier(&mut line)?;
                let (symbol, id) = self
                    .arch()?
                    .get_symbol_by_name(symbol_name)
                    .ok_or(format!("Unknown symbol name '{symbol_name}'"))?;

                let limit = self
                    .read_brackets_opt(TOK_LIMIT_OPEN, TOK_LIMIT_CLOSE, &mut line, |s, line| {
                        s.read_irange(line, false, false)
                    })?
                    .map(|lim| lim.start.min(lim.end)..lim.start.max(lim.end));

                Param::Symbol {
                    name: param_name.to_string(),
                    symbol_id: id,
                    limit,
                }
            }
            _ => Param::Token {
                value: token.to_string(),
            },
        };

        *parent_line = line;
        Ok(param)
    }

    fn read_exact(&self, expect: &str, parent_line: &mut &str) -> AsmResult<()> {
        let mut line = *parent_line;
        let token = read_token(&mut line);
        if token == expect {
            *parent_line = line;
            Ok(())
        } else {
            Err(AsmError {
                message: format!("Expected token '{expect}' but found '{token}'"),
                cause: None,
            })
        }
    }
    fn read_eol(&self, line: &str) -> AsmResult<()> {
        match line.trim().is_empty() {
            true => Ok(()),
            false => Err(AsmError {
                message: format!("Expected end of line, found '{}'", read_token_peek(line)),
                cause: None,
            }),
        }
    }
    fn read_identifier<'a>(&self, parent_line: &mut &'a str) -> AsmResult<&'a str> {
        let mut line = *parent_line;
        let token = read_token(&mut line);
        let valid = match token.chars().next() {
            Some(c) => c.is_alphabetic(),
            None => false,
        };

        if valid {
            *parent_line = line;
            Ok(token)
        } else {
            Err(AsmError {
                message: format!("Expected indentifier but found \"{token}\""),
                cause: None,
            })
        }
    }
    fn read_number_literal<'a>(&self, parent_line: &mut &'a str) -> AsmResult<isize> {
        let mut line = *parent_line;
        let mut token = read_token(&mut line);

        let mut neg = false;
        if token == "-" {
            neg = true;
            token = read_token(&mut line);
        }

        let result = match token.chars().last() {
            Some('h') => isize::from_str_radix(&token[0..token.len() - 1], 16),
            Some('d') => isize::from_str_radix(&token[0..token.len() - 1], 10),
            Some('o') => isize::from_str_radix(&token[0..token.len() - 1], 8),
            Some('b') => isize::from_str_radix(&token[0..token.len() - 1], 2),
            _ => isize::from_str_radix(token, 10),
        };

        if result.is_ok() {
            *parent_line = line;
        }

        result
            .map(|val| if !neg { val } else { -val })
            .map_err(|e| AsmError {
                message: format!("Invalid number literal \"{token}\""),
                cause: Some(Box::new(e.into())),
            })
    }
    fn read_sized_number_literal<'a>(
        &self,
        parent_line: &mut &'a str,
    ) -> AsmResult<SizedInt<isize>> {
        let mut line = *parent_line;
        let size = self.read_number_literal(parent_line)? as usize;
        self.read_exact("'", &mut line)?;
        let value = self.read_number_literal(&mut line)?;

        *parent_line = line;
        Ok(SizedInt { size, value })
    }
    fn read_irange(
        &self,
        parent_line: &mut &str,
        reverse: bool,
        unsigned: bool,
    ) -> AsmResult<Range<isize>> {
        let mut line = *parent_line;
        let a = self.read_number_literal(&mut line)?;
        self.read_exact(TOK_RANGE_SEP, &mut line)?;
        let b = self.read_number_literal(&mut line)?;

        let range = match reverse {
            false => a..(b + 1),
            true => b..(a + 1),
        };

        if unsigned && (range.start < 0 || range.end < 0) {
            return Err(format!("Negative range {a}:{b} not allowed here").into());
        }
        if range.start >= range.end {
            return Err(format!("Empty or negative-sized range {a}:{b} is not allowed").into());
        }

        *parent_line = line;
        Ok(range)
    }
    fn read_urange(&self, parent_line: &mut &str, reverse: bool) -> AsmResult<Range<usize>> {
        let mut line = *parent_line;
        let range = self.read_irange(&mut line, reverse, true)?;

        *parent_line = line;
        return Ok((range.start as usize)..(range.end as usize));
    }
    fn read_brackets<T, F>(
        &self,
        open: &str,
        close: &str,
        parent_line: &mut &str,
        content: F,
    ) -> AsmResult<T>
    where
        F: FnOnce(&Self, &mut &str) -> AsmResult<T>,
    {
        let mut line = *parent_line;
        self.read_exact(open, &mut line)?;
        let result = content(self, &mut line)?;
        self.read_exact(close, &mut line)?;

        *parent_line = line;
        return Ok(result);
    }
    fn read_brackets_opt<T, F>(
        &self,
        open: &str,
        close: &str,
        parent_line: &mut &str,
        content: F,
    ) -> AsmResult<Option<T>>
    where
        F: FnOnce(&Self, &mut &str) -> AsmResult<T>,
    {
        let mut line = *parent_line;
        if read_token(&mut line) == open {
            let result = content(self, &mut line)?;
            self.read_exact(close, &mut line)?;
            *parent_line = line;
            Ok(Some(result))
        } else {
            Ok(None)
        }
    }
    fn read_size_opt(&self, parent_line: &mut &str) -> AsmResult<Option<usize>> {
        let mut line = *parent_line;
        match read_token(&mut line) {
            TOK_SIZE_OPEN => {
                let size = self.read_number_literal(&mut line)?;
                self.read_exact(TOK_SIZE_CLOSE, &mut line)?;

                if size < 0 {
                    return Err(AsmError::new(&format!(
                        "Negative size [{size}] is not allowed"
                    )));
                }
                *parent_line = line;
                Ok(Some(size as usize))
            }
            _ => Ok(None),
        }
    }
    fn read_one_of(&self, options: &[&str], parent_line: &mut &str) -> AsmResult<usize> {
        let mut line = *parent_line;
        let token = read_token(&mut line);

        match options.iter().position(|opt| *opt == token) {
            Some(i) => {
                *parent_line = line;
                return Ok(i);
            }
            None => Err(format!("Expected one of {:?}, found '{token}'", options).into()),
        }
    }
    fn read_symbol_value(
        &self,
        mut symbol_id: SymbolTypeId,
        limit: Option<Range<isize>>,
        parent_line: &mut &str,
    ) -> AsmResult<ParsedParam> {
        let mut line = *parent_line;

        let mut token = read_token_peek(line);
        if let Some((_, id)) = self.arch()?.get_symbol_by_name(token) {
            self.read_exact(token, &mut line)?;
            self.read_exact(TOK_SYMTYPE_MARK, &mut line)?;
            symbol_id = id;
        }

        if symbol_id == SYMBOL_INT {
            return self
                .read_number_literal(&mut line)
                .map(|value| ParsedParam::Value(value));
        }

        token = self.read_identifier(&mut line)?;
        let symbol = self.arch()?.get_symbol(symbol_id);
        let found = symbol.get_variant(token);

        if found.is_none() {
            if symbol_id == SYMBOL_LABEL {
                return Ok(ParsedParam::UnresolvedLabel {
                    label: token.to_string(),
                });
            }

            return Err(format!(
                "Unknown variant \"{}\" of symbol {}. Expected one of {}",
                token,
                symbol.name,
                symbol
                    .variants
                    .keys()
                    .map(|s| s.as_str())
                    .collect::<Vec<_>>()
                    .join(", ")
            )
            .into());
        }

        let num = *found.unwrap() as isize;

        *parent_line = line;
        Ok(ParsedParam::Value(num))
    }
    fn read_str_lit<'a>(&self, parent_line: &mut &'a str) -> AsmResult<&'a str> {
        let mut line = *parent_line;
        let token = read_token(&mut line);

        if token.len() < 2
            || token.chars().nth(0).unwrap() != CHAR_QUOTE
            || token.chars().nth_back(0).unwrap() != CHAR_QUOTE
        {
            return Err(format!("Expected string literal, found: \"{}\"", token).into());
        }

        *parent_line = line;
        Ok(&token[1..token.len() - 1])
    }

    fn add_label_req(&mut self, req: LabelRequest) {
        if !self.label_requests.contains_key(&req.label) {
            self.label_requests.insert(req.label.clone(), Vec::new());
        }
        self.label_requests.get_mut(&req.label).unwrap().push(req);
    }

    fn err<T: Into<AsmError>>(&self, t: T) -> LocError {
        LocError {
            error: t.into(),
            file: self.file_stack.last().map(|s| s.clone()),
            line: self.lineno,
        }
    }
    fn errs<T: Into<AsmError>>(&self, t: T) -> Vec<LocError> {
        vec![LocError {
            error: t.into(),
            file: self.file_stack.last().map(|s| s.clone()),
            line: self.lineno,
        }]
    }
}

enum CodeBlock {
    Program,
    Architecture,
}

/// Get next token
fn read_token_peek<'a>(text: &'a str) -> &'a str {
    let mut my_text = text;
    read_token(&mut my_text)
}
/// Get next token and consume it
fn read_token<'a>(text: &mut &'a str) -> &'a str {
    #[derive(PartialEq, Eq)]
    enum State {
        Any,
        Ident,
        Sign,
        Minus,
        Symbol,
        String,
        StringEsc,
        LastOne,
        Done,
    }

    let mut start = 0;
    let mut len = 0;
    let mut state = State::Any;

    for c in text.chars() {
        state = match state {
            State::Any => {
                if c.is_whitespace() {
                    start += c.len_utf8();
                    continue;
                } else if c == '+' {
                    State::Sign
                } else if c == '-' {
                    State::Minus
                } else if c.is_alphanumeric() || c == '_' {
                    State::Ident
                } else if c == '"' {
                    State::String
                } else {
                    State::Symbol
                }
            }
            State::Ident => {
                if c.is_alphanumeric() || c == '_' {
                    state
                } else {
                    State::Done
                }
            }
            State::Sign => {
                if c.is_numeric() {
                    State::Ident
                } else if c == '>' {
                    State::Symbol
                } else {
                    State::Done
                }
            }
            State::Minus => match c {
                '>' => State::Symbol,
                '-' => {
                    len = 0;
                    State::Done
                }
                _ => State::Done,
            },
            State::Symbol => State::Done,
            State::String => match c {
                '\\' => State::StringEsc,
                '"' => State::LastOne,
                default => State::String,
            },
            State::StringEsc => State::String,
            State::Done => break,
            State::LastOne => break,
        };

        if state == State::Done {
            break;
        }

        len += c.len_utf8();
    }
    let end = start + len;
    let result = &text[start..end];

    *text = &text[end..];
    result
}

fn is_identifier(token: &str) -> bool {
    token.len() > 0 && char::is_alphanumeric(token.chars().next().unwrap())
}

fn iff<Bool: Into<bool>, T>(b: Bool, yes: T, no: T) -> T {
    match b.into() {
        true => yes,
        false => no,
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use crate::asm::*;

    fn setup_parser_empty() -> Assembler {
        let mut parser = Assembler::new();

        parser.add_arch(Arch::new("test"));
        parser.arch_mut().add_symbol(SymbolType {
            name: "reg".to_string(),
            size: Some(5),
            variants: {
                let mut variants = HashMap::new();
                variants.insert("r0".to_string(), 0);
                variants.insert("r1".to_string(), 1);
                variants.insert("r2".to_string(), 2);
                variants.insert("r3".to_string(), 3);
                variants
            },
        });
        parser
    }
    fn setup_parser_mov() -> Assembler {
        let mut parser = Assembler::new();
        let mut asm = |line| parser.accept_line(line).unwrap();

        asm(".architecture a1");
        asm("symbol reg[2] = r0 | r1 | r2 | r3");
        asm("mnem mov $rd:reg, $rs:reg -> 010 $rd 1 $rs");
        asm("mnem nop -> 0000 0000");
        asm(".end a1");

        parser
    }
    fn setup_parser_simple() -> Assembler {
        let mut parser = Assembler::new();
        let mut asm = |line| parser.accept_line(line).unwrap();

        asm(".architecture simple1");
        asm("symbol reg[2] = r0 | r1 | r2 | r3");
        asm("mnem mov $src:reg, $dst:reg -> 0000 $src $dst");
        asm("mnem add $src:reg, $dst:reg -> 0010 $src $dst");
        asm("mnem sub $src:reg, $dst:reg -> 0011 $src $dst");
        asm("mnem li  $imm:int(-64:63)   -> 01 $imm[5:0]");
        asm("mnem jmp $imm:label(0:4000h)-> 10 $imm[13:0]");
        asm("mnem nop                    -> 1111 1111");
        asm(".end simple1");

        parser
    }

    #[test]
    fn read_token_is_read_word() {
        let mut input = "hello world, how are you doing?";

        assert_eq!(read_token(&mut input), "hello");
        assert_eq!(read_token(&mut input), "world");
        assert_eq!(read_token(&mut input), ",");
        assert_eq!(read_token(&mut input), "how");
        assert_eq!(read_token(&mut input), "are");
        assert_eq!(read_token(&mut input), "you");
        assert_eq!(read_token(&mut input), "doing");
        assert_eq!(read_token(&mut input), "?");
        assert_eq!(read_token(&mut input).is_empty(), true);
    }

    #[test]
    fn arrow_is_one_token() {
        let mut input = "1 -> 24 -> 789 [-123] \"he lo\"  \"    \"";

        assert_eq!(read_token(&mut input), "1");
        assert_eq!(read_token(&mut input), TOK_REWRITE);
        assert_eq!(read_token(&mut input), "24");
        assert_eq!(read_token(&mut input), TOK_REWRITE);
        assert_eq!(read_token(&mut input), "789");
        assert_eq!(read_token(&mut input), TOK_SIZE_OPEN);
        assert_eq!(read_token(&mut input), TOK_MINUS);
        assert_eq!(read_token(&mut input), "123");
        assert_eq!(read_token(&mut input), TOK_SIZE_CLOSE);
        assert_eq!(read_token(&mut input), "\"he lo\"");
        assert_eq!(read_token(&mut input), "\"    \"");
        assert_eq!(read_token(&mut input).is_empty(), true);
    }

    #[test]
    fn number_radix_is_correctly_parsed() {
        let mut input = "numbers 1 FFh 10FFh 1010b 10o 100o 10 101 1111111111111111b -5 -FFh";
        let parser = setup_parser_empty();

        assert_eq!(read_token(&mut input), "numbers");
        assert_eq!(parser.read_number_literal(&mut input), Ok(1));
        assert_eq!(parser.read_number_literal(&mut input), Ok(0xff));
        assert_eq!(parser.read_number_literal(&mut input), Ok(0x10ff));
        assert_eq!(parser.read_number_literal(&mut input), Ok(0b1010));
        assert_eq!(parser.read_number_literal(&mut input), Ok(8));
        assert_eq!(parser.read_number_literal(&mut input), Ok(64));
        assert_eq!(parser.read_number_literal(&mut input), Ok(10));
        assert_eq!(parser.read_number_literal(&mut input), Ok(101));
        assert_eq!(parser.read_number_literal(&mut input), Ok(0xffff));
        assert_eq!(parser.read_number_literal(&mut input), Ok(-5));
        assert_eq!(parser.read_number_literal(&mut input), Ok(-255));
        assert_eq!(read_token(&mut input).is_empty(), true);
    }

    #[test]
    fn range_is_correctly_parsed() {
        let mut input = "ranges 10:0 0:10 0:99 -10:9 9:-10";
        let parser = setup_parser_empty();

        assert_eq!(read_token(&mut input), "ranges");
        assert_eq!(parser.read_irange(&mut input, true, false).unwrap(), 0..11);
        assert_eq!(parser.read_irange(&mut input, false, false).unwrap(), 0..11);
        assert_eq!(
            parser.read_irange(&mut input, false, false).unwrap(),
            0..100
        );
        assert_eq!(
            parser.read_irange(&mut input, false, false).unwrap(),
            -10..10
        );
        assert_eq!(
            parser.read_irange(&mut input, true, false).unwrap(),
            -10..10
        );
        assert_eq!(read_token(&mut input).is_empty(), true);
    }

    #[test]
    fn param_is_correctly_parsed() {
        let mut input = "$test:reg $arg:reg(0:1)";
        let parser = setup_parser_empty();

        assert_eq!(
            parser.read_param(&mut input).unwrap(),
            Param::Symbol {
                name: "test".to_string(),
                symbol_id: SymbolTypeId(2),
                limit: None
            }
        );
        assert_eq!(
            parser.read_param(&mut input).unwrap(),
            Param::Symbol {
                name: "arg".to_string(),
                symbol_id: SymbolTypeId(2),
                limit: Some(0..2)
            }
        );
    }

    #[test]
    fn symbol_is_correctly_parsed() {
        let mut parser = Assembler::new();

        let lines = vec![
            ".architecture a1",
            "symbol reg[2] = r0:0 | r1 | r2 | r3",
            "symbol test = r0 | r1 | hello:10 | world",
            ".end a1",
        ];

        for l in &lines {
            parser.accept_line(l).unwrap();
        }

        let reg = parser.arch().unwrap().get_symbol_by_name("reg").unwrap().0;
        assert_eq!(reg.name, "reg");
        assert_eq!(reg.size, Some(2));

        let test = parser.arch().unwrap().get_symbol_by_name("test").unwrap().0;
        assert_eq!(test.variants.get("r0"), Some(&0));
        assert_eq!(test.variants.get("r1"), Some(&1));
        assert_eq!(test.variants.get("hello"), Some(&10));
        assert_eq!(test.variants.get("world"), Some(&11));
        assert_eq!(test.size, None);
    }

    #[test]
    fn mnemonic_params_parsed_and_encoded() {
        let mut p = Assembler::new();
        let mut asm = |line| p.accept_line(line).unwrap();
        let mut s = |text| String::from(text);

        asm(".architecture a1");
        asm("symbol reg[2] = r0 | r1 | r2 | r3");
        asm("mnem sum $r0:reg, $r1:reg, $r2:reg, $r3:reg, $r4:reg -> 100100 $r0 $r1 $r2 $r3 $r4");
        asm(".end a1");

        let ir = p.arch().unwrap().get_instr_by_name("sum").unwrap().0;
        let (_, reg2) = p.arch().unwrap().get_symbol_by_name("reg").unwrap();

        assert_eq!(ir.mnemonic, "sum");
        assert_eq!(ir.params.len(), 9);
        assert_eq!(
            ir.params[0],
            Param::Symbol {
                name: s("r0"),
                symbol_id: reg2,
                limit: None
            }
        );
        assert_eq!(ir.params[1], Param::Token { value: s(",") });
        assert_eq!(
            ir.params[2],
            Param::Symbol {
                name: s("r1"),
                symbol_id: reg2,
                limit: None
            }
        );
        assert_eq!(ir.params[3], Param::Token { value: s(",") });
        assert_eq!(
            ir.params[4],
            Param::Symbol {
                name: s("r2"),
                symbol_id: reg2,
                limit: None
            }
        );
        assert_eq!(ir.params[5], Param::Token { value: s(",") });
        assert_eq!(
            ir.params[6],
            Param::Symbol {
                name: s("r3"),
                symbol_id: reg2,
                limit: None
            }
        );
        assert_eq!(ir.params[7], Param::Token { value: s(",") });
        assert_eq!(
            ir.params[8],
            Param::Symbol {
                name: s("r4"),
                symbol_id: reg2,
                limit: None
            }
        );

        assert_eq!(ir.encoding.len(), 6);
        assert_eq!(
            ir.encoding[0],
            Encode::Bits {
                value: 0b100100,
                size: 6
            }
        );
        assert_eq!(
            ir.encoding[1],
            Encode::Param {
                id: 0,
                part: 0..2,
                rel: false
            }
        );
        assert_eq!(
            ir.encoding[2],
            Encode::Param {
                id: 1,
                part: 0..2,
                rel: false
            }
        );
        assert_eq!(
            ir.encoding[3],
            Encode::Param {
                id: 2,
                part: 0..2,
                rel: false
            }
        );
        assert_eq!(
            ir.encoding[4],
            Encode::Param {
                id: 3,
                part: 0..2,
                rel: false
            }
        );
        assert_eq!(
            ir.encoding[5],
            Encode::Param {
                id: 4,
                part: 0..2,
                rel: false
            }
        );
    }

    #[test]
    fn mnemonic_params_encoded() {
        let p = setup_parser_mov();

        let ir = p.arch().unwrap().get_instr_by_name("mov").unwrap().0;

        assert_eq!(ir.mnemonic, "mov");
        assert_eq!(ir.params.len(), 3);

        assert_eq!(ir.encoding.len(), 4);
        assert_eq!(ir.encoding[0], Encode::Bits { value: 2, size: 3 });
        assert_eq!(
            ir.encoding[1],
            Encode::Param {
                id: 0,
                part: 0..2,
                rel: false
            }
        );
        assert_eq!(ir.encoding[2], Encode::Bits { value: 1, size: 1 });
        assert_eq!(
            ir.encoding[3],
            Encode::Param {
                id: 1,
                part: 0..2,
                rel: false
            }
        );
    }

    #[test]
    fn mnemonic_translated() {
        let mut p = setup_parser_mov();
        let mut asm = |line| p.accept_line(line).unwrap();

        asm("mov r0 r1");
        asm("mov r1 r2");
        asm("mov r2 r3");
        asm("mov r3 r0");

        assert_eq!(p.program.len(), 4);
        assert_eq!(p.program[0], 0b010_00_1_01);
        assert_eq!(p.program[1], 0b010_01_1_10);
        assert_eq!(p.program[2], 0b010_10_1_11);
        assert_eq!(p.program[3], 0b010_11_1_00);
    }

    #[test]
    fn label_before_mnemonic_parsed() {
        let mut p = setup_parser_mov();
        let mut asm = |line| p.accept_line(line).unwrap();

        asm("a: nop");
        asm("b: mov r1 r2");
        asm("c: mov r2 r3");
        asm("d: mov r3 r0");

        assert_eq!(p.program.len(), 4);
        assert_eq!(p.program[0], 0);
        assert_eq!(p.program[1], 0b010_01_1_10);
        assert_eq!(p.program[2], 0b010_10_1_11);
        assert_eq!(p.program[3], 0b010_11_1_00);

        let label = p.arch().unwrap().get_symbol(SYMBOL_LABEL);
        assert!(label.get_variant("a").is_some());
        assert!(label.get_variant("b").is_some());
        assert!(label.get_variant("c").is_some());
        assert!(label.get_variant("d").is_some());
    }

    #[test]
    fn label_backwards_translated() {
        let mut parser = setup_parser_simple();
        let mut asm = |line| parser.accept_line(line).unwrap();

        asm("li 1");
        asm("top:");
        asm("mov r1, r2");
        asm("mov r0, r1");
        asm("add r2, r0");
        asm("jmp top");

        assert_eq!(parser.program[0], 0b01_000001);
        assert_eq!(parser.program[1], 0b0000_01_10);
        assert_eq!(parser.program[2], 0b0000_00_01);
        assert_eq!(parser.program[3], 0b0010_10_00);
        assert_eq!(parser.program[4], 0b10_000000);
        assert_eq!(parser.program[5], 0b00000001);
    }

    #[test]
    fn label_forwards_translated() {
        let mut parser = setup_parser_simple();
        let mut asm = |line| parser.accept_line(line).unwrap();

        asm("jmp skip");
        asm("li 1");
        asm("skip:");
        asm("li 2");
        asm("nop");
        asm("jmp skip2");
        asm("nop");
        asm("skip2: nop");
        asm("nop");

        assert_eq!(parser.program[0], 0b10_000000);
        assert_eq!(parser.program[1], 0b00000011);
        assert_eq!(parser.program[2], 0b01_000001);
        assert_eq!(parser.program[3], 0b01_000010);
        assert_eq!(parser.program[4], 0b1111_1111);
        assert_eq!(parser.program[5], 0b10_000000);
        assert_eq!(parser.program[6], 0b00001000);
        assert_eq!(parser.program[7], 0b1111_1111);
        assert_eq!(parser.program[8], 0b1111_1111);
        assert_eq!(parser.program[8], 0b1111_1111);
        assert_eq!(parser.program.len(), 10);
    }

    #[test]
    fn parameter_part_not_zero() {
        let mut parser = Assembler::new();
        let mut asm = |line| parser.accept_line(line).unwrap();

        asm(".architecture a1");
        asm("mnem test $a:int -> $a[7:4] 0000");
        asm(".end a1");
        asm("test A0h");

        assert_eq!(parser.program[0], 0b10100000);
    }

    #[test]
    fn parameter_part_repeat() {
        let mut parser = Assembler::new();
        let mut asm = |line| parser.accept_line(line).unwrap();

        asm(".architecture a1");
        asm("mnem test x y $a:int z w -> $a[7:6] $a[7:6] $a[7:6] $a[7:6]");
        asm(".end a1");
        asm("test x y 80h z w");

        assert_eq!(parser.program[0], 0b10101010);
    }

    #[test]
    fn parameter_relative_repeat() {
        let mut parser = Assembler::new();
        let mut asm = |line| parser.accept_line(line).unwrap();

        asm(".architecture a1");
        asm("mnem test x y $a:int z w -> $a[7:6]R $a[7:6] $a[7:6]R $a[7:6]");
        asm(".end a1");
        asm("test x y 80h z w");
        asm("test x y 80h z w");

        assert_eq!(parser.program[0], 0b10101010);
        assert_eq!(parser.program[1], 0b01100110);
    }

    #[test]
    fn include_architecture_works() {
        let mut parser = Assembler::new();

        parser
            .accept_line(".include \"test-data/test1.arch\"")
            .unwrap();
        parser.accept_line("nop").unwrap();

        assert!(parser.arch().is_ok());

        assert_eq!(parser.program[0], 0b1000_0000);
        assert_eq!(parser.program.len(), 1);
    }

    #[test]
    fn relative_label_is_relative() {
        let mut p = Assembler::new();
        let mut asm = |s| p.accept_line(s);

        asm(".architecture a").unwrap();
        asm("mnem nop -> 0000 0000").unwrap();
        asm("mnem rjmp $dst:label -> 1000 $dst[3:0] R $dst[7:0]").unwrap();
        asm(".end a").unwrap();

        asm("zero: nop").unwrap();
        asm("nop").unwrap();
        asm("nop").unwrap();
        asm("nop").unwrap();
        asm("four: nop").unwrap();
        asm("rjmp zero").unwrap();
        asm("rjmp four").unwrap();

        let jmp1 = ((p.program[5] as u32) << 8) | p.program[6] as u32;
        let jmp2 = ((p.program[7] as u32) << 8) | p.program[8] as u32;

        assert_eq!(jmp1, 0b1000_1011__0000_0000);
        assert_eq!(jmp2, 0b1000_1101__0000_0100);
    }
}
