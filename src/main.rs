#![allow(unused)]

use bitvec::prelude::*;
use std::collections::HashMap;
use std::fmt::Display;
use std::fs::File;
use std::io::{BufRead, BufReader, Error};
use std::num::ParseIntError;
use std::ops::Range;

fn main() -> Result<(), Error> {
    let mut parser = Parser::new();

    let file = File::open("examples/riscv32i.arch")?;
    let reader = BufReader::new(file);

    let mut i = 0;
    for line in reader.lines() {
        i += 1;
        let result = parser.accept_line(&line?);

        match result {
            Err(e) => println!("line {i}: {e}"),
            _ => (),
        }
    }

    Ok(())
}

type ParserResult<T> = Result<T, ParserError>;

struct Arch {
    name: String,
    symbol_table: Vec<TypedSymbol>,
    instructions: Vec<Instr>,
}
impl Arch {
    fn new(name: &str) -> Self {
        Self {
            name: name.to_string(),
            symbol_table: Vec::new(),
            instructions: Vec::new(),
        }
    }
    fn add_symbol(&mut self, symbol: TypedSymbol) {
        self.symbol_table.push(symbol)
    }
    fn get_symbol(&self, id: TypedSymbolRef) -> &TypedSymbol {
        &self.symbol_table[id.0]
    }
    fn get_symbol_by_name(&self, name: &str) -> Option<(&TypedSymbol, TypedSymbolRef)> {
        let id = self.symbol_table.iter().position(|s| s.name == name);
        id.map(|id| (&self.symbol_table[id], TypedSymbolRef(id)))
    }
    fn get_ir(&self, id: InstrRef) -> &Instr {
        &self.instructions[id.0]
    }
    fn get_ir_by_name(&self, name: &str) -> Option<(&Instr, InstrRef)> {
        let id = self.instructions.iter().position(|s| s.mnem == name);
        id.map(|id| (&self.instructions[id], InstrRef(id)))
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
struct ArchRef(usize);

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
struct TypedSymbolRef(usize);
impl TypedSymbolRef {
    pub fn deref(self, arch: &Arch) -> &TypedSymbol {
        arch.get_symbol(self)
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
struct InstrRef(usize);

#[derive(Debug)]
struct TypedSymbol {
    name: String,
    size: Option<usize>,
    variants: HashMap<String, usize>,
}
struct Instr {
    mnem: String,
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
        symbol: TypedSymbolRef,
        limit: Option<Range<isize>>,
    },
    Token {
        value: String,
    },
}
impl Param {
    pub fn token(&self) -> &str {
        match self {
            Param::Symbol { name, .. } => name,
            Param::Token { value, .. } => value,
        }
    }
    pub fn size(&self, symbol_table: &Vec<TypedSymbol>) -> Option<usize> {
        match self {
            Param::Symbol { symbol, .. } => symbol_table[symbol.0].size,
            Param::Token { value, .. } => None,
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
enum Encode {
    Bits { value: usize, size: usize },
    Param { id: usize, part: Range<usize> },
}

struct LabelRequest {
    address: usize,
    ir: Instr,
}

struct Parser {
    architectures: Vec<Arch>,
    current_arch: usize,
    block: CodeBlock,
    arch_names: HashMap<String, ArchRef>,

    program: Vec<u8>,
    labels: HashMap<String, usize>,
    label_requests: HashMap<String, Vec<LabelRequest>>,
}
impl Parser {
    pub fn new() -> Self {
        Self {
            architectures: Vec::new(),
            block: CodeBlock::Program,
            arch_names: Default::default(),
            current_arch: usize::MAX,
            program: Vec::new(),
            labels: Default::default(),
            label_requests: Default::default(),
        }
    }
    pub fn accept_line(&mut self, line: &str) -> ParserResult<()> {
        if line.is_empty() {
            return Ok(());
        }

        match self.block {
            CodeBlock::Program => self.accept_program_line(line),
            CodeBlock::Architecture => self.accept_arch_line(line),
        }
    }

    fn arch(&self) -> &Arch {
        &self.architectures[self.current_arch]
    }
    fn arch_mut(&mut self) -> &mut Arch {
        &mut self.architectures[self.current_arch]
    }
    fn add_arch(&mut self, arch: Arch) {
        let id = self.architectures.len();
        self.current_arch = id;
        self.arch_names.insert(arch.name.clone(), ArchRef(id));
        self.architectures.push(arch);
    }

    fn accept_program_line(&mut self, mut line: &str) -> ParserResult<()> {
        println!("Program line: {}", line);
        let mut tok = read_token(&mut line);
        if tok == "#" {
            return self.accept_program_directive(line);
        } else if tok == "--" {
            // comment
            println!("Comment: {}", line);
            return Ok(());
        }

        if is_ident(tok) {
            let next = read_token_peek(&line);
            if next == ":" {
                self.read_exact(":", &mut line);
                self.accept_program_label(tok)?;
                tok = read_token(&mut line);
            }
        }

        if is_ident(tok) {
            let ir = self.arch().get_ir_by_name(tok);
            if let Some((_, ir)) = ir {
                return self.accept_program_instr(ir, line);
            } else {
                return self.err(format!("Unknown mnemonic '{tok}'."));
            }
        }

        let irs = self.arch().instructions.iter().map(|ir| ir.mnem.as_str());
        self.err(format!(
            "Unknown token '{}', expected one of '#', {}",
            tok,
            irs.collect::<Vec<_>>().join(", ")
        ))
    }
    fn accept_program_directive(&mut self, mut line: &str) -> ParserResult<()> {
        println!("Program directive: {}", line);
        let token = read_token(&mut line);

        match token {
            "architecture" => self.start_architecture_block(line),
            "use" => todo!(),
            _ => self.err(format!(
                "Unknown directive '#{token}'. Expected '#architecture' or '#use'."
            )),
        }
    }
    fn accept_program_label(&mut self, label: &str) -> ParserResult<()> {
        println!("Label: {}", label);
        todo!()
    }
    fn accept_program_instr(&mut self, ir: InstrRef, mut line: &str) -> ParserResult<()> {
        let mut parsed_params = Vec::<isize>::new();
        for expect_param in &self.arch().get_ir(ir).params {
            match expect_param {
                Param::Token { value } => {
                    self.read_exact(value.as_str(), &mut line);
                }
                Param::Symbol {
                    name,
                    symbol,
                    limit,
                } => {
                    let symbol = self.arch().get_symbol(*symbol);
                    let value = self.read_symbol_value(symbol, limit.clone(), &mut line)?;
                    parsed_params.push(value);
                }
            }
        }

        let mut code = BitVec::<usize, Msb0>::with_capacity(1);
        let mut end = 0;
        let ir = self.arch().get_ir(ir);
        for frag in &ir.encoding {
            match frag {
                Encode::Bits { value, size } => {
                    println!("Appending const {:03X}:{} to {}", value, size, code);
                    code.resize(code.len() + size, false);
                    code[end..end + size].store(*value);
                    end += size;
                }
                Encode::Param { id, part } => {
                    if *id >= parsed_params.len() {
                        return self.err(format!(
                            "A parameter #{id} expected, but only parsed total of {}.",
                            parsed_params.len()
                        ));
                    }
                    let value = parsed_params[*id];
                    println!("Appending param {:03X}:{} to {}", value, part.len(), code);
                    code.resize(code.len() + part.len(), false);
                    code[end..end + part.len()].store(value);
                    end += part.len();
                }
            }
        }

        println!("Converted instruction: {}", code);
        assert!(code.len() % 8 == 0);

        let bytes = code.len() / 8;
        for i in 0..bytes {
            let byte: u8 = code[0 + i * 8..8 + i * 8].load();
            self.program.push(byte);
        }

        Ok(())
    }

    fn start_architecture_block(&mut self, mut line: &str) -> ParserResult<()> {
        self.block = CodeBlock::Architecture;
        self.current_arch = self.architectures.len();
        let name = self.read_indentifier(&mut line)?;
        self.architectures.push(Arch::new(name));
        Ok(())
    }
    fn accept_arch_line(&mut self, mut line: &str) -> ParserResult<()> {
        let token = self.read_one_of(&["symbol", "mnem", "#"], &mut line)?;

        match token {
            0 => self.accept_symbol_line(line),
            1 => self.accept_mnem_line(line),
            2 => self.accept_arch_directive(line),
            _ => todo!("Command branch not implemented"),
        }
    }
    fn accept_symbol_line(&mut self, mut my_line: &str) -> ParserResult<()> {
        let line = &mut my_line;
        let name = self.read_indentifier(line)?;
        let size = self.read_size_opt(line)?;

        self.read_exact("=", line)?;
        let mut variants = HashMap::<String, usize>::new();

        let mut auto_inc = 0;
        loop {
            let variant = self.read_indentifier(line)?;
            let value = match self.read_exact(":", line) {
                Ok(_) => self.read_number_literal(line)?,
                Err(_) => auto_inc,
            };
            auto_inc = value + 1;

            if variants.contains_key(variant) {
                return Err(ParserError::new(&format!(
                    "Duplicate variant '{variant}' in symbol '{name}'."
                )));
            }
            variants.insert(variant.to_string(), value as _);
            if line.trim().is_empty() {
                break;
            }

            self.read_exact("|", line)?;
        }

        {
            let symbol = TypedSymbol {
                name: name.to_string(),
                size,
                variants,
            };
            println!("{:?}", symbol);
            self.arch_mut().add_symbol(symbol);
        }
        Ok(())
    }
    fn accept_mnem_line(&mut self, mut my_line: &str) -> ParserResult<()> {
        let line = &mut my_line;
        let mnem = read_token(line);

        let mut params = Vec::<Param>::new();
        loop {
            let token = read_token_peek(*line);

            match token {
                "" => {
                    return self.err(format!(
                        "Expected '->' followed by instruction encoding but found end of line."
                    ))
                }
                "->" => break,
                _ => (),
            };

            let param = self.read_param(line)?;
            params.push(param);
        }

        self.read_exact("->", line)?;
        let size = self.read_size_opt(line);

        let mut encoding = Vec::<Encode>::new();
        let mut encode_params = 0;
        loop {
            let token = read_token(line);
            if token.is_empty() {
                break;
            }
            let enc = match token {
                "$" => {
                    let token = self.read_indentifier(line)?;

                    let param_id = params
                        .iter()
                        .position(|p| p.token() == token)
                        .ok_or(self.parse_error(format!("Unknown parameter '${token}'"), None))?;
                    let param = &params[param_id];
                    let param_size = param.size(&self.arch().symbol_table);

                    let part = self
                        .read_brackets_opt("[", "]", line, |s, line| s.read_urange(line))?
                        .or(param_size.map(|size| 0..size));

                    let part = match part {
                        Some(range) => range,
                        None => {
                            return self.err(format!(
                                "Parameter ${token} is unsized and no explicit size was provided. \
                            Use ${token}[i:j] to specify, what bits should be encoded."
                            ))
                        }
                    };
                    let id = encode_params;
                    encode_params += 1;
                    Encode::Param { id, part }
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
            mnem: mnem.to_string(),
            params,
            encoding,
        });
        Ok(())
    }
    fn accept_arch_directive(&mut self, mut my_line: &str) -> ParserResult<()> {
        self.read_exact("end", &mut my_line)?;
        self.read_exact(&self.arch().name, &mut my_line)?;
        self.read_eol(my_line)?;

        self.block = CodeBlock::Program;
        Ok(())
    }

    fn read_param(&self, parent_line: &mut &str) -> ParserResult<Param> {
        let mut line = *parent_line;
        let token = read_token(&mut line);

        let param = match token {
            "$" => {
                let param_name = self.read_indentifier(&mut line)?;
                self.read_exact(":", &mut line)?;

                let symbol_name = self.read_indentifier(&mut line)?;
                let (symbol, id) = self.arch().get_symbol_by_name(symbol_name).ok_or(
                    self.parse_error(format!("Unknown symbol name '{symbol_name}'."), None),
                )?;

                let token = read_token_peek(line);
                let limit = self
                    .read_brackets_opt("(", ")", &mut line, |s, line| s.read_irange(line))?
                    .map(|lim| lim.start.min(lim.end)..lim.start.max(lim.end));

                Param::Symbol {
                    name: param_name.to_string(),
                    symbol: id,
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

    fn read_exact(&self, expect: &str, parent_line: &mut &str) -> ParserResult<()> {
        let mut line = *parent_line;
        let token = read_token(&mut line);
        if token == expect {
            *parent_line = line;
            Ok(())
        } else {
            Err(ParserError {
                message: format!("Expected token '{expect}' but found '{token}'."),
                cause: None,
            })
        }
    }
    fn read_eol(&self, line: &str) -> ParserResult<()> {
        match line.trim().is_empty() {
            true => Ok(()),
            false => Err(ParserError {
                message: format!("Expected end of line, found '{}'", read_token_peek(line)),
                cause: None,
            }),
        }
    }
    fn read_indentifier<'a>(&self, parent_line: &mut &'a str) -> ParserResult<&'a str> {
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
            Err(ParserError {
                message: format!("Expected indentifier but found '{token}'."),
                cause: None,
            })
        }
    }
    fn read_number_literal<'a>(&self, parent_line: &mut &'a str) -> ParserResult<isize> {
        let mut line = *parent_line;
        let token = read_token(&mut line);

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

        result.map_err(|e| ParserError {
            message: format!("Invalid number literal '{token}'."),
            cause: Some(Box::new(e.into())),
        })
    }
    fn read_sized_number_literal<'a>(
        &self,
        parent_line: &mut &'a str,
    ) -> ParserResult<SizedInt<isize>> {
        let mut line = *parent_line;
        let size = self.read_number_literal(parent_line)? as usize;
        self.read_exact("'", &mut line)?;
        let value = self.read_number_literal(&mut line)?;

        *parent_line = line;
        Ok(SizedInt { size, value })
    }
    fn read_irange(&self, parent_line: &mut &str) -> ParserResult<Range<isize>> {
        let mut line = *parent_line;
        let upper = self.read_number_literal(&mut line)?;
        self.read_exact(":", &mut line)?;
        let lower = self.read_number_literal(&mut line)?;

        *parent_line = line;
        return Ok(lower..upper);
    }
    fn read_urange(&self, parent_line: &mut &str) -> ParserResult<Range<usize>> {
        let mut line = *parent_line;
        let range = self.read_irange(&mut line)?;

        if range.start < 0 || range.end < 0 {
            return self.err(format!(
                "Negative range {}:{} not allowed.",
                range.end, range.start
            ));
        }

        *parent_line = line;
        return Ok((range.start as usize)..(range.end as usize));
    }
    fn read_brackets<T, F>(
        &self,
        open: &str,
        close: &str,
        parent_line: &mut &str,
        content: F,
    ) -> ParserResult<T>
    where
        F: FnOnce(&Self, &mut &str) -> ParserResult<T>,
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
    ) -> ParserResult<Option<T>>
    where
        F: FnOnce(&Self, &mut &str) -> ParserResult<T>,
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
    fn read_size_opt(&self, parent_line: &mut &str) -> ParserResult<Option<usize>> {
        let mut line = *parent_line;
        match read_token(&mut line) {
            "[" => {
                let size = self.read_number_literal(&mut line)?;
                self.read_exact("]", &mut line)?;

                if size < 0 {
                    return Err(ParserError::new(&format!(
                        "Negative size [{size}] is not allowed."
                    )));
                }
                *parent_line = line;
                Ok(Some(size as usize))
            }
            _ => Ok(None),
        }
    }
    fn read_one_of(&self, options: &[&str], parent_line: &mut &str) -> ParserResult<usize> {
        let mut line = *parent_line;
        let token = read_token(&mut line);

        match options.iter().position(|opt| *opt == token) {
            Some(i) => {
                *parent_line = line;
                return Ok(i);
            }
            None => self.err(format!("Expected one of {:?}, found '{token}'.", options)),
        }
    }
    fn read_symbol_value(
        &self,
        symbol: &TypedSymbol,
        limit: Option<Range<isize>>,
        parent_line: &mut &str,
    ) -> ParserResult<isize> {
        let mut line = *parent_line;
        let token = read_token(&mut line);

        let num = if symbol.name == "int" {
            self.read_number_literal(&mut line)?
        } else {
            let found = symbol.variants.get(token);

            if found.is_none() {
                return self.err(format!(
                    "Unknown value '{}' of symbol {}. Expected one of {}.",
                    token,
                    symbol.name,
                    symbol
                        .variants
                        .keys()
                        .map(|s| s.as_str())
                        .collect::<Vec<_>>()
                        .join(", ")
                ));
            }
            *found.unwrap() as _
        };

        *parent_line = line;
        Ok(num)
    }

    fn parse_error(&self, message: String, cause: Option<ParserError>) -> ParserError {
        ParserError {
            message,
            cause: cause.map(|e| Box::new(e)),
        }
    }
    fn err<T>(&self, message: String) -> ParserResult<T> {
        Err(self.parse_error(message, None))
    }
    fn err_c<T>(&self, message: String, cause: ParserError) -> ParserResult<T> {
        Err(self.parse_error(message, Some(cause)))
    }
}

#[derive(Debug, PartialEq, Eq)]
struct ParserError {
    pub message: String,
    pub cause: Option<Box<ParserError>>,
}
impl ParserError {
    fn new(text: &str) -> Self {
        Self {
            message: text.to_string(),
            cause: None,
        }
    }
}
impl Display for ParserError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.message)?;
        if let Some(ref reason) = self.cause {
            f.write_fmt(format_args!("Caused by: {}", reason.as_ref()))?;
        }
        Ok(())
    }
}
impl From<ParseIntError> for ParserError {
    fn from(value: ParseIntError) -> Self {
        Self {
            message: format!("{value}"),
            cause: None,
        }
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
        Done,
    }

    let mut start = 0;
    let mut len = 0;
    let mut state = State::Any;

    for c in text.chars() {
        if c.is_whitespace() {
            if len == 0 {
                start += c.len_utf8();
                continue;
            } else {
                break;
            }
        }

        state = match state {
            State::Any => {
                if c == '+' {
                    State::Sign
                } else if c == '-' {
                    State::Minus
                } else if c.is_alphanumeric() || c == '_' {
                    State::Ident
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
                '>' | '-' => State::Symbol,
                _ => State::Done,
            },
            State::Symbol => State::Done,
            State::Done => break,
        };

        if state == State::Done {
            break;
        } else {
            len += c.len_utf8();
        }
    }
    let end = start + len;
    let result = &text[start..end];

    *text = &text[end..];
    return result;
}

fn is_ident(token: &str) -> bool {
    token.len() > 0 && char::is_alphanumeric(token.chars().next().unwrap())
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use crate::{read_token, Arch, Encode, Param, Parser, TypedSymbol, TypedSymbolRef};

    fn setup_parser() -> Parser {
        let mut parser = Parser::new();

        parser.add_arch(Arch::new("test"));
        parser.arch_mut().add_symbol(TypedSymbol {
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
        let mut input = "1 -> 24 -> 789 [-123]";

        assert_eq!(read_token(&mut input), "1");
        assert_eq!(read_token(&mut input), "->");
        assert_eq!(read_token(&mut input), "24");
        assert_eq!(read_token(&mut input), "->");
        assert_eq!(read_token(&mut input), "789");
        assert_eq!(read_token(&mut input), "[");
        assert_eq!(read_token(&mut input), "-");
        assert_eq!(read_token(&mut input), "123");
        assert_eq!(read_token(&mut input), "]");
        assert_eq!(read_token(&mut input).is_empty(), true);
    }

    #[test]
    fn number_radix_is_correctly_parsed() {
        let mut input = "numbers 1 FFh 10FFh 1010b 10o 100o 10 101 1111111111111111b";
        let parser = setup_parser();

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
        assert_eq!(read_token(&mut input).is_empty(), true);
    }

    #[test]
    fn range_is_correctly_parsed() {
        let mut input = "ranges 1:0 0:1";
        let parser = setup_parser();

        assert_eq!(read_token(&mut input), "ranges");
        assert_eq!(parser.read_irange(&mut input).unwrap(), 0..1);
        assert_eq!(parser.read_irange(&mut input).unwrap(), 1..0);
        assert_eq!(read_token(&mut input).is_empty(), true);
    }

    #[test]
    fn param_is_correctly_parsed() {
        let mut input = "$test:reg $arg:reg(0:1)";
        let parser = setup_parser();

        assert_eq!(
            parser.read_param(&mut input).unwrap(),
            Param::Symbol {
                name: "test".to_string(),
                symbol: TypedSymbolRef(0),
                limit: None
            }
        );
        assert_eq!(
            parser.read_param(&mut input).unwrap(),
            Param::Symbol {
                name: "arg".to_string(),
                symbol: TypedSymbolRef(0),
                limit: Some(0..1)
            }
        );
    }

    #[test]
    fn symbol_is_correctly_parsed() {
        let mut parser = Parser::new();

        let lines = vec![
            "#architecture a1",
            "symbol reg[2] = r0 | r1 | r2 | r3",
            "symbol test = r0 | r1 | hello:10 | world",
            "#end a1",
        ];

        for l in &lines {
            parser.accept_line(l).unwrap();
        }

        let reg = parser.arch().get_symbol_by_name("reg").unwrap().0;
        assert_eq!(reg.name, "reg");
        assert_eq!(reg.size, Some(2));

        let test = parser.arch().get_symbol_by_name("test").unwrap().0;
        assert_eq!(test.variants.get("r0"), Some(&0));
        assert_eq!(test.variants.get("r1"), Some(&1));
        assert_eq!(test.variants.get("hello"), Some(&10));
        assert_eq!(test.variants.get("world"), Some(&11));
    }

    fn parser_setup_mov() -> Parser {
        let mut parser = Parser::new();
        let mut asm = |line| parser.accept_line(line).unwrap();

        asm("#architecture a1");
        asm("symbol reg[2] = r0 | r1 | r2 | r3");
        asm("mnem mov $rd:reg, $rs:reg -> 010 $rd 1 $rs");
        asm("#end a1");

        parser
    }

    #[test]
    fn mnemonic_params_parsed_and_encoded() {
        let mut p = Parser::new();
        let mut asm = |line| p.accept_line(line).unwrap();
        let mut s = |text| String::from(text);

        asm("#architecture a1");
        asm("symbol reg[2] = r0 | r1 | r2 | r3");
        asm("mnem sum $r0:reg, $r1:reg, $r2:reg, $r3:reg, $r4:reg -> 100100 $r0 $r1 $r2 $r3 $r4");
        asm("#end a1");

        let ir = p.arch().get_ir_by_name("sum").unwrap().0;
        let (_, reg2) = p.arch().get_symbol_by_name("reg").unwrap();

        assert_eq!(ir.mnem, "sum");
        assert_eq!(ir.params.len(), 9);
        assert_eq!(ir.params[0], Param::Symbol { name: s("r0"), symbol: reg2, limit: None });
        assert_eq!(ir.params[1], Param::Token { value: s(",")});
        assert_eq!(ir.params[2], Param::Symbol { name: s("r1"), symbol: reg2, limit: None });
        assert_eq!(ir.params[3], Param::Token { value: s(",")});
        assert_eq!(ir.params[4], Param::Symbol { name: s("r2"), symbol: reg2, limit: None });
        assert_eq!(ir.params[5], Param::Token { value: s(",")});
        assert_eq!(ir.params[6], Param::Symbol { name: s("r3"), symbol: reg2, limit: None });
        assert_eq!(ir.params[7], Param::Token { value: s(",")});
        assert_eq!(ir.params[8], Param::Symbol { name: s("r4"), symbol: reg2, limit: None });

        assert_eq!(ir.encoding.len(), 6);
        assert_eq!(ir.encoding[0], Encode::Bits { value: 0b100100, size: 6 });
        assert_eq!(ir.encoding[1], Encode::Param { id: 0, part: 0..2 });
        assert_eq!(ir.encoding[2], Encode::Param { id: 1, part: 0..2 });
        assert_eq!(ir.encoding[3], Encode::Param { id: 2, part: 0..2 });
        assert_eq!(ir.encoding[4], Encode::Param { id: 3, part: 0..2 });
        assert_eq!(ir.encoding[5], Encode::Param { id: 4, part: 0..2 });
    }

    #[test]
    fn mnemonic_params_encoded() {
        let p = parser_setup_mov();

        let ir = p.arch().get_ir_by_name("mov").unwrap().0;

        assert_eq!(ir.mnem, "mov");
        assert_eq!(ir.params.len(), 3);

        assert_eq!(ir.encoding.len(), 4);
        assert_eq!(ir.encoding[0], Encode::Bits { value: 2, size: 3 });
        assert_eq!(ir.encoding[1], Encode::Param { id: 0, part: 0..2 });
        assert_eq!(ir.encoding[2], Encode::Bits { value: 1, size: 1 });
        assert_eq!(ir.encoding[3], Encode::Param { id: 1, part: 0..2 });
    }

    #[test]
    fn mnemonic_translated() {
        let mut p = parser_setup_mov();

        p.accept_line("mov r0 r1").unwrap();
        p.accept_line("mov r1 r2").unwrap();
        p.accept_line("mov r2 r3").unwrap();
        p.accept_line("mov r3 r0").unwrap();

        assert_eq!(p.program.len(), 4);
        assert_eq!(p.program[0], 0b01000101);
        assert_eq!(p.program[1], 0b01001110);
        assert_eq!(p.program[2], 0b01010111);
        assert_eq!(p.program[3], 0b01011100);
    }
}
