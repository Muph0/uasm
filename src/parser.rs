use std::{
    collections::{BTreeMap, HashMap},
    error::Error,
    fmt::{format, Debug},
    ops::Range,
    path::Path,
    process::Termination,
};

use lalrpop_util::{lexer::Token, ParseError};

use crate::grammar;

// Location ////////////////////////////////////////

#[derive(Clone)]
pub struct Loc {
    file: SourceId,
    offset: Range<usize>,
}

// symbol ////////////////////////////////////////

#[derive(Debug, Clone, Copy)]
pub struct SymbolId(usize);
#[derive(Debug)]
pub struct Symbol {
    name: String,
    size: Option<usize>,
    loc: Loc,
    variants: BTreeMap<String, SymbolVariant>,
}

pub struct SymbolVariant {
    value: isize,
    loc: Loc,
}

// mnemonics ////////////////////////////////////////

#[derive(Debug)]
pub struct Mnemonic {
    pub params: Vec<ParamDecl>,
    pub encoding: Vec<Encode>,
}

#[derive(Debug)]
pub enum ParamDecl {
    Symbol {
        name: String,
        symbol_id: SymbolId,
        limit: Option<Range<isize>>,
    },
    Token {
        value: String,
    },
}

#[derive(Debug)]
pub enum Encode {
    Bits {
        value: usize,
        length: usize,
    },
    Param {
        expr: EncodeExpr,
        bitsize: Range<usize>,
    },
}

#[derive(Debug)]
pub enum EncodeExpr {
    ParamRef(usize),
    InstrPtrValue,
    UnOp(UnOps, Box<EncodeExpr>),
    BinOp(Box<EncodeExpr>, BinOps, Box<EncodeExpr>),
    Substr(Box<EncodeExpr>, Range<usize>),
}

#[derive(Debug)]
pub enum UnOps {
    Neg,
    BitInv,
}

#[derive(Debug)]
pub enum BinOps {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    BitAnd,
    BitOr,
    BitXor,
    LAnd,
    LOr,
    Shl,
    Shr,
    Extend,
    SignExt,
}

// Errors ////////////////////////////////////////

pub enum ErrorType {
    ArchEndMismatch { arch_id: ArchId, found: String },
    SymbolAlreadyDefined { name: String },
}

// Architecture ////////////////////////////////////////

pub struct ArchId(usize);
#[derive(Debug, Default)]
pub struct Architecture {
    pub name: String,
    pub symbols: Vec<Symbol>,
    pub mnemonics: Vec<Mnemonic>,
    pub big_endian: bool,
}

#[derive(Debug, Clone, Copy)]
pub struct SourceId(usize);
#[derive(Debug)]
pub struct Source<'a> {
    filename: String,
    content: &'a str,
}

#[derive(Debug, Default)]
pub struct ParserState<'inp> {
    architectures: Vec<Architecture>,
    files: Vec<Source<'inp>>,
    current_file: Vec<SourceId>,
}

impl Debug for Loc {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("{:?}:{:?}", self.file, self.offset))
    }
}
impl Debug for SymbolVariant {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("{} @ {:?}", self.value, self.loc))
    }
}

impl ArchId {
    pub fn get<'a>(&self, p: &'a ParserState) -> &'a Architecture {
        &p.architectures[self.0]
    }
}
impl Architecture {
    pub fn find_symbol(&self, name: &str) -> Option<&Symbol> {
        self.symbols.iter().find(|s| s.name == name)
    }
}

impl SourceId {
    pub fn get<'a, 'b>(&self, p: &'a ParserState<'b>) -> &'a Source<'b> {
        &p.files[self.0]
    }
}

impl<'inp> ParserState<'inp> {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn parse(
        &mut self,
        input: Source<'inp>,
    ) -> Result<(), lalrpop_util::ParseError<usize, grammar::Token<'inp>, &'static str>> {
        self.files.push(input);
        self.current_file.push(SourceId(0));
        grammar::UnitParser::new().parse(self, &self.files[0].content)
    }

    pub fn add_architecture(&mut self, a: Architecture, fnd: &str, pos: Range<usize>) {
        let id = self.architectures.len();
        if (fnd != a.name) {
            self.error_here(ErrorType::ArchEndMismatch {
                arch_id: ArchId(id),
                found: fnd.to_string(),
            });
        }
        self.architectures.push(a);
    }

    pub fn create_symbol(
        &self,
        name: &str,
        loc: Loc,
        size: Option<usize>,
        vars: Vec<(&str, Option<usize>, Loc)>,
    ) -> Symbol {
        let mut variants = BTreeMap::new();
        let mut i: isize = -1;
        for (name, size_opt, loc) in vars {
            i = match size_opt {
                Some(n) => n as _,
                None => i + 1,
            };

            variants.insert(name.to_string(), SymbolVariant { value: i, loc });
        }
        Symbol {
            name: name.to_string(),
            size,
            variants,
            loc,
        }
    }

    pub fn add_symbol(&mut self, mut a: Architecture, new_sym: Symbol) -> Architecture {
        if let Some(s) = a.find_symbol(&new_sym.name) {
            self.error_here(ErrorType::SymbolAlreadyDefined {
                name: s.name.clone(),
            });
        }
        a.symbols.push(new_sym);
        a
    }

    pub fn add_mnemonic(&mut self, mut a: Architecture, m: Mnemonic) -> Architecture {
        a.mnemonics.push(m);
        a
    }

    pub fn add_mnemdecl_param(
        &self,
        v: Vec<ParamDecl>,
        param_name: &str,
        param_ofs: Range<usize>,
        sym_name: &str,
        sym_ofs: Range<usize>,
    ) {
    }

    /// ----
    pub fn visit_mnemdecl_param_token(&self, text: &str) -> ParamDecl {
        ParamDecl::Token {
            value: text.to_string(),
        }
    }

    pub fn visit_mnemdecl_param_sym(
        &self,
        name: &str,
        id: SymbolId,
        limit: Option<Range<isize>>,
    ) -> ParamDecl {
        ParamDecl::Symbol {
            name: name.to_string(),
            symbol_id: id,
            limit,
        }
    }

    pub fn visit_mnem_def(&mut self, name: &str, params: &[ParamDecl]) -> Encode {
        todo!()
    }

    pub fn loc(&self, offset: Range<usize>) -> Loc {
        Loc {
            file: *self.current_file.last().unwrap(),
            offset,
        }
    }

    fn error_here(&self, err_type: ErrorType) {
        todo!()
    }
}

pub fn check_bit_string<'i>(
    input: &'i str,
    offset: Range<usize>,
) -> Result<&'i str, ParseError<usize, Token<'i>, &'static str>> {
    for c in input.chars() {
        if c != '0' && c != '1' {
            return Err(ParseError::UnrecognizedToken {
                token: (offset.start, Token(1, &input), offset.end),
                expected: vec!["bit string".to_string()],
            });
        }
    }
    Ok(input)
}

fn test_parse<'a>(input: &'a str) -> ParserState {
    let mut state = ParserState::new();
    let src = Source {
        filename: "test_input".to_string(),
        content: input,
    };
    match state.parse(src) {
        Ok(_) => state,
        Err(e) => panic!("\x1b[31m{}\x1b[0m", e),
    }
}
fn dbg<T: Debug>(t: &T) -> String {
    format!("{:?}", t)
}

#[test]
fn test_parse_arch() {
    let state = test_parse(
        "

        .architecture Simple LE


        .end Simple

    ",
    );

    assert_eq!(state.architectures.len(), 1);
    assert_eq!(state.architectures[0].name, "Simple");
    assert_eq!(state.architectures[0].big_endian, false);
    assert_eq!(state.architectures[0].symbols.len(), 0);
    assert_eq!(state.architectures[0].mnemonics.len(), 0);
}

#[test]
fn test_parse_symbol() {
    let state = test_parse(
        "

        .architecture test LE
        symbol reg[2] = r0 | r1 | r2 | r3
        symbol rw_mode = READ:15 | WRITE:7 | X
        .end test

    ",
    );

    let a = &state.architectures[0];

    let variant_str = |sym: &Symbol| {
        sym.variants
            .iter()
            .map(|(name, var)| format!("{name}:{}@{:?}", var.value, var.loc))
            .collect::<Vec<_>>()
            .join(", ")
    };

    assert_eq!(a.symbols.len(), 2);
    assert_eq!(a.symbols[0].name, "reg");
    assert_eq!(a.symbols[0].size, Some(2));
    assert_eq!(
        variant_str(&a.symbols[0]),
        "r0:0@SourceId(0):56..58, r1:1@SourceId(0):61..63, r2:2@SourceId(0):66..68, r3:3@SourceId(0):71..73"
    );
    assert_eq!(dbg(&a.symbols[0].loc), "SourceId(0):47..50");

    assert_eq!(a.symbols[1].name, "rw_mode");
    assert_eq!(a.symbols[1].size, None);
    assert_eq!(
        variant_str(&a.symbols[1]),
        "READ:15@SourceId(0):99..106, WRITE:7@SourceId(0):109..116, X:8@SourceId(0):119..120"
    );
    assert_eq!(dbg(&a.symbols[1].loc), "SourceId(0):89..96");
}

#[test]
fn test_parse_mnem() {
    let state = test_parse(
        "

        .architecture test LE
        symbol reg[2] = r0 | r1 | r2 | r3

        mnem mov $a:reg, $b:reg -> 1000 $a $b

        .end test

    ",
    );

    let a = &state.architectures[0];
    let mov = &a.mnemonics[0];

    assert_eq!(dbg(&mov.params), "");
}
