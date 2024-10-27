use crate::asm::Assembler;

#[test]
fn nonexistent_include_is_reported() {
    let mut parser = Assembler::new();

    let r = parser.accept_line(".include \"garbage-nonexistent\"");

    assert!(r.is_err());
}


#[test]
fn nonexistent_macro_is_error() {
    let mut parser = Assembler::new();

    let r = parser.accept_line(".banan lopata");

    assert!(r.is_err());
}