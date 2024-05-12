use crate::asm::Assembler;

#[test]
fn nonexistent_include_is_reported() {
    let mut parser = Assembler::new();

    let r = parser.accept_line(".include \"garbage-nonexistent\"");

    assert!(r.is_err());
}
