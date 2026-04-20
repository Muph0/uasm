use std::io::Write;
use std::process::{Command, Stdio};

fn unas_bin() -> std::path::PathBuf {
    let mut path = std::env::current_exe()
        .unwrap()
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .to_path_buf();
    path.push(if cfg!(windows) { "unas.exe" } else { "unas" });
    path
}

fn assemble_rv32i(source: &str) -> Vec<u32> {
    let arch_dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("arch");

    let mut child = Command::new(unas_bin())
        .args(["--arch=rv32i", "-I", arch_dir.to_str().unwrap(), "STDIN"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("failed to start unas");

    child
        .stdin
        .as_mut()
        .unwrap()
        .write_all(source.as_bytes())
        .unwrap();

    let output = child.wait_with_output().unwrap();
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "unas failed with status {:?}\nstderr: {}",
        output.status,
        stderr
    );
    assert_eq!(
        output.stdout.len() % 4,
        0,
        "Expected 32-bit output, got {} bytes. stderr: {}",
        output.stdout.len(),
        stderr
    );

    output
        .stdout
        .chunks_exact(4)
        .map(|chunk| u32::from_le_bytes(chunk.try_into().unwrap()))
        .collect()
}

#[test]
fn auipc_uses_pc_relative_immediate() {
    let words = assemble_rv32i("nop\nauipc x2, 8\n");

    assert_eq!(
        words,
        vec![0x00000013, 0x00008117],
        "Expected auipc literal immediate to remain unchanged in the emitted upper bits"
    );
}

#[test]
fn la_expands_to_auipc_then_addi_with_relative_low_bits() {
    let words = assemble_rv32i("nop\nla x3, 305419896\n");

    assert_eq!(
        words,
        vec![0x00000013, 0x12345197, 0x67418193],
        "Expected la to expand into PC-relative auipc/addi words"
    );
}

#[test]
fn la_label_and_auipc_emit_expected_rv32i_words() {
    let words = assemble_rv32i(
        "la a1, label:msg\n\
         auipc a2, 12345h\n\
         \n\
         jal zero, skip\n\
         msg: .db \"Hello, world\", 0\n\
         skip:\n",
    );

    assert_eq!(
        words,
        vec![
            0x00000597, 0x01058593, 0x12345617, 0x0140006F, 0x6c6c6548, 0x77202c6f, 0x646c726f,
            0x00000000,
        ],
        "Expected la label reference and auipc immediate to match the emitted rv32i program"
    );
}
