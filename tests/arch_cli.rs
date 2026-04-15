use std::io::Write;
use std::process::{Command, Stdio};

fn cargo_bin() -> std::path::PathBuf {
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

#[test]
fn arch_rv32i_assembles_basic_program() {
    let arch_dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("arch");

    let mut child = Command::new(cargo_bin())
        .args(["--arch=rv32i", "-I", arch_dir.to_str().unwrap(), "STDIN"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("failed to start unas");

    // Feed a small valid RISC-V program via stdin
    {
        let stdin = child.stdin.as_mut().unwrap();
        stdin
            .write_all(b"addi x1, zero, 42\nadd x2, x1, x0\n")
            .unwrap();
    }

    let output = child.wait_with_output().unwrap();

    let stderr_str = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "unas failed with status {:?}\nstderr: {}",
        output.status,
        stderr_str
    );

    // The program should produce some binary output (2 instructions * 4 bytes = 8 bytes)
    assert_eq!(
        output.stdout.len(),
        8,
        "Expected 8 bytes of output, got {}. stderr: {}",
        output.stdout.len(),
        stderr_str
    );
}

#[test]
fn arch_list_finds_rv32i() {
    let arch_dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("arch");

    let output = Command::new(cargo_bin())
        .args(["--arch-list", "-I", arch_dir.to_str().unwrap()])
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .output()
        .expect("failed to start unas");

    let stderr_str = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "unas --arch-list failed: {}",
        stderr_str
    );

    let stdout_str = String::from_utf8_lossy(&output.stdout);
    let names: Vec<&str> = stdout_str.lines().collect();
    assert!(
        names.contains(&"rv32i"),
        "Expected 'rv32i' in arch list, got: {:?}",
        names
    );
}

#[test]
fn empty_output_produces_warning_no_file() {
    let arch_dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("arch");

    let mut child = Command::new(cargo_bin())
        .args(["--arch=rv32i", "-I", arch_dir.to_str().unwrap(), "STDIN"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("failed to start unas");

    // Feed empty program (just a comment, no instructions)
    {
        let stdin = child.stdin.as_mut().unwrap();
        stdin.write_all(b"-- nothing here\n").unwrap();
    }

    let output = child.wait_with_output().unwrap();

    let stderr_str = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "unas should succeed with empty output, got: {}",
        stderr_str
    );

    // stdout should be empty (no binary output)
    assert!(
        output.stdout.is_empty(),
        "Expected no stdout output, got {} bytes",
        output.stdout.len()
    );

    // stderr should contain the warning
    assert!(
        stderr_str.contains("empty output"),
        "Expected 'empty output' warning in stderr, got: {}",
        stderr_str
    );
}

#[test]
fn arch_rv32i_lui_encodes_correct_immediate() {
    let arch_dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("arch");

    let mut child = Command::new(cargo_bin())
        .args(["--arch=rv32i", "-I", arch_dir.to_str().unwrap(), "STDIN"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("failed to start unas");

    {
        let stdin = child.stdin.as_mut().unwrap();
        stdin.write_all(b"lui x1, 12345h\nauipc x2, 1\n").unwrap();
    }

    let output = child.wait_with_output().unwrap();
    let stderr_str = String::from_utf8_lossy(&output.stderr);
    assert!(output.status.success(), "unas failed: {}", stderr_str);

    assert_eq!(
        output.stdout.len(),
        8,
        "Expected 8 bytes, got {}. stderr: {}",
        output.stdout.len(),
        stderr_str
    );

    // lui x1, 12345h -> expected encoding: 0x123450B7
    let lui_word = u32::from_le_bytes(output.stdout[0..4].try_into().unwrap());
    assert_eq!(
        lui_word, 0x123450B7,
        "lui x1, 12345h: expected 0x123450B7, got 0x{:08X}",
        lui_word
    );

    // auipc x2, 1 -> expected encoding: 0x00001117
    let auipc_word = u32::from_le_bytes(output.stdout[4..8].try_into().unwrap());
    assert_eq!(
        auipc_word, 0x00001117,
        "auipc x2, 1: expected 0x00001117, got 0x{:08X}",
        auipc_word
    );
}
