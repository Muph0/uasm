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

#[test]
fn arch_rv32i_jal_is_pc_relative() {
    let arch_dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("arch");

    let mut child = Command::new(cargo_bin())
        .args(["--arch=rv32i", "-I", arch_dir.to_str().unwrap(), "STDIN"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("failed to start unas");

    // jal x1, target at address 0 -> target at address 8 -> offset = +8
    // nop at address 4
    // target: nop at address 8
    {
        let stdin = child.stdin.as_mut().unwrap();
        stdin
            .write_all(b"jal ra, target\nnop\ntarget: nop\n")
            .unwrap();
    }

    let output = child.wait_with_output().unwrap();
    let stderr_str = String::from_utf8_lossy(&output.stderr);
    assert!(output.status.success(), "unas failed: {}", stderr_str);

    assert_eq!(
        output.stdout.len(),
        12,
        "Expected 12 bytes (3 instructions), got {}. stderr: {}",
        output.stdout.len(),
        stderr_str
    );

    // jal x1, +8: imm=8, encoding bits:
    //   off[20]=0, off[10:1]=0000000100, off[11]=0, off[19:12]=00000000
    //   rd=x1=00001, opcode=1101111
    // -> 0x008000EF
    let jal_word = u32::from_le_bytes(output.stdout[0..4].try_into().unwrap());
    assert_eq!(
        jal_word, 0x008000EF,
        "jal ra, target (offset +8): expected 0x008000EF, got 0x{:08X}. \
         If 0x008080EF, the jump is absolute instead of PC-relative.",
        jal_word
    );
}

#[test]
fn arch_rv32i_beq_is_pc_relative() {
    let arch_dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("arch");

    let mut child = Command::new(cargo_bin())
        .args(["--arch=rv32i", "-I", arch_dir.to_str().unwrap(), "STDIN"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("failed to start unas");

    // beq x0, x0, target at address 0 -> target at address 8 -> offset = +8
    // nop at address 4
    // target: nop at address 8
    {
        let stdin = child.stdin.as_mut().unwrap();
        stdin
            .write_all(b"beq zero, zero, target\nnop\ntarget: nop\n")
            .unwrap();
    }

    let output = child.wait_with_output().unwrap();
    let stderr_str = String::from_utf8_lossy(&output.stderr);
    assert!(output.status.success(), "unas failed: {}", stderr_str);

    assert_eq!(
        output.stdout.len(),
        12,
        "Expected 12 bytes (3 instructions), got {}. stderr: {}",
        output.stdout.len(),
        stderr_str
    );

    // beq x0, x0, +8: offset=8
    //   off[12]=0, off[10:5]=000000, rs2=00000, rs1=00000, funct3=000,
    //   off[4:1]=0100, off[11]=0, opcode=1100011
    // -> 0x00000463
    let beq_word = u32::from_le_bytes(output.stdout[0..4].try_into().unwrap());
    assert_eq!(
        beq_word, 0x00000463,
        "beq zero, zero, target (offset +8): expected 0x00000463, got 0x{:08X}. \
         If wrong, the branch may be absolute instead of PC-relative.",
        beq_word
    );
}

#[test]
fn arch_rv32im_inherits_rv32i_and_adds_mul() {
    let arch_dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("arch");

    let mut child = Command::new(cargo_bin())
        .args(["--arch=rv32im", "-I", arch_dir.to_str().unwrap(), "STDIN"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("failed to start unas");

    // Test that inherited instructions (addi) and new M instructions (mul) both work
    {
        let stdin = child.stdin.as_mut().unwrap();
        stdin
            .write_all(b"addi x1, zero, 5\nmul x2, x1, x1\n")
            .unwrap();
    }

    let output = child.wait_with_output().unwrap();
    let stderr_str = String::from_utf8_lossy(&output.stderr);
    assert!(output.status.success(), "unas failed: {}", stderr_str);

    assert_eq!(
        output.stdout.len(),
        8,
        "Expected 8 bytes (2 instructions), got {}. stderr: {}",
        output.stdout.len(),
        stderr_str
    );

    // addi x1, x0, 5 -> imm=5, rs1=x0=0, funct3=000, rd=x1=1, opcode=0010011
    // 000000000101 00000 000 00001 0010011 = 0x00500093
    let addi_word = u32::from_le_bytes(output.stdout[0..4].try_into().unwrap());
    assert_eq!(
        addi_word, 0x00500093,
        "addi x1, zero, 5: expected 0x00500093, got 0x{:08X}",
        addi_word
    );

    // mul x2, x1, x1 -> funct7=0000001, rs2=x1=1, rs1=x1=1, funct3=000, rd=x2=2, opcode=0110011
    // 0000001 00001 00001 000 00010 0110011 = 0x02108133
    let mul_word = u32::from_le_bytes(output.stdout[4..8].try_into().unwrap());
    assert_eq!(
        mul_word, 0x02108133,
        "mul x2, x1, x1: expected 0x02108133, got 0x{:08X}",
        mul_word
    );
}
