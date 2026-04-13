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
