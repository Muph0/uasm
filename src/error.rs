use std::fmt::Display;

#[derive(Debug, PartialEq, Eq)]
pub struct AsmError {
    pub message: String,
    pub cause: Option<Box<AsmError>>,
}
impl AsmError {
    pub fn new(text: &str) -> Self {
        Self {
            message: text.to_string(),
            cause: None,
        }
    }

    pub fn wrap_str(self, arg: &str) -> Self {
        self.wrap(arg.to_string())
    }
    pub fn wrap(self, arg: String) -> Self {
        AsmError {
            message: arg,
            cause: Some(Box::new(self)),
        }
    }
}
impl Display for AsmError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.message)?;
        if let Some(ref reason) = self.cause {
            f.write_fmt(format_args!(", {}", reason.as_ref()))?;
        } else {
            f.write_str(".");
        }
        Ok(())
    }
}
impl From<&str> for AsmError {
    fn from(value: &str) -> Self {
        AsmError::new(value)
    }
}
impl From<String> for AsmError {
    fn from(value: String) -> Self {
        AsmError {
            message: value,
            cause: None,
        }
    }
}
impl From<std::num::ParseIntError> for AsmError {
    fn from(value: std::num::ParseIntError) -> Self {
        format!("{value}").into()
    }
}
impl From<std::io::Error> for AsmError {
    fn from(value: std::io::Error) -> Self {
        format!("{value}").into()
    }
}

#[derive(Debug)]
pub struct LocError {
    pub error: AsmError,
    pub file: Option<String>,
    pub line: usize,
}
impl Display for LocError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(ref file) = self.file {
            f.write_fmt(format_args!("{}:{}: {}", file, self.line, self.error))
        } else {
            f.write_fmt(format_args!("{}", self.error))
        }
    }
}
impl From<LocError> for Vec<LocError> {
    fn from(value: LocError) -> Self {
        vec![value]
    }
}
