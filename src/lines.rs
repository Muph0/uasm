use std::io::{self, BufRead, BufReader, Read};

struct LinesWCont<R> {
    reader: BufReader<R>,
}

pub fn lines_w_continuation<F: Read>(input: F) -> impl Iterator<Item = Result<String, io::Error>> {
    LinesWCont {
        reader: BufReader::new(input),
    }
}

impl<R: Read> Iterator for LinesWCont<R> {
    type Item = Result<String, io::Error>;

    fn next(&mut self) -> Option<Self::Item> {
        let mut line = "\\".to_string();
        let mut n_total = 0;

        loop {
            let Some(last) = line.pop() else { break };

            if char::is_whitespace(last) {
                continue;
            } else if last == '\\' {
                if n_total > 0 {
                    line.push(' ');
                }
                match self.reader.read_line(&mut line) {
                    Ok(0) | Err(_) => {
                        if n_total == 0 {
                            return None;
                        }
                        break;
                    }
                    Ok(n) => n_total += n,
                }
            } else {
                line.push(last);
                break;
            }
        }

        Some(Ok(line))
    }
}

#[cfg(test)]
mod test {
    use std::io::{BufReader, Cursor};

    use crate::lines::lines_w_continuation;

    #[test]
    fn basic_lines() {
        let input = "line1\nline2\nline3\n";
        let mut lines: Vec<_> = lines_w_continuation(Cursor::new(input)).collect();

        assert_eq!(lines[0].as_ref().unwrap(), "line1");
        assert_eq!(lines[1].as_ref().unwrap(), "line2");
        assert_eq!(lines[2].as_ref().unwrap(), "line3");
        assert_eq!(lines.len(), 3);
    }

    #[test]
    fn no_newline_eof() {
        let input = "line1\nline2\nline3";
        let mut lines: Vec<_> = lines_w_continuation(Cursor::new(input)).collect();

        assert_eq!(lines[0].as_ref().unwrap(), "line1");
        assert_eq!(lines[1].as_ref().unwrap(), "line2");
        assert_eq!(lines[2].as_ref().unwrap(), "line3");
        assert_eq!(lines.len(), 3);
    }

    #[test]
    fn empty_lines() {
        let input = "line1\n\nline3\n\nline5\n";
        let mut lines: Vec<_> = lines_w_continuation(Cursor::new(input)).collect();

        assert_eq!(lines[0].as_ref().unwrap(), "line1");
        assert_eq!(lines[1].as_ref().unwrap(), "");
        assert_eq!(lines[2].as_ref().unwrap(), "line3");
        assert_eq!(lines[3].as_ref().unwrap(), "");
        assert_eq!(lines[4].as_ref().unwrap(), "line5");
        assert_eq!(lines.len(), 5);
    }

    #[test]
    fn continued_line() {
        let input = "line1\\\nstill line 1\n\\\nline2\n";
        let mut lines: Vec<_> = lines_w_continuation(Cursor::new(input)).collect();

        assert_eq!(lines[0].as_ref().unwrap(), "line1 still line 1");
        assert_eq!(lines[1].as_ref().unwrap(), " line2");
        assert_eq!(lines.len(), 2);
    }
}
