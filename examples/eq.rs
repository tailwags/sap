use std::{ffi::OsString, os::unix::prelude::OsStrExt};

fn main() {
    let mut args = std::env::args_os().skip(1);

    while let Some(arg) = args.next() {
        dbg!(arg.to_string_lossy());
        dbg!(parse_arg(arg));
    }
}

fn parse_arg(arg: OsString) {
    if let Some(arg) = arg.as_bytes().strip_prefix(b"--") {
        if let Some(index) = arg.iter().position(|b| b == &b'=') {
            let args = arg.split_at(index);
        }
    }
}

// pub fn split_once(slice: &[u8], delimiter: u8) -> Option<(&[u8], &[u8])> {
//     let (start, end) = delimiter.into_searcher(self).next_match()?;
//     // SAFETY: `Searcher` is known to return valid indices.
//     unsafe { Some((self.get_unchecked(..start), self.get_unchecked(end..))) }
// }

struct ParsedArgs<I> {
    iter: I,
    pending_value: Option<OsString>,
}

enum ParsedArg<'a> {
    Short(u8),
    Long(&'a [u8]),
    Value(OsString),
}

impl<I> ParsedArgs<I>
where
    I: Iterator<Item = OsString>,
{
    fn new(iter: I) -> Self {
        Self {
            iter,
            pending_value: None,
        }
    }

    fn next(&mut self) -> Option<ParsedArg> {
        let arg = self.iter.next();

        if let Some(arg) = arg {
            if let Some(arg) = arg.as_bytes().strip_prefix(b"--") {
                Some(ParsedArg::Long(arg))
            } else {
                None
            }

        } else {
            None
        }
    }
}
