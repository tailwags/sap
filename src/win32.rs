const BACKSLASH: u16 = b'\\' as u16;
const QUOTE: u16 = b'"' as u16;
const TAB: u16 = b'\t' as u16;
const SPACE: u16 = b' ' as u16;

pub struct Args<'a> {
    code_units: &'a [u16],
    first: bool,
    index: usize,
}

impl<'a> Args<'a> {
    /// # Safety
    /// TODO
    pub const unsafe fn new(code_units: &'a [u16]) -> Self {
        Self {
            code_units,
            first: true,
            index: 0,
        }
    }

    pub const fn empty() -> Self {
        Self {
            code_units: &[],
            first: false,
            index: 0,
        }
    }

    pub fn skip_whitespace(&mut self) {
        for point in &self.code_units[self.index..] {
            if !(*point == SPACE || *point == TAB) {
                break;
            }

            self.index += 1
        }
    }
}

impl<'a> Iterator for Args<'a> {
    type Item = &'a [u16];

    // FIXME: This whole implentation relays on windows giving us the correct args, not sure how to make it better.
    fn next(&mut self) -> Option<Self::Item> {
        if self.index >= self.code_units.len() {
            return None;
        }

        if self.first {
            self.first = false;

            let mut quoted = false;
            let mut index = 0usize;

            for point in self.code_units {
                match *point {
                    // A quote mark always toggles `quoted` no matter what because
                    // there are no escape characters when parsing the executable name.
                    QUOTE => quoted = !quoted,
                    // If not `quoted` then whitespace ends argv[0].
                    SPACE | TAB if !quoted => {
                        break;
                    }
                    _ => {}
                }

                index += 1;
            }

            self.index = index;

            self.skip_whitespace();

            return Some(&self.code_units[1..index - 1]);
        }

        // dbg!(self.index);
        // dbg!(self.code_units[self.index] as u8 as char);
        // dbg!(OsString::from_wide(&self.code_units[self.index..]));

        let mut quoted = false;
        let initial_index = self.index;
        let mut index = self.index;
        let mut points_iter = self.code_units[self.index..].iter();

        while let Some(point) = points_iter.next() {
            match *point {
                SPACE | TAB if !quoted => {
                    break;
                }
                BACKSLASH => {
                    // let backslash_count = code_units.advance_while(|w| w == BACKSLASH) + 1;
                    let backlash_count = 1;
                    if points_iter.next() == Some(&QUOTE) {
                        // cur.extend(iter::repeat(BACKSLASH.get()).take(backslash_count / 2));
                        // // The quote is escaped if there are an odd number of backslashes.
                        // if backslash_count % 2 == 1 {
                        //     raw.next();
                        //     cur.push(QUOTE.get());
                        // }
                    } else {
                        // If there is no quote on the end then there is no escaping.
                        // cur.extend(iter::repeat(BACKSLASH.get()).take(backslash_count));
                    }
                }
                QUOTE if quoted => match points_iter.next() {
                    Some(&QUOTE) => {
                        // points_iter.next();
                    }
                    Some(_) => quoted = false,

                    None => break,
                },
                QUOTE => quoted = true,
                _ => {}
            }

            index += 1
        }

        self.index = index;

        self.skip_whitespace();

        return Some(&self.code_units[initial_index..index]);

        // return Some(&self.code_units[self.index..index]);

        let mut quoted = false;
        let raw = self.code_units;
        let mut iter = raw.iter().enumerate();
        let mut final_index = 0;

        while let Some((index, w)) = iter.next() {
            let w = *w;
            match w {
                // If not `quoted`, a space or tab ends the argument.
                SPACE | TAB if !quoted => {
                    final_index = index;
                    break;
                    // ret_val.push(OsString::from_wide(&cur[..]));
                    // cur.truncate(0);

                    // Skip whitespace.

                    // if !(w == SPACE || w == TAB) {
                    //     continue;
                    // }

                    // if

                    // code_units.advance_while(|w| w == SPACE || w == TAB);
                }
                // Backslashes can escape quotes or backslashes but only if consecutive backslashes are followed by a quote.
                BACKSLASH => {
                    // let backslash_count = code_units.advance_while(|w| w == BACKSLASH) + 1;
                    // if code_units.peek() == Some(QUOTE) {
                    //     cur.extend(iter::repeat(BACKSLASH.get()).take(backslash_count / 2));
                    //     // The quote is escaped if there are an odd number of backslashes.
                    //     if backslash_count % 2 == 1 {
                    //         raw.next();
                    //         cur.push(QUOTE.get());
                    //     }
                    // } else {
                    //     // If there is no quote on the end then there is no escaping.
                    //     cur.extend(iter::repeat(BACKSLASH.get()).take(backslash_count));
                    // }
                }
                // If `quoted` and not backslash escaped (see above) then a quote either
                // unsets `in_quote` or is escaped by another quote.
                QUOTE if quoted => match iter.next() {
                    // Two consecutive quotes when `quoted` produces one literal quote.
                    Some((_, &QUOTE)) => {
                        // cur.push(QUOTE);
                        // raw.next();
                        iter.next();
                    }
                    // Otherwise set `quoted`.
                    Some(_) => quoted = false,
                    // The end of the command line.
                    // Push `cur` even if empty, which we do by breaking while `quoted` is still set.
                    None => break,
                },
                // If not `quoted` and not BACKSLASH escaped (see above) then a quote sets `in_quote`.
                QUOTE => quoted = true,
                // Everything else is always taken literally.
                // _ => cur.push(w),
                _ => continue,
            }
        }

        self.index += 1;
        Some(&raw[self.index..final_index])
    }
}
