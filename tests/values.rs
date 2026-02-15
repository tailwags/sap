use sap::{
    Argument::{Long, Short, Stdio},
    Parser, Result,
};

// ── inline --option=value tests ────────────────────────────────────────────

#[test]
fn long_option_with_value() -> Result<()> {
    let mut parser = Parser::from_arbitrary(["prog", "--file=test.txt"])?;
    assert_eq!(parser.forward()?, Some(Long("file")));
    assert_eq!(parser.value(), Some("test.txt".to_string()));
    assert_eq!(parser.value(), None);
    assert_eq!(parser.forward()?, None);
    Ok(())
}

#[test]
fn long_option_empty_value() -> Result<()> {
    let mut parser = Parser::from_arbitrary(["prog", "--empty="])?;
    assert_eq!(parser.forward()?, Some(Long("empty")));
    assert_eq!(parser.value(), Some(String::new()));
    assert_eq!(parser.forward()?, None);
    Ok(())
}

#[test]
fn long_option_complex_values() -> Result<()> {
    let mut parser = Parser::from_arbitrary(["prog", "--equation=x=y+z", "--spaces=hello world"])?;

    assert_eq!(parser.forward()?, Some(Long("equation")));
    assert_eq!(parser.value(), Some("x=y+z".to_string()));

    assert_eq!(parser.forward()?, Some(Long("spaces")));
    assert_eq!(parser.value(), Some("hello world".to_string()));

    assert_eq!(parser.forward()?, None);
    Ok(())
}

#[test]
fn value_consumption() -> Result<()> {
    let mut parser = Parser::from_arbitrary(["prog", "--file=test.txt", "--verbose"])?;

    assert_eq!(parser.forward()?, Some(Long("file")));
    assert_eq!(parser.value(), Some("test.txt".to_string()));
    assert_eq!(parser.value(), None);

    assert_eq!(parser.forward()?, Some(Long("verbose")));
    parser.ignore_value();

    assert_eq!(parser.forward()?, None);
    Ok(())
}

// ── separate-argument value tests ──────────────────────────────────────────

#[test]
fn value_consumes_next_argument() -> Result<()> {
    let mut parser = Parser::from_arbitrary(["prog", "--file", "test.txt", "--output", "out.txt"])?;
    assert_eq!(parser.forward()?, Some(Long("file")));
    assert_eq!(parser.value(), Some("test.txt".to_string()));
    assert_eq!(parser.forward()?, Some(Long("output")));
    assert_eq!(parser.value(), Some("out.txt".to_string()));
    assert_eq!(parser.forward()?, None);
    Ok(())
}

#[test]
fn value_does_not_consume_options() -> Result<()> {
    let mut parser = Parser::from_arbitrary(["prog", "--file", "--other", "-x"])?;
    assert_eq!(parser.forward()?, Some(Long("file")));
    assert_eq!(parser.value(), None);
    assert_eq!(parser.forward()?, Some(Long("other")));
    assert_eq!(parser.forward()?, Some(Short('x')));
    Ok(())
}

/// Short option followed by a separate argument consumed via `value()`.
#[test]
fn value_after_short_option() {
    let mut p = Parser::from_arbitrary(["prog", "-f", "myfile.txt"]).unwrap();
    assert_eq!(p.forward().unwrap(), Some(Short('f')));
    assert_eq!(p.value(), Some("myfile.txt".to_string()));
    assert_eq!(p.forward().unwrap(), None);
}

/// After a short option, `value()` does not consume the following option flag.
#[test]
fn value_after_short_does_not_consume_option() {
    let mut p = Parser::from_arbitrary(["prog", "-f", "--other"]).unwrap();
    assert_eq!(p.forward().unwrap(), Some(Short('f')));
    assert_eq!(p.value(), None);
    assert_eq!(p.forward().unwrap(), Some(Long("other")));
}

/// `value()` does not consume `-` (the stdin marker) because it starts with `-`.
#[test]
fn value_does_not_consume_stdio_marker() {
    let mut p = Parser::from_arbitrary(["prog", "-f", "-"]).unwrap();
    assert_eq!(p.forward().unwrap(), Some(Short('f')));
    assert_eq!(p.value(), None); // '-' is not consumed
    assert_eq!(p.forward().unwrap(), Some(Stdio));
}

// ── combined-option value tests ────────────────────────────────────────────

#[test]
fn value_combined_options_return_none() -> Result<()> {
    let mut parser = Parser::from_arbitrary(["prog", "-abc"])?;
    assert_eq!(parser.forward()?, Some(Short('a')));
    assert_eq!(parser.value(), None);
    assert_eq!(parser.forward()?, Some(Short('b')));
    assert_eq!(parser.value(), None);
    Ok(())
}

/// After all flags in a combined cluster (`-abc`) are drained, `value()` can
/// consume the next non-option argument just like in any other state.
#[test]
fn value_after_combined_shorts_exhaust() {
    let mut p = Parser::from_arbitrary(["prog", "-abc", "file.txt"]).unwrap();
    p.forward().unwrap(); // 'a'
    p.forward().unwrap(); // 'b'
    p.forward().unwrap(); // 'c'
    assert_eq!(p.value(), Some("file.txt".to_string()));
}
