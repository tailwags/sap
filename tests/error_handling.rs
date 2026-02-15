use sap::{Argument::Short, Parser, Result};

// ── unconsumed value / poisoning ───────────────────────────────────────────

#[test]
fn unconsumed_value_error() -> Result<()> {
    let mut parser = Parser::from_arbitrary(["prog", "--file=test.txt", "--verbose"])?;
    assert_eq!(parser.forward()?, Some(sap::Argument::Long("file")));
    assert!(parser.forward().is_err());
    Ok(())
}

/// Verifies the full `is_poisoned()` lifecycle: false before any error, true
/// after an unconsumed-value error, and `forward()` returns `Ok(None)` once poisoned.
#[test]
fn is_poisoned_lifecycle() {
    let mut p = Parser::from_arbitrary(["prog", "--file=test", "--next"]).unwrap();
    assert!(!p.is_poisoned());

    p.forward().unwrap(); // Long("file") – leaves LeftoverValue state

    assert!(p.forward().is_err()); // UnconsumedValue error → parser poisoned
    assert!(p.is_poisoned());

    assert_eq!(p.forward().unwrap(), None); // poisoned → Ok(None), no panic
}

// ── has_leftover_value ─────────────────────────────────────────────────────

/// `has_leftover_value()` is false initially, true after parsing `--option=value`,
/// and false again after calling `value()` to consume it.
#[test]
fn has_leftover_value_transitions() {
    let mut p = Parser::from_arbitrary(["prog", "--file=test.txt"]).unwrap();
    assert!(!p.has_leftover_value());

    p.forward().unwrap(); // Long("file") with leftover "test.txt"
    assert!(p.has_leftover_value());

    let _ = p.value(); // consume the leftover
    assert!(!p.has_leftover_value());
}

// ── into_inner ─────────────────────────────────────────────────────────────

#[test]
fn into_inner() -> Result<()> {
    let mut parser = Parser::from_arbitrary(["prog", "-v", "remaining1", "remaining2"])?;
    assert_eq!(parser.forward()?, Some(Short('v')));

    let remaining: Vec<_> = parser.into_inner().collect();
    assert_eq!(remaining, ["remaining1", "remaining2"]);
    Ok(())
}

/// After the parser is poisoned by an error, `into_inner()` still yields the
/// arguments that were not yet consumed from the underlying iterator.
#[test]
fn into_inner_after_poison() {
    let mut p = Parser::from_arbitrary(["prog", "--file=test", "remaining"]).unwrap();

    p.forward().unwrap(); // Long("file")
    assert!(p.forward().is_err()); // UnconsumedValue → poison

    assert!(p.is_poisoned());

    let rest: Vec<_> = p.into_inner().collect();
    assert_eq!(rest, ["remaining"]);
}
