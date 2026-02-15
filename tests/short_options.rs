use sap::{Argument::Short, Parser, ParsingError, Result};

#[test]
fn short_options() -> Result<()> {
    let mut parser = Parser::from_arbitrary(["prog", "-a", "-b", "-c"])?;
    assert_eq!(parser.forward()?, Some(Short('a')));
    assert_eq!(parser.forward()?, Some(Short('b')));
    assert_eq!(parser.forward()?, Some(Short('c')));
    assert_eq!(parser.forward()?, None);
    Ok(())
}

#[test]
fn short_option_clustering() -> Result<()> {
    let mut parser = Parser::from_arbitrary(["prog", "-abc"])?;
    assert_eq!(parser.forward()?, Some(Short('a')));
    assert_eq!(parser.forward()?, Some(Short('b')));
    assert_eq!(parser.forward()?, Some(Short('c')));
    assert_eq!(parser.forward()?, None);
    Ok(())
}

#[test]
fn short_option_special_chars() -> Result<()> {
    let mut parser = Parser::from_arbitrary(["prog", "-1", "-@", "-ñ"])?;
    assert_eq!(parser.forward()?, Some(Short('1')));
    assert_eq!(parser.forward()?, Some(Short('@')));
    assert_eq!(parser.forward()?, Some(Short('ñ')));
    assert_eq!(parser.forward()?, None);
    Ok(())
}

#[test]
fn short_option_equals_error() -> Result<()> {
    let mut parser = Parser::from_arbitrary(["prog", "-x=value"])?;
    assert_eq!(parser.forward()?, Some(Short('x')));
    let err = parser.forward().unwrap_err();
    assert_eq!(
        err,
        ParsingError::InvalidSyntax {
            reason: "Short options do not support values"
        }
    );
    Ok(())
}
