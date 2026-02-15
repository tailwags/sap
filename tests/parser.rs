use sap::{
    Argument::{Long, Short, Stdio, Value},
    Parser, Result,
};

#[test]
#[cfg(feature = "std")]
fn parser_creation() -> Result<()> {
    use sap::Parser as P;
    let parser = P::from_env()?;
    assert!(!parser.name().is_empty());

    let parser = Parser::from_arbitrary(["test"])?;
    assert_eq!(parser.name(), "test");

    let parser = Parser::from_arbitrary(["/usr/bin/program", "-v"])?;
    assert_eq!(parser.name(), "/usr/bin/program");

    assert!(Parser::from_arbitrary::<[&str; 0]>([]).is_err());
    Ok(())
}

#[test]
fn long_options() -> Result<()> {
    let mut parser = Parser::from_arbitrary(["prog", "--verbose", "--help"])?;
    assert_eq!(parser.forward()?, Some(Long("verbose")));
    assert_eq!(parser.value(), None);
    assert_eq!(parser.forward()?, Some(Long("help")));
    assert_eq!(parser.forward()?, None);
    Ok(())
}

#[test]
fn positional_args() -> Result<()> {
    let mut parser = Parser::from_arbitrary(["prog", "file1", "file2", "file3"])?;
    assert_eq!(parser.forward()?, Some(Value("file1".into())));
    assert_eq!(parser.forward()?, Some(Value("file2".into())));
    assert_eq!(parser.forward()?, Some(Value("file3".into())));
    assert_eq!(parser.forward()?, None);
    Ok(())
}

#[test]
fn stdio_argument() -> Result<()> {
    let mut parser = Parser::from_arbitrary(["prog", "-"])?;
    assert_eq!(parser.forward()?, Some(Stdio));
    assert_eq!(parser.forward()?, None);

    let mut parser = Parser::from_arbitrary(["prog", "-v", "-", "--help"])?;
    assert_eq!(parser.forward()?, Some(Short('v')));
    assert_eq!(parser.forward()?, Some(Stdio));
    assert_eq!(parser.forward()?, Some(Long("help")));
    assert_eq!(parser.forward()?, None);
    Ok(())
}

#[test]
fn double_dash_terminator() -> Result<()> {
    let mut parser = Parser::from_arbitrary(["prog", "-v", "--", "--not-an-option", "-x"])?;
    assert_eq!(parser.forward()?, Some(Short('v')));
    assert_eq!(parser.forward()?, Some(Value("--not-an-option".into())));
    assert_eq!(parser.forward()?, Some(Value("-x".into())));
    assert_eq!(parser.forward()?, None);

    let mut parser = Parser::from_arbitrary(["prog", "--"])?;
    assert_eq!(parser.forward()?, None);

    let mut parser = Parser::from_arbitrary(["prog", "--", "file1", "file2"])?;
    assert_eq!(parser.forward()?, Some(Value("file1".into())));
    assert_eq!(parser.forward()?, Some(Value("file2".into())));
    assert_eq!(parser.forward()?, None);
    Ok(())
}

#[test]
fn stdio_after_double_dash() -> Result<()> {
    let mut parser = Parser::from_arbitrary(["prog", "-", "--", "-", "file"])?;
    assert_eq!(parser.forward()?, Some(Stdio));
    assert_eq!(parser.forward()?, Some(Value("-".into())));
    assert_eq!(parser.forward()?, Some(Value("file".into())));
    assert_eq!(parser.forward()?, None);
    Ok(())
}

#[test]
fn mixed_arguments() -> Result<()> {
    let mut parser = Parser::from_arbitrary([
        "prog",
        "-abc",
        "--verbose",
        "-f",
        "file.txt",
        "--output=result.txt",
        "--",
        "pos1",
        "-x",
    ])?;

    assert_eq!(parser.forward()?, Some(Short('a')));
    assert_eq!(parser.forward()?, Some(Short('b')));
    assert_eq!(parser.forward()?, Some(Short('c')));
    assert_eq!(parser.forward()?, Some(Long("verbose")));
    assert_eq!(parser.forward()?, Some(Short('f')));
    assert_eq!(parser.forward()?, Some(Value("file.txt".into())));
    assert_eq!(parser.forward()?, Some(Long("output")));
    assert_eq!(parser.value(), Some("result.txt".to_string()));
    assert_eq!(parser.forward()?, Some(Value("pos1".into())));
    assert_eq!(parser.forward()?, Some(Value("-x".into())));
    assert_eq!(parser.forward()?, None);
    Ok(())
}

#[test]
fn gnu_style_parsing() -> Result<()> {
    let mut parser = Parser::from_arbitrary(["prog", "-a", "operand", "-b"])?;
    assert_eq!(parser.forward()?, Some(Short('a')));
    assert_eq!(parser.forward()?, Some(Value("operand".into())));
    assert_eq!(parser.forward()?, Some(Short('b')));
    assert_eq!(parser.forward()?, None);
    Ok(())
}

#[test]
fn unicode_support() -> Result<()> {
    let mut parser = Parser::from_arbitrary(["prog", "--файл=документ.txt", "-ñ"])?;
    assert_eq!(parser.forward()?, Some(Long("файл")));
    assert_eq!(parser.value(), Some("документ.txt".to_string()));
    assert_eq!(parser.forward()?, Some(Short('ñ')));
    assert_eq!(parser.forward()?, None);
    Ok(())
}

#[test]
fn empty_and_whitespace() -> Result<()> {
    let mut parser = Parser::from_arbitrary(["prog", "", "--msg=hello world"])?;
    assert_eq!(parser.forward()?, Some(Value("".into())));
    assert_eq!(parser.forward()?, Some(Long("msg")));
    assert_eq!(parser.value(), Some("hello world".to_string()));
    assert_eq!(parser.forward()?, None);
    Ok(())
}

#[test]
fn argument_into_error() {
    use sap::Argument::{Long, Short, Stdio, Value};

    assert_eq!(
        Long("test").into_error("value").to_string(),
        "unexpected argument: --test=value"
    );
    assert_eq!(
        Long("test").into_error(None::<&str>).to_string(),
        "unexpected argument: --test"
    );
    assert_eq!(
        Short('x').into_error("val").to_string(),
        "unexpected argument: -x val"
    );
    assert_eq!(
        Short('x').into_error(None::<&str>).to_string(),
        "unexpected argument: -x"
    );
    assert_eq!(
        Value("file".into()).into_error(None::<&str>).to_string(),
        "unexpected argument: file"
    );
    assert_eq!(
        Stdio.into_error(None::<&str>).to_string(),
        "unexpected argument: -"
    );
}

#[test]
fn stress_test() -> Result<()> {
    let mut parser = Parser::from_arbitrary(["prog"])?;
    assert_eq!(parser.forward()?, None);

    let long_name = "a".repeat(1000);
    let long_option = format!("--{long_name}");
    let mut parser = Parser::from_arbitrary(["prog", &long_option])?;
    if let Some(Long(name)) = parser.forward()? {
        assert_eq!(name, long_name);
    }
    Ok(())
}
