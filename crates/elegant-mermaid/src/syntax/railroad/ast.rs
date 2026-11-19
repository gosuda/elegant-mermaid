use crate::source::Span;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Notation {
    Constructor,
    Ebnf,
    Abnf,
    Peg,
}

impl Notation {
    pub const ALL: [Notation; 4] = [
        Notation::Constructor,
        Notation::Ebnf,
        Notation::Abnf,
        Notation::Peg,
    ];

    pub const fn as_str(self) -> &'static str {
        match self {
            Notation::Constructor => "railroad",
            Notation::Ebnf => "railroad-ebnf",
            Notation::Abnf => "railroad-abnf",
            Notation::Peg => "railroad-peg",
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Token {
    pub kind: String,
    pub text: String,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Value {
    pub span: Span,
    pub text: String,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MetaKind {
    Title,
    AccTitle,
    AccDescr,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Meta {
    pub span: Span,
    pub kind: MetaKind,
    pub value: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Start {
    pub span: Span,
    pub header: Token,
    pub notation: Notation,
    pub meta: Vec<Meta>,
    pub rules: Vec<Rule>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Rule {
    pub span: Span,
    pub index: usize,
    pub name: Value,
    pub body: Expression,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expression {
    RailroadSequence(RailroadSequenceExpr),
    RailroadChoice(RailroadChoiceExpr),
    RailroadOptional(RailroadOptionalExpr),
    RailroadOneOrMore(RailroadOneOrMoreExpr),
    RailroadZeroOrMore(RailroadZeroOrMoreExpr),
    RailroadTerminal(RailroadTerminalExpr),
    RailroadNonTerminal(RailroadNonTerminalExpr),
    RailroadSpecial(RailroadSpecialExpr),
    Ebnf(EbnfChoice),
    Abnf(AbnfAlternation),
    Peg(PegOrderedChoice),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RailroadSequenceExpr {
    pub span: Span,
    pub elements: Vec<Expression>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RailroadChoiceExpr {
    pub span: Span,
    pub alternatives: Vec<Expression>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RailroadOptionalExpr {
    pub span: Span,
    pub element: Box<Expression>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RailroadOneOrMoreExpr {
    pub span: Span,
    pub element: Box<Expression>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RailroadZeroOrMoreExpr {
    pub span: Span,
    pub element: Box<Expression>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RailroadTerminalExpr {
    pub span: Span,
    pub value: Value,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RailroadNonTerminalExpr {
    pub span: Span,
    pub name: Value,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RailroadSpecialExpr {
    pub span: Span,
    pub text: Value,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EbnfChoice {
    pub span: Span,
    pub alternatives: Vec<EbnfSequence>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EbnfSequence {
    pub span: Span,
    pub elements: Vec<EbnfTerm>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EbnfTerm {
    pub span: Span,
    pub base: EbnfPrimary,
    pub postfixes: Vec<EbnfPostfix>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EbnfPrimary {
    Terminal(EbnfTerminal),
    NonTerminal(EbnfNonTerminal),
    Special(EbnfSpecial),
    Group(EbnfGroup),
    Optional(EbnfOptional),
    Repetition(EbnfRepetition),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EbnfPostfix {
    Optional(EbnfOptionalPostfix),
    ZeroOrMore(EbnfZeroOrMorePostfix),
    OneOrMore(EbnfOneOrMorePostfix),
    Exception(EbnfExceptionPostfix),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EbnfTerminal {
    pub span: Span,
    pub value: Value,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EbnfNonTerminal {
    pub span: Span,
    pub name: Value,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EbnfSpecial {
    pub span: Span,
    pub text: Value,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EbnfGroup {
    pub span: Span,
    pub element: EbnfChoice,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EbnfOptional {
    pub span: Span,
    pub element: EbnfChoice,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EbnfRepetition {
    pub span: Span,
    pub element: EbnfChoice,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EbnfOptionalPostfix {
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EbnfZeroOrMorePostfix {
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EbnfOneOrMorePostfix {
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EbnfExceptionPostfix {
    pub span: Span,
    pub except: EbnfPrimary,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AbnfAlternation {
    pub span: Span,
    pub alternatives: Vec<AbnfConcatenation>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AbnfConcatenation {
    pub span: Span,
    pub elements: Vec<AbnfElement>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AbnfElement {
    pub span: Span,
    pub repeat: Option<Token>,
    pub primary: AbnfPrimary,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AbnfPrimary {
    StringLiteral(AbnfStringLiteral),
    NumVal(AbnfNumVal),
    RuleName(AbnfRuleName),
    Group(AbnfGroup),
    OptionalGroup(AbnfOptionalGroup),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AbnfStringLiteral {
    pub span: Span,
    pub value: Value,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AbnfNumVal {
    pub span: Span,
    pub value: Value,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AbnfRuleName {
    pub span: Span,
    pub name: Value,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AbnfGroup {
    pub span: Span,
    pub element: AbnfAlternation,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AbnfOptionalGroup {
    pub span: Span,
    pub element: AbnfAlternation,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PegOrderedChoice {
    pub span: Span,
    pub alternatives: Vec<PegSequence>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PegSequence {
    pub span: Span,
    pub elements: Vec<PegPrefix>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PegPrefix {
    pub span: Span,
    pub operator: Option<Token>,
    pub suffix: PegSuffix,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PegSuffix {
    pub span: Span,
    pub primary: PegPrimary,
    pub operator: Option<Token>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PegPrimary {
    Literal(PegLiteral),
    Identifier(PegIdentifier),
    Group(PegGroup),
    Any(PegAny),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PegLiteral {
    pub span: Span,
    pub value: Value,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PegIdentifier {
    pub span: Span,
    pub name: Value,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PegGroup {
    pub span: Span,
    pub element: PegOrderedChoice,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PegAny {
    pub span: Span,
}
