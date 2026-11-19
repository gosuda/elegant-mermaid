use super::*;

pub(super) fn zero() -> Span {
    Span { start: 0, end: 0 }
}
pub(super) fn join(a: Span, b: Span) -> Span {
    if a == zero() {
        return b;
    }
    Span {
        start: a.start.min(b.start),
        end: a.end.max(b.end),
    }
}
pub(super) fn token_span(tokens: &[Token]) -> Span {
    tokens.first().map_or(zero(), |first| Span {
        start: first.span.start,
        end: tokens.last().map_or(first.span.end, |last| last.span.end),
    })
}
pub(super) fn empty_id() -> IdString {
    IdString {
        span: zero(),
        text: String::new(),
    }
}
pub(super) fn empty_styles() -> StylesOpt {
    StylesOpt {
        span: zero(),
        styles: Vec::new(),
    }
}
pub(super) fn direction(k: K) -> bool {
    matches!(
        k,
        K::DirectionTb | K::DirectionBt | K::DirectionRl | K::DirectionLr | K::DirectionTd
    )
}
pub(super) fn quoted(k: K) -> bool {
    matches!(k, K::Str | K::MdStr)
}
pub(super) fn text_kind(k: K) -> TextKind {
    match k {
        K::Str => TextKind::String,
        K::MdStr => TextKind::Markdown,
        _ => TextKind::Plain,
    }
}
pub(super) fn id_token(k: K) -> bool {
    matches!(
        k,
        K::Num
            | K::NodeString
            | K::Down
            | K::Minus
            | K::Default
            | K::Comma
            | K::Colon
            | K::Amp
            | K::Brkt
            | K::Mult
            | K::UnicodeText
    )
}
pub(super) fn label_token(k: K) -> bool {
    matches!(
        k,
        K::Text | K::TagStart | K::TagEnd | K::UnicodeText | K::Str | K::MdStr
    )
}
pub(super) fn text_no_tags(k: K) -> bool {
    id_token(k)
        || label_token(k)
        || matches!(
            k,
            K::Space
                | K::Style
                | K::LinkStyle
                | K::ClassDef
                | K::Class
                | K::Click
                | K::Up
                | K::Subgraph
                | K::End
                | K::Graph
                | K::Dir
                | K::DirectionTb
                | K::DirectionBt
                | K::DirectionRl
                | K::DirectionLr
                | K::DirectionTd
                | K::StartLink
        )
}
pub(super) fn style_token(k: K) -> bool {
    matches!(
        k,
        K::Num | K::NodeString | K::Colon | K::Space | K::Brkt | K::Style
    )
}
pub(super) fn label_form(k: K) -> Option<LabelForm> {
    Some(match k {
        K::Sqs => LabelForm::Square,
        K::Ps => LabelForm::Round,
        K::DoubleCircleStart => LabelForm::Circle,
        K::EllipseStart => LabelForm::Ellipse,
        K::StadiumStart => LabelForm::Stadium,
        K::SubroutineStart => LabelForm::Subroutine,
        K::CylinderStart => LabelForm::Cylinder,
        K::DiamondStart => LabelForm::Diamond,
        K::TagEnd => LabelForm::Odd,
        K::TrapStart => LabelForm::Trap {
            closer: TrapCloser::Trap,
        },
        K::InvTrapStart => LabelForm::InvTrap {
            closer: TrapCloser::InvTrap,
        },
        K::VertexWithPropsStart => LabelForm::RectProps {
            field: String::new(),
            value: String::new(),
        },
        _ => return None,
    })
}
pub(super) fn closers(k: K) -> &'static [K] {
    match k {
        K::Sqs | K::TagEnd | K::VertexWithPropsStart => &[K::Sqe],
        K::Ps => &[K::Pe],
        K::DoubleCircleStart => &[K::DoubleCircleEnd],
        K::EllipseStart => &[K::EllipseEnd],
        K::StadiumStart => &[K::StadiumEnd],
        K::SubroutineStart => &[K::SubroutineEnd],
        K::CylinderStart => &[K::CylinderEnd],
        K::DiamondStart => &[K::DiamondStop],
        K::TrapStart => &[K::TrapEnd, K::InvTrapEnd],
        K::InvTrapStart => &[K::InvTrapEnd, K::TrapEnd],
        _ => &[],
    }
}
pub(super) fn closer(k: K) -> bool {
    matches!(
        k,
        K::Sqe
            | K::Pe
            | K::DiamondStop
            | K::StadiumEnd
            | K::SubroutineEnd
            | K::CylinderEnd
            | K::DoubleCircleEnd
            | K::EllipseEnd
            | K::TrapEnd
            | K::InvTrapEnd
    )
}
pub(super) fn statement_span(s: &Statement) -> Span {
    match s {
        Statement::Vertex(s) => s.span,
        Statement::Style(s) => s.span,
        Statement::ClassDef(s) => s.span,
        Statement::Class(s) => s.span,
        Statement::LinkStyle(s) => s.span,
        Statement::Click(s) => s.span,
        Statement::Subgraph(s) => s.span,
        Statement::Direction(s) => s.span,
        Statement::AccTitle(s) => s.span,
        Statement::AccDescr(s) => s.span,
        Statement::AccDescrBlock(s) => s.span,
    }
}
