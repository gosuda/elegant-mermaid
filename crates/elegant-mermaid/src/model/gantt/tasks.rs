//! Task statements: tag consumption, data-field splitting, ids, and ordering.

use crate::source::Span;
use crate::syntax::gantt::ast::Task as TaskNode;
use crate::syntax::gantt::is_space;

use super::{Operand, Resolver, Row, RowKind, StartKind, Task, trim};
use crate::syntax::entities::decode_entities as label;

const C_TASK_DATA: &str = "gantt/task-data-invalid";

struct Field {
    text: String,
    span: Span,
}

type Tag = (&'static str, fn(&mut Task));

const TAGS: [Tag; 5] = [
    ("active", |t| t.active = true),
    ("done", |t| t.done = true),
    ("crit", |t| t.crit = true),
    ("milestone", |t| t.milestone = true),
    ("vert", |t| t.vert = true),
];

fn split_fields(body: &str, base: usize) -> Vec<Field> {
    let mut out = Vec::new();
    let mut from = 0;
    loop {
        let rest = body.get(from..).unwrap_or("");
        let end = rest.find(',').map_or(body.len(), |at| from + at);
        out.push(Field {
            text: body.get(from..end).unwrap_or("").to_owned(),
            span: Span {
                start: base + from,
                end: base + end,
            },
        });
        if end == body.len() {
            return out;
        }
        from = end + 1;
    }
}

impl Field {
    fn trimmed(&self) -> Self {
        let lead = self.text.len() - self.text.trim_start_matches(is_space).len();
        let body = self.text.trim_matches(is_space);
        let start = self.span.start + lead;
        Self {
            text: body.to_owned(),
            span: Span {
                start,
                end: start + body.len(),
            },
        }
    }

    fn operand(&self) -> Operand {
        Operand {
            text: self.text.clone(),
            span: self.span,
        }
    }
}

fn consume_tags(task: &mut Task, fields: Vec<Field>) -> Vec<Field> {
    let mut fields = fields.into_iter().peekable();
    loop {
        let mut matched = false;
        for (name, set) in TAGS {
            if fields.peek().is_some_and(|f| trim(&f.text) == name) {
                set(task);
                fields.next();
                matched = true;
            }
        }
        if !matched {
            return fields.collect();
        }
    }
}

impl Resolver {
    pub(super) fn add_task(&mut self, node: &TaskNode, span: Span) {
        let data = &node.data;
        let body = data.value.strip_prefix(':').unwrap_or(&data.value);
        let mut task = Task::new(
            node.text.value.clone(),
            label(trim(&node.text.value)),
            self.model.sections.len().checked_sub(1),
            span,
            data.span,
        );
        let fields = consume_tags(&mut task, split_fields(body, data.span.start + 1));
        if fields.is_empty() || fields.len() > 3 {
            self.diagnostics.push(crate::syntax::gantt::diagnostic(
                C_TASK_DATA,
                "task requires one, two, or three data fields after tags".into(),
                data.span,
            ));
            return;
        }
        let fields: Vec<Field> = fields.iter().map(Field::trimmed).collect();
        self.assign_operands(&mut task, &fields);
        if !task.vert {
            task.order = Some(self.order);
            self.order += 1;
        }
        task.owner = format!("t{}", self.model.tasks.len());
        self.model.tasks.push(task);
        let at = self.model.tasks.len() - 1;
        self.model.rows.push(Row {
            kind: RowKind::Task,
            index: at,
        });
        if let Some(added) = self.model.tasks.get(at) {
            self.ids.insert(added.id.clone(), at);
            self.last_id = Some(added.id.clone());
        }
    }

    fn assign_operands(&mut self, task: &mut Task, fields: &[Field]) {
        match fields {
            [end] => {
                task.id = self.generated_id();
                task.generated = true;
                task.start_kind = StartKind::PrevEnd;
                task.prev_id.clone_from(&self.last_id);
                task.end = end.operand();
            }
            [start, end] => {
                task.id = self.generated_id();
                task.generated = true;
                task.start = start.operand();
                task.end = end.operand();
            }
            [id, start, end] => {
                task.id.clone_from(&id.text);
                task.start = start.operand();
                task.end = end.operand();
            }
            _ => {}
        }
    }

    fn generated_id(&mut self) -> String {
        self.counter += 1;
        format!("task{}", self.counter)
    }
}
