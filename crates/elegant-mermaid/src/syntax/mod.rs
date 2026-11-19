pub mod agentflow;
pub mod architecture;
pub mod block;
pub mod c4;
pub mod class;
pub mod config_value;
pub mod cynefin;
pub mod detect;
pub(crate) mod entities;
pub mod er;
pub mod eventmodeling;
pub mod flowchart;
pub mod gantt;
pub mod gitgraph;
pub mod info;
pub mod ishikawa;
pub mod journey;
pub mod kanban;
pub mod langium;
pub mod mindmap;
pub mod packet;
pub mod pie;
pub mod preprocess;
pub mod quadrant;
pub mod radar;
pub mod railroad;
pub mod requirement;
pub mod sankey;
pub mod sequence;
pub mod state;
pub mod swimlane;
pub mod timeline;
pub mod treemap;
pub mod treeview;
pub mod usecase;
pub mod venn;
pub mod wardley;
pub mod xychart;

#[cfg(test)]
mod layered_corpus_tests;

pub(crate) fn eol_len(b: &[u8], i: usize) -> usize {
    match b.get(i) {
        Some(b'\n') => 1,
        Some(b'\r') => {
            if b.get(i + 1) == Some(&b'\n') {
                2
            } else {
                1
            }
        }
        _ => 0,
    }
}

pub(crate) fn line_content_end(b: &[u8], from: usize, to: usize) -> usize {
    let mut j = from;
    while j < to {
        match b.get(j) {
            Some(b'\r') | Some(b'\n') => break,
            _ => j += 1,
        }
    }
    j
}

pub(crate) fn is_ws_byte(c: u8) -> bool {
    matches!(c, b' ' | b'\t' | b'\r' | b'\n')
}
