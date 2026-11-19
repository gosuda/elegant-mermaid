#![no_main]

use libfuzzer_sys::fuzz_target;

fuzz_target!(|source: &[u8]| {
    for block in elegant_mermaid::markdown::blocks(source) {
        assert!(block.span.start <= block.span.end && block.span.end <= source.len());
        for line in &block.lines {
            for delta in 0..line.len {
                let offset = line.block_offset + delta;
                assert_eq!(block.host_offset(offset), line.host_offset + delta);
                assert_eq!(block.source[offset], source[line.host_offset + delta]);
            }
        }
        let _ = block.host_offset(usize::MAX);
    }
});
