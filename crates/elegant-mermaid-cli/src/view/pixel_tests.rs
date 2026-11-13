use super::*;

#[test]
fn composite_samples_integer_nearest_neighbours() -> Result<(), String> {
    let image = Image {
        width: 2,
        height: 1,
        data: vec![11, 22, 33, 255, 44, 55, 66, 255],
    };
    let mut state = ViewState::new("diagram.mmd", 20, 5, Mode::Kitty);
    state.cell_w = 1;
    state.cell_h = 1;
    state.src_w = 2;
    state.src_h = 1;
    state.zoom = 200;
    state.fit = false;
    let viewer = Viewer {
        state,
        options: Options::new("elegant-light"),
        source: Vec::new(),
        image: None,
        scheduler: SchedulerState::initial(),
        colour: false,
    };
    let pixels = composite(&viewer, &image)?;
    for x in 0..4 {
        let at = (8 + x) * 4;
        let source = (x / 2) * 4;
        assert_eq!(&pixels[at..at + 4], &image.data[source..source + 4]);
    }
    Ok(())
}

#[test]
fn split_arrow_bytes_are_not_lone_escape() {
    let mut bytes = vec![0x1b];
    let mut started = None;
    assert_eq!(next_key(&mut bytes, &mut started), None);
    bytes.extend_from_slice(b"[A");
    assert_eq!(next_key(&mut bytes, &mut started).as_deref(), Some("up"));
    assert!(
        bytes.is_empty(),
        "split_arrow_bytes_are_not_lone_escape: expected {} to hold (observed false)",
        stringify!(bytes.is_empty())
    );
}
