use super::{
    Charset, DEFAULT_THEME, EMPTY_SOURCE_CODE, FrameData, Key, KeyEffect, Mode, Options, PanDir,
    Panel, RevisionResult, UNKNOWN_KIND_CODE, ViewState, clamp_zoom, fit_zoom, next_theme,
    origin_offset, scaled_size,
};

fn pixel_state() -> ViewState {
    ViewState {
        path: String::from("a.mmd"),
        width: 80,
        height: 24,
        mode: Mode::Kitty,
        fit: false,
        zoom: 100,
        src_w: 800,
        src_h: 400,
        ..ViewState::default()
    }
}

#[test]
fn zoom_steps_follow_the_floor_rule() {
    let state = pixel_state();
    assert_eq!(state.clone().zoom_in().zoom, 125);
    assert_eq!(state.clone().zoom_out().zoom, 80);
    let high = ViewState {
        zoom: 700,
        ..state.clone()
    };
    assert_eq!(high.zoom_in().zoom, 800);
    let low = ViewState { zoom: 12, ..state };
    assert_eq!(low.zoom_out().zoom, 10);
    assert_eq!(clamp_zoom(9), 10);
    assert_eq!(clamp_zoom(801), 800);
}

#[test]
fn zoom_is_ignored_in_cells() {
    let state = ViewState {
        mode: Mode::Cells,
        zoom: 100,
        ..pixel_state()
    };
    assert_eq!(state.clone().zoom_in(), state);
    assert_eq!(state.clone().zoom_out(), state);
}

#[test]
fn zoom_keys_leave_fit_mode() {
    let state = ViewState {
        fit: true,
        ..pixel_state()
    };
    assert!(
        !state.clone().zoom_in().fit,
        "zoom_keys_leave_fit_mode: expected {} to hold (observed false)",
        stringify!(!state.clone().zoom_in().fit)
    );
    assert!(
        !state.clone().zoom_out().fit,
        "zoom_keys_leave_fit_mode: expected {} to hold (observed false)",
        stringify!(!state.clone().zoom_out().fit)
    );
    assert!(
        state.home().fit,
        "zoom_keys_leave_fit_mode: expected {} to hold (observed false)",
        stringify!(state.home().fit)
    );
}

#[test]
fn fit_zoom_is_clamped() {
    assert_eq!(fit_zoom(800, 400, 640, 368), 80);
    assert_eq!(fit_zoom(1, 1, 640, 368), 800);
    assert_eq!(fit_zoom(100_000, 100_000, 640, 368), 10);
    assert_eq!(fit_zoom(0, 10, 640, 368), 10);
}

#[test]
fn scaled_size_rounds_up() {
    assert_eq!(scaled_size(800, 100), 800);
    assert_eq!(scaled_size(800, 125), 1000);
    assert_eq!(scaled_size(3, 33), 1);
    assert_eq!(scaled_size(3, 34), 2);
}

#[test]
fn pan_clamps_to_the_scaled_image() {
    let state = pixel_state();
    assert_eq!(state.clone().pan(PanDir::Left).offset_x, 0);
    assert_eq!(state.clone().pan(PanDir::Right).offset_x, 8);
    let wide = ViewState { zoom: 200, ..state };
    assert_eq!(wide.pan(PanDir::Right).offset_x, 8);
    let clamped = ViewState {
        zoom: 200,
        offset_x: 10_000,
        ..pixel_state()
    };
    assert_eq!(clamped.clamp_offsets().offset_x, 960);
}

#[test]
fn pan_in_cells_clamps_to_content() {
    let state = ViewState {
        mode: Mode::Cells,
        content_w: 100,
        content_h: 30,
        ..pixel_state()
    };
    assert_eq!(state.clone().pan(PanDir::Left).offset_x, 0);
    let far = ViewState {
        offset_x: 200,
        offset_y: 200,
        ..state
    };
    let clamped = far.pan(PanDir::Right);
    assert_eq!(clamped.offset_x, 20);
    assert_eq!(clamped.offset_y, 8);
}

#[test]
fn cells_home_resets_both_offsets() {
    let state = ViewState {
        mode: Mode::Cells,
        content_w: 100,
        content_h: 30,
        offset_x: 5,
        offset_y: 5,
        ..pixel_state()
    };
    let home = state.home();
    assert_eq!(home.offset_x, 0);
    assert_eq!(home.offset_y, 0);
    assert!(
        !home.fit,
        "cells_home_resets_both_offsets: expected {} to hold (observed false)",
        stringify!(!home.fit)
    );
}

#[test]
fn blocks_wrap_in_both_directions() {
    let state = ViewState {
        block: Some((1, 3)),
        ..pixel_state()
    };
    assert_eq!(state.clone().next_block().block, Some((2, 3)));
    assert_eq!(
        ViewState {
            block: Some((3, 3)),
            ..state.clone()
        }
        .next_block()
        .block,
        Some((1, 3))
    );
    assert_eq!(state.clone().prev_block().block, Some((3, 3)));
    assert_eq!(
        ViewState {
            block: Some((2, 3)),
            ..state
        }
        .prev_block()
        .block,
        Some((1, 3))
    );
    let none = ViewState {
        block: None,
        ..pixel_state()
    };
    assert_eq!(none.clone().next_block().block, None);
    assert_eq!(none.prev_block().block, None);
}

#[test]
fn theme_cycle_starts_over_on_an_unknown_theme() {
    assert_eq!(next_theme(DEFAULT_THEME), "elegant-dark");
    assert_eq!(next_theme("solarized-dark"), DEFAULT_THEME);
    assert_eq!(next_theme("forest"), DEFAULT_THEME);
    let mut options = Options::new("forest");
    let (_, effect) = ViewState::default().key(Key::Theme, &mut options);
    assert!(
        effect.edited,
        "theme_cycle_starts_over_on_an_unknown_theme: expected {} to hold (observed false)",
        stringify!(effect.edited)
    );
    assert_eq!(options.theme, DEFAULT_THEME);
}

#[test]
fn charset_toggle_edits() {
    let mut options = Options::new(DEFAULT_THEME);
    let (_, effect) = ViewState::default().key(Key::Charset, &mut options);
    assert_eq!(options.charset, Charset::Ascii);
    assert!(
        effect.edited,
        "charset_toggle_edits: expected {} to hold (observed false)",
        stringify!(effect.edited)
    );
    let (_, effect) = ViewState::default().key(Key::Charset, &mut options);
    assert_eq!(options.charset, Charset::Unicode);
    assert!(
        effect.edited,
        "charset_toggle_edits: expected {} to hold (observed false)",
        stringify!(effect.edited)
    );
}

#[test]
fn graphics_cycle_wraps_and_fits_pixel_modes() {
    let mut options = Options::new(DEFAULT_THEME);
    let cells = ViewState {
        mode: Mode::Cells,
        src_w: 100,
        src_h: 100,
        ..ViewState::default()
    };
    let (kitty, effect) = cells.key(Key::Graphics, &mut options);
    assert_eq!(kitty.mode, Mode::Kitty);
    assert!(
        kitty.fit,
        "graphics_cycle_wraps_and_fits_pixel_modes: expected {} to hold (observed false)",
        stringify!(kitty.fit)
    );
    assert!(
        effect.edited,
        "graphics_cycle_wraps_and_fits_pixel_modes: expected {} to hold (observed false)",
        stringify!(effect.edited)
    );
    let (iterm, _) = kitty.key(Key::Graphics, &mut options);
    let (sixel, _) = iterm.key(Key::Graphics, &mut options);
    let (wrapped, _) = sixel.key(Key::Graphics, &mut options);
    assert_eq!(wrapped.mode, Mode::Cells);
}

#[test]
fn panels_are_exclusive_and_escape_closes() {
    let state = ViewState::default();
    let diagnostics = state.toggle_panel(Panel::Diagnostics);
    assert_eq!(diagnostics.panel, Panel::Diagnostics);
    let keys = diagnostics.toggle_panel(Panel::Keys);
    assert_eq!(keys.panel, Panel::Keys);
    assert_eq!(keys.clone().toggle_panel(Panel::Keys).panel, Panel::None);
    assert_eq!(keys.clone().close_panel().panel, Panel::None);
    assert!(
        !keys.clone().close_panel().auto_panel,
        "panels_are_exclusive_and_escape_closes: expected {} to hold (observed false)",
        stringify!(!keys.clone().close_panel().auto_panel)
    );
    let mut options = Options::new(DEFAULT_THEME);
    let (closed, effect) = keys.key(Key::Escape, &mut options);
    assert_eq!(closed.panel, Panel::None);
    assert!(
        !effect.edited,
        "panels_are_exclusive_and_escape_closes: expected {} to hold (observed false)",
        stringify!(!effect.edited)
    );
    assert!(
        !effect.quit,
        "panels_are_exclusive_and_escape_closes: expected {} to hold (observed false)",
        stringify!(!effect.quit)
    );
}

#[test]
fn quit_sets_only_quit() {
    let mut options = Options::new(DEFAULT_THEME);
    let (_, effect) = ViewState::default().key(Key::Quit, &mut options);
    assert_eq!(
        effect,
        KeyEffect {
            edited: false,
            quit: true
        }
    );
}

#[test]
fn reload_edits_without_changing_the_frame() {
    let mut options = Options::new(DEFAULT_THEME);
    let state = pixel_state();
    let (next, effect) = state.clone().key(Key::Reload, &mut options);
    assert_eq!(next, state);
    assert!(
        effect.edited,
        "reload_edits_without_changing_the_frame: expected {} to hold (observed false)",
        stringify!(effect.edited)
    );
}

#[test]
fn resize_keeps_the_centre_in_cells() {
    let state = ViewState {
        mode: Mode::Cells,
        content_w: 200,
        content_h: 100,
        offset_x: 40,
        offset_y: 20,
        ..pixel_state()
    };
    let shrunk = state.resize(40, 12);
    assert_eq!(shrunk.offset_x, 60);
    assert_eq!(shrunk.offset_y, 26);
    let grown = shrunk.resize(80, 24);
    assert_eq!(grown.offset_x, 40);
    assert_eq!(grown.offset_y, 20);
}

#[test]
fn resize_recomputes_the_fit_only_in_fit_mode() {
    let fitted = ViewState {
        fit: true,
        ..pixel_state()
    };
    let resized = fitted.resize(40, 12);
    assert!(
        resized.fit,
        "resize_recomputes_the_fit_only_in_fit_mode: expected {} to hold (observed false)",
        stringify!(resized.fit)
    );
    assert_eq!(resized.zoom, 40);
    let manual = ViewState {
        fit: false,
        zoom: 100,
        ..pixel_state()
    };
    assert_eq!(manual.resize(40, 12).zoom, 100);
}

#[test]
fn origin_offset_centres_a_small_image() {
    assert_eq!(origin_offset(100, 300), 100);
    assert_eq!(origin_offset(300, 300), 0);
    assert_eq!(origin_offset(400, 300), 0);
}

#[test]
fn display_with_a_frame_sets_the_revision_and_clears_the_panel() {
    let mut state = ViewState {
        panel: Panel::Diagnostics,
        auto_panel: true,
        mode: Mode::Cells,
        ..pixel_state()
    };
    let mut result = RevisionResult::new(2);
    result.kind = Some(String::from("flowchart"));
    result.frame = Some(FrameData {
        text: vec![String::from("A --> B")],
        content_w: 7,
        content_h: 1,
        src_w: 448,
        src_h: 64,
    });
    state.display(&result);
    assert_eq!(state.displayed, 2);
    assert_eq!(state.frame_rev, 2);
    assert_eq!(state.kind.as_deref(), Some("flowchart"));
    assert_eq!(state.text, vec![String::from("A --> B")]);
    assert_eq!(state.content_w, 7);
    assert_eq!(state.panel, Panel::None);
    assert!(
        !state.auto_panel,
        "display_with_a_frame_sets_the_revision_and_clears_the_panel: expected {} to hold (observed false)",
        stringify!(!state.auto_panel)
    );
}

#[test]
fn display_without_a_frame_keeps_the_last_good_frame() {
    let mut state = ViewState {
        mode: Mode::Cells,
        frame_rev: 2,
        content_w: 7,
        content_h: 1,
        text: vec![String::from("A --> B")],
        ..pixel_state()
    };
    let mut result = RevisionResult::new(3);
    result.errors = 1;
    result.diagnostics = vec![String::from("error flowchart/unexpected-token 1:1 x")];
    result.error_codes = vec![String::from("flowchart/unexpected-token")];
    state.display(&result);
    assert_eq!(state.displayed, 3);
    assert_eq!(state.frame_rev, 2);
    assert_eq!(state.text, vec![String::from("A --> B")]);
    assert_eq!(state.panel, Panel::None);
    assert!(
        !state.auto_panel,
        "display_without_a_frame_keeps_the_last_good_frame: expected {} to hold (observed false)",
        stringify!(!state.auto_panel)
    );
}

#[test]
fn display_opens_the_panel_for_a_first_load_error() {
    let mut state = ViewState {
        mode: Mode::Cells,
        ..pixel_state()
    };
    let mut result = RevisionResult::new(1);
    result.errors = 1;
    result.error_codes = vec![String::from("flowchart/unexpected-token")];
    state.display(&result);
    assert_eq!(state.panel, Panel::Diagnostics);
    assert!(
        state.auto_panel,
        "display_opens_the_panel_for_a_first_load_error: expected {} to hold (observed false)",
        stringify!(state.auto_panel)
    );
}

#[test]
fn display_opens_the_panel_for_an_unknown_kind() {
    let mut state = ViewState {
        mode: Mode::Cells,
        frame_rev: 3,
        ..pixel_state()
    };
    let mut result = RevisionResult::new(4);
    result.errors = 1;
    result.error_codes = vec![String::from(UNKNOWN_KIND_CODE)];
    state.display(&result);
    assert_eq!(state.panel, Panel::Diagnostics);
    assert!(
        state.auto_panel,
        "display_opens_the_panel_for_an_unknown_kind: expected {} to hold (observed false)",
        stringify!(state.auto_panel)
    );
}

#[test]
fn display_leaves_the_empty_message_visible() {
    let mut state = ViewState {
        mode: Mode::Cells,
        ..pixel_state()
    };
    let mut result = RevisionResult::new(1);
    result.empty = true;
    result.errors = 1;
    result.error_codes = vec![String::from(EMPTY_SOURCE_CODE)];
    state.display(&result);
    assert_eq!(state.panel, Panel::None);
    assert!(
        !state.auto_panel,
        "display_leaves_the_empty_message_visible: expected {} to hold (observed false)",
        stringify!(!state.auto_panel)
    );
}

#[test]
fn display_does_not_open_a_panel_after_a_watch_loss() {
    let mut state = ViewState {
        mode: Mode::Cells,
        watch_lost: true,
        ..pixel_state()
    };
    let mut result = RevisionResult::new(1);
    result.errors = 1;
    result.error_codes = vec![String::from("flowchart/unexpected-token")];
    state.display(&result);
    assert_eq!(state.panel, Panel::None);
}

#[test]
fn size_text_uses_cells_or_scaled_pixels() {
    let cells = ViewState {
        mode: Mode::Cells,
        content_w: 12,
        content_h: 3,
        ..pixel_state()
    };
    assert_eq!(cells.size_text(), "12x3 cells");
    let pixel = pixel_state();
    assert_eq!(pixel.size_text(), "100x25 cells");
}
