mod json;
mod ops;
mod options;
mod report;
mod response;
#[cfg(test)]
mod tests;

use options::{Op, OptionError};
use response::Response;
use wasm_bindgen::prelude::wasm_bindgen;

#[wasm_bindgen(js_name = emdCall)]
pub fn emd_call(op: &str, source: &str, options_json: &str) -> String {
    call(op, source, options_json).encode()
}

fn call(op: &str, source: &str, options_json: &str) -> Response {
    let Some(op) = Op::parse(op) else {
        return Response::rejected(&OptionError::Rejected("op".to_owned()));
    };
    match options::parse(op, options_json) {
        Ok(options) => ops::run(op, source, &options),
        Err(error) => Response::rejected(&error),
    }
}
