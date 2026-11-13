#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub enum IconPackError {
    #[error("malformed icon pack: {reason}")]
    Malformed { reason: String },
}

#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub enum RenderError {
    #[error("document has {errors} error-severity diagnostics")]
    InvalidDocument { errors: usize },
    #[error("model exceeds the limit of {limit}; actual {actual}")]
    TooLarge { limit: u32, actual: u32 },
    #[error("arithmetic overflow")]
    Overflow,
    #[error("invalid configuration: {errors} invalid entries")]
    InvalidConfig { errors: usize },
    #[error("render cancelled")]
    Cancelled,
}

#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub enum RasterError {
    #[error("image is too large: {width}x{height} pixels")]
    PixelsTooLarge { width: u32, height: u32 },
    #[error("PNG encoding failed: {message}")]
    Encode { message: String },
    #[error("invalid configuration: {errors} invalid entries")]
    InvalidConfig { errors: usize },
}

#[cfg(test)]
mod tests {
    use crate::error::{IconPackError, RasterError, RenderError};

    fn render_messages() -> Vec<String> {
        vec![
            RenderError::InvalidDocument { errors: 2 }.to_string(),
            RenderError::TooLarge {
                limit: 2000,
                actual: 2001,
            }
            .to_string(),
            RenderError::Overflow.to_string(),
            RenderError::InvalidConfig { errors: 1 }.to_string(),
            RenderError::Cancelled.to_string(),
        ]
    }

    fn raster_messages() -> Vec<String> {
        vec![
            RasterError::PixelsTooLarge {
                width: 20000,
                height: 10,
            }
            .to_string(),
            RasterError::Encode {
                message: "bad chunk".to_owned(),
            }
            .to_string(),
            RasterError::InvalidConfig { errors: 1 }.to_string(),
        ]
    }

    fn assert_non_empty_distinct(messages: &[String]) {
        for message in messages {
            assert!(
                !message.is_empty(),
                "error display message must be nonempty: message={message:?}"
            );
        }
        let mut sorted = messages.to_vec();
        sorted.sort();
        sorted.dedup();
        assert_eq!(sorted.len(), messages.len());
    }

    #[test]
    fn render_error_messages_are_non_empty_and_distinct() {
        assert_non_empty_distinct(&render_messages());
    }

    #[test]
    fn raster_error_messages_are_non_empty_and_distinct() {
        assert_non_empty_distinct(&raster_messages());
    }

    #[test]
    fn icon_pack_error_message_is_non_empty() {
        let message = IconPackError::Malformed {
            reason: "no prefix".to_owned(),
        }
        .to_string();
        assert!(
            !message.is_empty(),
            "error display message must be nonempty: message={message:?}"
        );
        assert!(
            message.contains("no prefix"),
            "icon pack error must retain its reason: message={message:?}, reason=no prefix"
        );
    }

    #[test]
    fn error_messages_carry_their_counts() {
        let document_message = RenderError::InvalidDocument { errors: 7 }.to_string();
        assert!(
            document_message.contains('7'),
            "invalid document error must retain error count 7: message={document_message:?}"
        );
        let raster_message = RasterError::PixelsTooLarge {
            width: 16385,
            height: 3,
        }
        .to_string();
        assert!(
            raster_message.contains("16385"),
            "pixel size error must retain width 16385: message={raster_message:?}"
        );
    }
}
