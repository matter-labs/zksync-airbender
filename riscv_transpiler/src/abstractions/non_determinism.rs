use std::collections::VecDeque;

#[derive(Clone, Debug)]
pub struct QuasiUARTSource {
    pub oracle: VecDeque<u32>,
    pub write_state: UartFrame,
}

impl Default for QuasiUARTSource {
    fn default() -> Self {
        Self {
            oracle: VecDeque::new(),
            write_state: UartFrame::Idle,
        }
    }
}

impl QuasiUARTSource {
    pub fn new_with_reads(reads: Vec<u32>) -> Self {
        Self {
            oracle: VecDeque::from(reads),
            write_state: UartFrame::Idle,
        }
    }

    /// A word the guest writes to the CSR: only QuasiUART frames are interpreted, and a complete
    /// message is printed to stdout; any other write is ignored.
    pub fn process_write(&mut self, value: u32) {
        if let Some(message) = self.write_state.process_write(value) {
            println!("UART: `{}`", String::from_utf8_lossy(&message));
        }
    }
}

/// The guest's debug output. A QuasiUART frame is [`UartFrame::HELLO_VALUE`], the number of
/// words that follow, the length of the message in bytes, and the bytes as little-endian words.
/// The frame ends with its last word, whatever the length says: bytes that the words do not
/// cover are dropped, and so are the words past the length.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub enum UartFrame {
    #[default]
    Idle,
    /// The word count was not sent yet
    Started,
    Words {
        remaining_words: usize,
        /// `None` until the length word arrives
        remaining_bytes: Option<usize>,
        bytes: Vec<u8>,
    },
}

/// What a write was to a [`UartFrame`]
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum UartWrite {
    /// No frame is in progress: the word is not a part of one
    NotAFrame,
    /// A word of the frame in progress
    Consumed,
    /// The last word of a frame, and the message of the frame
    Complete(Vec<u8>),
}

impl UartFrame {
    /// The word that starts a frame
    pub const HELLO_VALUE: u32 = u32::MAX;

    /// Starts a frame: the next write is its word count.
    pub fn start(&mut self) {
        *self = Self::Started;
    }

    /// Takes `value` as a word of the frame in progress, if there is one. It does not start a
    /// frame: the caller decides what [`Self::HELLO_VALUE`] means between frames, see
    /// [`Self::start`] and [`Self::process_write`].
    pub fn write(&mut self, value: u32) -> UartWrite {
        match self {
            Self::Idle => UartWrite::NotAFrame,
            Self::Started => {
                // a frame without words has no length either, and no message
                *self = if value == 0 {
                    Self::Idle
                } else {
                    Self::Words {
                        remaining_words: value as usize,
                        remaining_bytes: None,
                        bytes: Vec::new(),
                    }
                };
                UartWrite::Consumed
            }
            Self::Words {
                remaining_words,
                remaining_bytes,
                bytes,
            } => {
                *remaining_words -= 1;
                match remaining_bytes {
                    None => *remaining_bytes = Some(value as usize),
                    Some(remaining) => {
                        let take = (*remaining).min(4);
                        bytes.extend_from_slice(&value.to_le_bytes()[..take]);
                        *remaining -= take;
                    }
                }
                if *remaining_words == 0 {
                    let message = std::mem::take(bytes);
                    *self = Self::Idle;
                    UartWrite::Complete(message)
                } else {
                    UartWrite::Consumed
                }
            }
        }
    }

    /// For a source that takes nothing but frames: [`Self::HELLO_VALUE`] between frames starts
    /// one, and any other word between frames is ignored. Returns the message when `value`
    /// completes a frame.
    pub fn process_write(&mut self, value: u32) -> Option<Vec<u8>> {
        match self.write(value) {
            UartWrite::NotAFrame => {
                if value == Self::HELLO_VALUE {
                    self.start();
                }
                None
            }
            UartWrite::Consumed => None,
            UartWrite::Complete(message) => Some(message),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const HELLO: u32 = UartFrame::HELLO_VALUE;

    /// Feeds the words, and collects the messages of the frames they complete
    fn messages(frame: &mut UartFrame, words: &[u32]) -> Vec<Vec<u8>> {
        words
            .iter()
            .filter_map(|word| frame.process_write(*word))
            .collect()
    }

    #[test]
    fn a_frame_is_the_marker_the_word_count_the_length_and_the_bytes() {
        let mut frame = UartFrame::Idle;
        // "hello": 5 bytes in 2 words, after the word count (the length word included)
        assert!(messages(&mut frame, &[HELLO]).is_empty());
        assert_eq!(frame, UartFrame::Started);
        assert!(messages(&mut frame, &[3]).is_empty());
        assert_eq!(
            frame,
            UartFrame::Words {
                remaining_words: 3,
                remaining_bytes: None,
                bytes: vec![],
            }
        );
        assert!(messages(&mut frame, &[5, u32::from_le_bytes(*b"hell")]).is_empty());
        assert_eq!(
            frame,
            UartFrame::Words {
                remaining_words: 1,
                remaining_bytes: Some(1),
                bytes: b"hell".to_vec(),
            }
        );
        assert_eq!(
            messages(&mut frame, &[u32::from_le_bytes(*b"o\0\0\0")]),
            [b"hello".to_vec()]
        );
        assert_eq!(frame, UartFrame::Idle);
    }

    #[test]
    fn frames_follow_each_other() {
        let mut frame = UartFrame::Idle;
        let words = [HELLO, 2, 4, 0x1234_5678, HELLO, 2, 2, 0xffff_4142];
        assert_eq!(
            messages(&mut frame, &words),
            [vec![0x78, 0x56, 0x34, 0x12], vec![0x42, 0x41]]
        );
        assert_eq!(frame, UartFrame::Idle);
    }

    /// What the guest's `QuasiUART` sends for an empty string: the length word alone
    #[test]
    fn an_empty_message_ends_with_its_length_word() {
        let mut frame = UartFrame::Idle;
        assert_eq!(messages(&mut frame, &[HELLO, 1, 0]), [Vec::<u8>::new()]);
        assert_eq!(frame, UartFrame::Idle);
        // and the next frame is not swallowed
        assert_eq!(
            messages(&mut frame, &[HELLO, 2, 1, u32::from(b'x')]),
            [b"x".to_vec()]
        );
    }

    #[test]
    fn a_frame_without_words_has_no_message() {
        let mut frame = UartFrame::Idle;
        assert!(messages(&mut frame, &[HELLO, 0]).is_empty());
        assert_eq!(frame, UartFrame::Idle);
        // the next write is not a part of it
        assert_eq!(frame.write(7), UartWrite::NotAFrame);
    }

    #[test]
    fn the_words_bound_the_frame_whatever_the_length_says() {
        // the length promises more bytes than the words carry
        let mut frame = UartFrame::Idle;
        assert_eq!(
            messages(&mut frame, &[HELLO, 2, 100, u32::from_le_bytes(*b"abcd")]),
            [b"abcd".to_vec()]
        );
        // the words go on past the length
        assert_eq!(
            messages(
                &mut frame,
                &[HELLO, 3, 2, u32::from_le_bytes(*b"abcd"), 0x5555_5555]
            ),
            [b"ab".to_vec()]
        );
        assert_eq!(frame, UartFrame::Idle);
    }

    #[test]
    fn writes_between_frames_are_not_frames() {
        let mut frame = UartFrame::Idle;
        assert_eq!(frame.write(HELLO), UartWrite::NotAFrame);
        assert_eq!(frame, UartFrame::Idle);
        // a source of frames alone ignores them
        assert!(messages(&mut frame, &[1, 0]).is_empty());
        assert_eq!(frame, UartFrame::Idle);
    }

    #[test]
    fn the_source_takes_frames_and_ignores_other_writes() {
        let mut source = QuasiUARTSource::new_with_reads(vec![7]);
        for word in [1, HELLO, 1, 0, 2] {
            source.process_write(word);
        }
        assert_eq!(source.write_state, UartFrame::Idle);
        assert_eq!(source.oracle, [7]);
    }
}
