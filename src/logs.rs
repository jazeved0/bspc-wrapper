use std::borrow::Cow;
use std::io::Error as IoError;
use tokio::io::{AsyncBufReadExt as _, AsyncRead, BufReader};
use tokio::sync::mpsc::Sender as MpscSender;

const ERROR_PREFIX: &str = "ERROR: ";
const WARNING_PREFIX: &str = "WARNING: ";
const NO_FILES_FOUND: &str = "no files found";
// [sic]
const UNKNOWN_PARAMETER_PREFIX: &str = "unknows parameter ";

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum LogLine {
    Info(String),
    Warning(WarningLine),
    Error(ErrorLine),
    NoFilesFound(NoFilesFoundLine),
    UnknownArgument(UnknownArgumentLine),
}

impl From<String> for LogLine {
    #[allow(clippy::option_if_let_else)]
    fn from(line: String) -> Self {
        if let Some(error) = line.strip_prefix(ERROR_PREFIX) {
            Self::Error(ErrorLine {
                message: error.to_owned(),
            })
        } else if let Some(warning) = line.strip_prefix(WARNING_PREFIX) {
            Self::Warning(WarningLine {
                message: warning.to_owned(),
            })
        } else if line == NO_FILES_FOUND {
            Self::NoFilesFound(NoFilesFoundLine)
        } else if let Some(param) = line.strip_prefix(UNKNOWN_PARAMETER_PREFIX) {
            Self::UnknownArgument(UnknownArgumentLine {
                argument: param.to_owned(),
            })
        } else {
            Self::Info(line)
        }
    }
}

impl LogLine {
    #[must_use]
    pub fn content(&self) -> Cow<'_, str> {
        match self {
            Self::Info(content) => Cow::Borrowed(content),
            Self::Warning(line) => Cow::Owned(line.content()),
            Self::Error(line) => Cow::Owned(line.content()),
            Self::NoFilesFound(line) => Cow::Borrowed(line.content()),
            Self::UnknownArgument(line) => Cow::Owned(line.content()),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct WarningLine {
    pub message: String,
}

impl WarningLine {
    #[must_use]
    pub fn content(&self) -> String {
        format!("{}{}", WARNING_PREFIX, self.message)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct ErrorLine {
    pub message: String,
}

impl ErrorLine {
    #[must_use]
    pub fn content(&self) -> String {
        format!("{}{}", ERROR_PREFIX, self.message)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct NoFilesFoundLine;

impl NoFilesFoundLine {
    #[must_use]
    pub const fn content(self) -> &'static str {
        NO_FILES_FOUND
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct UnknownArgumentLine {
    pub argument: String,
}

impl UnknownArgumentLine {
    #[must_use]
    pub fn content(&self) -> String {
        format!("{}{}", UNKNOWN_PARAMETER_PREFIX, self.argument)
    }
}

pub(crate) async fn collect_logs(
    reader: impl AsyncRead + Unpin + Send,
    maybe_stream: Option<MpscSender<LogLine>>,
) -> Result<Vec<LogLine>, IoError> {
    let mut reader = BufReader::new(reader).lines();
    let mut log_lines: Vec<LogLine> = Vec::new();
    while let Some(line) = reader.next_line().await? {
        let log_line: LogLine = line.into();
        if let Some(stream) = &maybe_stream {
            let _err = stream.send(log_line.clone()).await;
        }
        log_lines.push(log_line);
    }

    Ok(log_lines)
}
