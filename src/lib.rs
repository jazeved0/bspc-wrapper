//! This library wraps around the [bspc](https://github.com/bnoordhuis/bspc) Quake utility tool
//! to make it easier to use it from Rust.
//! It does so by spawning a child process and asynchronously waiting for its output.
//!
//! Some features include:
//! - setting up a temporary directory to store input/output files in
//! - parsing output logs to look for errors/warnings
//! - streaming the output logs in real-time (via `OptionsBuilder::log_stream`)
//!
//! # Links
//!
//! The BSPC tool itself is not included with the library.
//! Instead, it needs to already exist in the filesystem before the library is used.
//!
//! - Old binary downloads for v1.2: [link](https://web.archive.org/web/20011023020820/http://www.botepidemic.com:80/gladiator/download.shtml)
//! - Source: [bnoordhuis/bspc](https://github.com/bnoordhuis/bspc)
//! - Fork with more recent commits: [TTimo/bspc](https://github.com/TTimo/bspc)
//!
//! # Example
//!
//! Basic example showing the conversion of a Quake BSP file to a MAP file:
//!
//! ```rust
//! use bspc::{Command, Options};
//! use tokio_util::sync::CancellationToken;
//!
//! # tokio_test::block_on(async {
//! let bsp_contents = b"...";
//! let result = bspc::convert(
//!     "./test_resources/bspci386",
//!     Command::BspToMap(bsp_contents),
//!     Options::builder()
//!         .verbose(true)
//!         .build(),
//! )
//! .await;
//! match result {
//!     Ok(output) => {
//!         assert_eq!(output.files.len(), 1);
//!         println!("{}", output.files[0].name);
//!         println!("{}", String::from_utf8_lossy(&output.files[0].contents));
//!     }
//!     Err(err) => {
//!         println!("Conversion failed: {}", err);
//!     }
//! }
//! # })
//! ```
//!
//! ## Example with cancellation
//!
//! The following snippet demonstrates how to cancel the conversion (in this
//! case, using a timeout) via the cancellation token. Note that the
//! cancellation is not done simply by dropping the future (as is normally done),
//! since we want to ensure that the child process is killed and the temporary
//! directory deleted before the future completes.
//!
//! ```rust
//! use bspc::{Command, Options, ConversionError};
//! use tokio_util::sync::CancellationToken;
//!
//! # tokio_test::block_on(async {
//! let bsp_contents = b"...";
//! let cancel_token = CancellationToken::new();
//! let cancel_task = {
//!     let cancel_token = cancel_token.clone();
//!     tokio::spawn(async move {
//!         tokio::time::sleep(std::time::Duration::from_secs(10)).await;
//!         cancel_token.cancel();
//!     })
//! };
//! let result = bspc::convert(
//!     "./test_resources/bspci386",
//!     Command::BspToMap(bsp_contents),
//!     Options::builder()
//!         .verbose(true)
//!         .cancellation_token(cancel_token)
//!         .build(),
//! )
//! .await;
//! match result {
//!     Ok(output) => {
//!         assert_eq!(output.files.len(), 1);
//!         println!("{}", output.files[0].name);
//!         println!("{}", String::from_utf8_lossy(&output.files[0].contents));
//!     }
//!     Err(ConversionError::Cancelled) => {
//!         println!("Conversion timed out after 10 seconds");
//!     }
//!     Err(err) => {
//!         println!("Conversion failed: {}", err);
//!     }
//! }
//! # })
//! ```
//!

#![warn(clippy::all, clippy::pedantic, clippy::nursery)]
#![warn(
    clippy::unwrap_used,
    clippy::unimplemented,
    clippy::todo,
    clippy::str_to_string
)]
#![allow(clippy::module_name_repetitions)]

pub mod logs;

use crate::logs::{LogLine, UnknownArgumentLine};
use derive_builder::UninitializedFieldError;
use std::ffi::OsString;
use std::future::Future;
use std::io::Error as IoError;
use std::path::{Path, PathBuf};
use std::process::{Command as StdCommand, ExitStatus, Stdio};
use tempfile::{Builder as TempFileBuilder, TempDir};
use tokio::process::Command as TokioCommand;
use tokio::sync::mpsc::Sender as MpscSender;
use tokio_util::sync::CancellationToken;

/// Callback used by [`Command::Other`].
///
/// Accepts a the temporary directory that can be used to write files to.
pub type CommandArgumentBuilder = Box<
    dyn FnOnce(
            &TempDir,
        ) -> Box<
            dyn Future<Output = Result<Vec<OsString>, ConversionError>>
                + Send
                + Sync
                + Unpin
                // The builder function can't borrow the TempDir argument, but
                // this is fine because any operations on it are synchronous.
                + 'static,
        > + Send
        + Sync,
>;

/// The subcommand to pass to the BSPC executable.
///
/// If this is one of the standard subcommands (i.e. not `Other`), then the
/// command accepts a byte slice containing the contents of the input file
/// that should be converted. This library handles writing the input file to
/// a temporary directory before invoking the BSPC executable.
pub enum Command<'a> {
    /// Corresponds to the `-map2bsp` subcommand.
    MapToBsp(&'a [u8]),
    /// Corresponds to the `-map2aas` subcommand.
    MapToAas(&'a [u8]),
    /// Corresponds to the `-bsp2map` subcommand.
    BspToMap(&'a [u8]),
    /// Corresponds to the `-bsp2bsp` subcommand.
    BspToBsp(&'a [u8]),
    /// Corresponds to the `-bsp2aas` subcommand.
    BspToAas(&'a [u8]),
    /// Allows sending an arbitrary command to the BSPC executable.
    /// This is an asynchronous callback that accepts the temporary directory
    /// that can be used to write files to, and returns a future that resolves
    /// to a list of arguments to pass to the BSPC executable (or an error).
    Other(CommandArgumentBuilder),
}

impl<'a> Command<'a> {
    async fn try_into_args(self, temp_dir: &TempDir) -> Result<Vec<OsString>, ConversionError> {
        if let Command::Other(build_arguments) = self {
            build_arguments(temp_dir).await
        } else {
            let input_file_extension = match self {
                Command::MapToBsp(_) | Command::MapToAas(_) => "map",
                Command::BspToMap(_) | Command::BspToBsp(_) | Command::BspToAas(_) => "bsp",
                Command::Other(_) => unreachable!(),
            };
            let input_file_contents = match self {
                Command::MapToBsp(contents)
                | Command::MapToAas(contents)
                | Command::BspToMap(contents)
                | Command::BspToBsp(contents)
                | Command::BspToAas(contents) => contents,
                Command::Other(_) => unreachable!(),
            };
            let subcommand = match self {
                Command::MapToBsp(_) => "-map2bsp",
                Command::MapToAas(_) => "-map2aas",
                Command::BspToMap(_) => "-bsp2map",
                Command::BspToBsp(_) => "-bsp2bsp",
                Command::BspToAas(_) => "-bsp2aas",
                Command::Other { .. } => unreachable!(),
            };

            // Write the input file to a temporary file.
            let input_file_path = temp_dir
                .path()
                .join(format!("input.{}", input_file_extension));
            tokio::fs::write(&input_file_path, input_file_contents)
                .await
                .map_err(|err| ConversionError::TempDirectoryIo(err, input_file_path.clone()))?;

            let args = vec![subcommand.into(), input_file_path.clone().into()];
            Ok(args)
        }
    }
}

/// Options for the conversion process.
///
/// Some of these are passed directly to the BSPC executable.
#[allow(clippy::struct_excessive_bools)]
#[derive(derive_builder::Builder)]
#[builder(build_fn(private, name = "fallible_build", error = "PrivateOptionsBuilderError"))]
pub struct Options {
    /// Whether to use verbose logging.
    ///
    /// If this is `false`, then the `-noverbose` flag will be passed to the
    /// BSPC executable.
    #[builder(default = "false")]
    pub verbose: bool,
    /// The number of threads to use for the conversion. By default,
    /// multi-threading is disabled (equivalent to setting this to `1`).
    ///
    /// This is passed to the BSPC executable via the `-threads` flag.
    #[builder(default, setter(strip_option))]
    pub threads: Option<usize>,
    /// A cancellation token that can be used to cancel the conversion
    /// (instead of dropping the future). See the docs on [`convert`] for
    /// more information.
    #[builder(default, setter(strip_option))]
    pub cancellation_token: Option<CancellationToken>,
    /// An optional channel to send log lines to as they get logged.
    #[builder(default, setter(strip_option))]
    pub log_stream: Option<MpscSender<LogLine>>,
    /// Additional command-line arguments to pass to the BSPC executable.
    /// These are added at the end, after all other arguments.
    #[builder(default, setter(custom))]
    pub additional_args: Vec<OsString>,
    /// Whether to log the command that is being executed.
    #[builder(default = "true")]
    pub log_command: bool,
}

#[derive(Debug)]
struct PrivateOptionsBuilderError(UninitializedFieldError);

impl From<UninitializedFieldError> for PrivateOptionsBuilderError {
    fn from(err: UninitializedFieldError) -> Self {
        Self(err)
    }
}

impl Options {
    #[must_use]
    pub fn builder() -> OptionsBuilder {
        OptionsBuilder::default()
    }
}

impl OptionsBuilder {
    #[must_use]
    pub fn build(&mut self) -> Options {
        self.fallible_build()
            .expect("OptionsBuilder::build() should not fail")
    }

    /// Adds additional command-line arguments to pass to the BSPC executable.
    /// These are added at the end, after all other arguments.
    pub fn additional_args<I, S>(&mut self, args: I) -> &mut Self
    where
        I: IntoIterator<Item = S>,
        S: Into<OsString>,
    {
        self.additional_args
            .get_or_insert_with(Vec::new)
            .extend(args.into_iter().map(Into::into));
        self
    }

    /// Adds an additional command-line argument to pass to the BSPC executable.
    /// This is added at the end, after all other arguments.
    pub fn additional_arg<S>(&mut self, arg: S) -> &mut Self
    where
        S: Into<OsString>,
    {
        self.additional_args
            .get_or_insert_with(Vec::new)
            .push(arg.into());
        self
    }
}

impl Options {
    #[must_use]
    fn into_args(self) -> Vec<OsString> {
        // Available arguments on bspc 1.2
        // Switches:
        //    map2bsp <[pakfilefilter/]filefilter> = convert MAP to BSP
        //    map2aas <[pakfilefilter/]filefilter> = convert MAP to AAS
        //    bsp2map <[pakfilefilter/]filefilter> = convert BSP to MAP
        //    bsp2bsp <[pakfilefilter/]filefilter> = convert BSP to BSP
        //    bsp2aas <[pakfilefilter/]filefilter> = convert BSP to AAS
        //    output <output path>                 = set output path
        //    noverbose                            = disable verbose output
        //    threads                              = number of threads to use
        //    ... the remaining arguments depend on the version used
        let mut args: Vec<OsString> = Vec::new();
        if !self.verbose {
            args.push("-noverbose".into());
        }
        if let Some(threads) = self.threads {
            args.push("-threads".into());
            args.push(threads.to_string().into());
        }
        args.extend(self.additional_args);
        args
    }
}

/// Full output of the child process, including the exit code, log, and any
/// output files.
///
/// This also includes the command-line arguments that were passed, for
/// diagnostic purposes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Output {
    /// The exit status of the child process.
    pub exit: ExitStatus,
    /// The exit code corresponding to the exit status, if one exists.
    ///
    /// See the docs on [`std::process::ExitStatus::code`].
    pub exit_code: Option<i32>,
    /// All output files that the child process produced.
    pub files: Vec<OutputFile>,
    /// The command-line arguments that were passed to the child process.
    pub args: Vec<String>,
    /// The log output of the child process, as a list of parsed log lines.
    pub logs: Vec<LogLine>,
}

/// Error type returned by [`convert`].
#[derive(Debug, thiserror::Error)]
pub enum ConversionError {
    /// The provided path to the BSPC executable does not exist or is not a
    /// file.
    #[error("provided path to bspc executable (\"{0}\") does not exist or is not a file: {0}")]
    ExecutableNotFound(PathBuf),
    /// Failed to create a temporary directory to store inputs/outputs.
    #[error("failed to create a temporary directory to store inputs/outputs: {0}")]
    TempDirectoryCreationFailed(#[source] IoError),
    /// Failed to read/write to the temporary directory storing inputs/outputs.
    #[error(
        "failed to read/write to the temporary directory (at \"{1}\") storing inputs/outputs: {0}"
    )]
    TempDirectoryIo(#[source] IoError, PathBuf),
    /// Failed to start the child BSPC process.
    #[error("failed to start child \"bspc\" process: {0}")]
    ProcessStartFailure(#[source] IoError),
    /// Failed to wait for the child BSPC process to exit.
    #[error("failed to wait for child \"bspc\" process to exit: {0}")]
    ProcessWaitFailure(#[source] IoError),
    /// The conversion process was cancelled via the cancellation token.
    #[error("conversion was cancelled by the cancellation token")]
    Cancelled,
    /// The child BSPC process was provided an unknown argument.
    #[error("child \"bspc\" process was provided unknown argument '{unknown_argument}': full argument list: {args:?}")]
    UnknownArgument {
        /// The offending argument.
        unknown_argument: String,
        /// All arguments passed to the child BSPC process.
        args: Vec<String>,
    },
    /// The child BSPC process did find any input files when it ran.
    ///
    /// If a standard command was used, then this indicates that the temporary
    /// file may have been deleted before BPSC ran.
    #[error("\"bspc\" did not find any files when it ran the conversion process (see logs). If a standard command was used, then this indicates that the temporary file may have been deleted before \"bspc\"")]
    NoInputFilesFound(Output),
    /// The child BSPC process exited with a non-zero exit code.
    #[error("child \"bspc\" process exited with a non-zero exit code {} (see logs)", .0.exit)]
    ProcessExitFailure(Output),
    /// The child BSPC process resulted in no output files.
    #[error("child \"bspc\" process resulted in no output files (see logs)")]
    NoOutputFiles(Output),
}

/// A single output file produced by the BSPC process.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OutputFile {
    pub name: String,
    pub extension: Option<String>,
    pub contents: Vec<u8>,
}

/// Runs the BSPC executable with the given arguments, converting a single file
/// to a different format, returning the complete output of the process
/// (all output files, logs, and exit code).
///
/// The future returned by this function should be polled to completion, in
/// order to best ensure that the temporary directory is cleaned up after the
/// child process exits.
///
/// To time-out the child process operation (or otherwise cancel it), pass a
/// [`CancellationToken`] to the [`Options`] argument.
///
/// # Executable
///
/// The BSPC executable must already exist in the filesystem before calling
/// this function.
///
/// # Errors
///
/// See the variants on the [`ConversionError`] enum for more information.
#[allow(clippy::too_many_lines)]
pub async fn convert(
    executable_path: impl AsRef<Path> + Send,
    cmd: Command<'_>,
    mut options: Options,
) -> Result<Output, ConversionError> {
    let cancellation_token = options
        .cancellation_token
        .take()
        .unwrap_or_else(CancellationToken::new);
    let log_stream = options.log_stream.take();
    let log_command = options.log_command;
    let option_args = options.into_args();

    // Check to make sure that the executable path exists and is a file,
    // asynchronously.
    let executable_path = executable_path.as_ref();
    let executable_path = tokio::fs::canonicalize(executable_path)
        .await
        .map_err(|_| ConversionError::ExecutableNotFound(executable_path.to_owned()))?;
    let executable_metadata = tokio::fs::metadata(&executable_path)
        .await
        .map_err(|_| ConversionError::ExecutableNotFound(executable_path.clone()))?;
    if !executable_metadata.is_file() {
        return Err(ConversionError::ExecutableNotFound(executable_path));
    }

    // Create a temporary directory to store the input and output files,
    // and to run the executable in.
    // This may invoke synchronous I/O, but it should be very fast.
    let temp_dir = TempFileBuilder::new()
        .prefix("bspc-rs")
        .tempdir()
        .map_err(ConversionError::TempDirectoryCreationFailed)?;

    // Create the output subdirectory.
    let output_directory_path = temp_dir.path().join("output");
    tokio::fs::create_dir(&output_directory_path)
        .await
        .map_err(|e| ConversionError::TempDirectoryIo(e, output_directory_path.clone()))?;

    let mut args: Vec<OsString> = Vec::new();
    let command_args = cmd.try_into_args(&temp_dir).await?;
    args.extend(command_args);
    args.push("-output".into());
    args.push(output_directory_path.as_os_str().to_owned());
    args.extend(option_args);

    let debug_args: Vec<String> = args
        .iter()
        .map(|arg| arg.to_string_lossy().into_owned())
        .collect::<Vec<_>>();

    let mut command = StdCommand::new(executable_path);
    command
        .env_clear()
        // Use the temporary directory as the working directory, since BSPC
        // also writes a log file to the working directory.
        .current_dir(temp_dir.path())
        .stdin(Stdio::null())
        // BSPC writes all logs to stdout
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .args(args);

    #[cfg(windows)]
    {
        use std::os::windows::process::CommandExt as _;
        use windows::Win32::System::Threading::CREATE_NO_WINDOW;

        // On Windows, add the CREATE_NO_WINDOW flag to the process creation
        // flags, so that the child process does not create a console window.
        command.creation_flags(CREATE_NO_WINDOW.0);
    }

    let initial_log_lines: Vec<LogLine> = {
        let mut initial_log_lines: Vec<LogLine> = Vec::new();
        if log_command {
            let command_log_line =
                LogLine::Info(format!("> bspc {}", pretty_format_args(&debug_args)));
            if let Some(log_stream) = &log_stream {
                let _send_err = log_stream.send(command_log_line.clone()).await;
            }
            initial_log_lines.push(command_log_line);
        }
        initial_log_lines
    };

    // Spawn the child process
    let mut child = TokioCommand::from(command)
        .spawn()
        .map_err(ConversionError::ProcessStartFailure)?;

    let wait_with_output_future = async {
        let mut stdout_pipe = child
            .stdout
            .take()
            .expect("child should have a piped stdout stream");

        let wait_future = async {
            child
                .wait()
                .await
                .map_err(ConversionError::ProcessWaitFailure)
        };
        let consume_log_future = async {
            crate::logs::collect_logs(&mut stdout_pipe, log_stream)
                .await
                .map_err(ConversionError::ProcessWaitFailure)
        };

        let (exit, logs) = tokio::try_join!(wait_future, consume_log_future)?;
        let logs = {
            // Prepend initial_log_lines
            let mut constructed_logs = Vec::with_capacity(initial_log_lines.len() + logs.len());
            constructed_logs.extend(initial_log_lines);
            constructed_logs.extend(logs);
            constructed_logs
        };

        // Drop the pipe after `try_join` to mirror Tokio's implementation of
        // `Child::wait_with_output`:
        // https://github.com/tokio-rs/tokio/blob/d65826236b9/tokio/src/process/mod.rs#L1224-L1234
        drop(stdout_pipe);

        Ok((exit, logs))
    };

    let (exit_status, log_lines): (ExitStatus, Vec<LogLine>) = {
        #[allow(clippy::redundant_pub_crate)]
        let cancellation_result: Result<
            Result<(ExitStatus, Vec<LogLine>), ConversionError>,
            (),
        > = tokio::select! {
            result = wait_with_output_future => Ok(result),
            _ = cancellation_token.cancelled() => Err(()),
        };
        match cancellation_result {
            Ok(Ok((exit, log_lines))) => (exit, log_lines),
            Ok(Err(err)) => {
                // Try to ensure the child process is killed before returning
                let _err = child.kill().await;
                return Err(err);
            }
            Err(_) => {
                // The cancellation token was cancelled, so we should kill the child
                // process.
                let _err = child.kill().await;
                return Err(ConversionError::Cancelled);
            }
        }
    };

    let mut no_files_found: bool = false;
    let mut unknown_argument: Option<UnknownArgumentLine> = None;
    for line in &log_lines {
        match line {
            LogLine::UnknownArgument(unknown_argument_line) => {
                unknown_argument = Some(unknown_argument_line.clone());
            }
            LogLine::NoFilesFound(_) => {
                no_files_found = true;
            }
            _ => {}
        }
    }

    // If there was an unknown argument, return an error immediately without
    // bothering to read in the output files or return the logs/exit code.
    if let Some(line) = unknown_argument {
        return Err(ConversionError::UnknownArgument {
            unknown_argument: line.argument,
            args: debug_args,
        });
    }

    // Read in all files in the output directory
    let mut output_files: Vec<OutputFile> = Vec::new();
    let mut read_dir = tokio::fs::read_dir(&output_directory_path)
        .await
        .map_err(|err| ConversionError::TempDirectoryIo(err, output_directory_path.clone()))?;
    while let Some(entry) = read_dir
        .next_entry()
        .await
        .map_err(|err| ConversionError::TempDirectoryIo(err, output_directory_path.clone()))?
    {
        let file_name = entry.file_name().to_string_lossy().into_owned();
        let file_path = entry.path();
        let file_extension = file_path
            .extension()
            .map(|ext| ext.to_string_lossy().into_owned());

        let file_contents = tokio::fs::read(&file_path)
            .await
            .map_err(|err| ConversionError::TempDirectoryIo(err, file_path))?;
        output_files.push(OutputFile {
            name: file_name,
            extension: file_extension,
            contents: file_contents,
        });
    }

    let output = Output {
        exit_code: exit_status.code(),
        exit: exit_status,
        files: output_files,
        args: debug_args,
        logs: log_lines,
    };

    if no_files_found {
        return Err(ConversionError::NoInputFilesFound(output));
    }

    if !output.exit.success() {
        return Err(ConversionError::ProcessExitFailure(output));
    }

    if output.files.is_empty() {
        return Err(ConversionError::NoOutputFiles(output));
    }

    Ok(output)
}

/// Performs best-effort "pretty-printing" of a sequence of arguments,
/// attempting to produce an output where the placement of any special
/// (i.e. whitespace, quote, control) characters can be easily discerned.
fn pretty_format_args<I, S>(args: I) -> String
where
    I: IntoIterator<Item = S>,
    S: AsRef<str>,
{
    args.into_iter()
        .map(|a| {
            let a = a.as_ref();
            if a.contains(char::is_whitespace) || a.contains(char::is_control) || a.contains('"') {
                // This will escape any quotes/control characters in the string,
                // and wrap the string in quotes (in the style of Rust source
                // code):
                format!("{:?}", a)
            } else {
                a.to_owned()
            }
        })
        .collect::<Vec<_>>()
        .join(" ")
}
