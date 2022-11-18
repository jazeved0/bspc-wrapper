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
use abort_on_drop::ChildTask;
use std::ffi::OsString;
use std::io::Error as IoError;
use std::path::{Path, PathBuf};
use std::process::{ExitStatus, Stdio};
use tempfile::{Builder as TempFileBuilder, TempDir};
use tokio::process::Command as TokioCommand;
use tokio::sync::mpsc::Sender as MpscSender;
use tokio_util::sync::CancellationToken;

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum Command<'a> {
    MapToBsp(&'a [u8]),
    MapToAas(&'a [u8]),
    BspToMap(&'a [u8]),
    BspToBsp(&'a [u8]),
    BspToAas(&'a [u8]),
}

impl<'a> Command<'a> {
    #[must_use]
    const fn input_extension(&self) -> &'static str {
        match self {
            Command::MapToBsp(_) | Command::MapToAas(_) => "map",
            Command::BspToMap(_) | Command::BspToBsp(_) | Command::BspToAas(_) => "bsp",
        }
    }

    async fn prepare_args(
        &self,
        temp_dir: &TempDir,
    ) -> Result<(Vec<OsString>, PathBuf), ConversionError> {
        // Write the input file to a temporary file.
        let input_file_path = temp_dir
            .path()
            .join(format!("input.{}", self.input_extension()));
        let input_contents = match self {
            Command::MapToBsp(contents)
            | Command::MapToAas(contents)
            | Command::BspToMap(contents)
            | Command::BspToBsp(contents)
            | Command::BspToAas(contents) => contents,
        };
        tokio::fs::write(&input_file_path, input_contents)
            .await
            .map_err(|err| ConversionError::TempDirectoryIo(err, input_file_path.clone()))?;

        let subcommand = match self {
            Command::MapToBsp(_) => "-map2bsp",
            Command::MapToAas(_) => "-map2aas",
            Command::BspToMap(_) => "-bsp2map",
            Command::BspToBsp(_) => "-bsp2bsp",
            Command::BspToAas(_) => "-bsp2aas",
        };

        Ok((
            vec![subcommand.into(), input_file_path.clone().into()],
            input_file_path,
        ))
    }
}

#[allow(clippy::struct_excessive_bools)]
#[derive(derive_builder::Builder)]
#[builder(build_fn(name = "fallible_build"))]
pub struct Options {
    #[builder(default = "false")]
    pub verbose: bool,
    #[builder(default, setter(strip_option))]
    pub threads: Option<usize>,
    #[builder(default = "false")]
    pub no_brush_merge: bool,
    #[builder(default = "false")]
    pub no_liquids: bool,
    #[builder(default = "false")]
    pub free_bsp_tree: bool,
    #[builder(default = "false")]
    pub disable_brush_chopping: bool,
    #[builder(default = "false")]
    pub breadth_first_bsp: bool,
    #[builder(default, setter(strip_option))]
    pub cancellation_token: Option<CancellationToken>,
    #[builder(default, setter(strip_option))]
    pub log_stream: Option<MpscSender<LogLine>>,
    #[builder(setter(custom))]
    pub additional_args: Vec<OsString>,
}

impl Options {
    #[must_use]
    pub fn builder() -> OptionsBuilder {
        OptionsBuilder::default()
    }
}

impl OptionsBuilder {
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

    pub fn additional_arg<S>(&mut self, arg: S) -> &mut Self
    where
        S: Into<OsString>,
    {
        self.additional_args
            .get_or_insert_with(Vec::new)
            .push(arg.into());
        self
    }

    #[must_use]
    pub fn build(&mut self) -> Options {
        self.fallible_build()
            .expect("OptionsBuilder::build() should not fail")
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
        //    breath                               = breath first bsp building
        //    nobrushmerge                         = don't merge brushes
        //    noliquids                            = don't write liquids to map
        //    freetree                             = free the bsp tree
        //    nocsg                                = disables brush chopping
        let mut args: Vec<OsString> = Vec::new();
        if !self.verbose {
            args.push("-noverbose".into());
        }
        if let Some(threads) = self.threads {
            args.push("-threads".into());
            args.push(threads.to_string().into());
        }
        if self.no_brush_merge {
            args.push("-nobrushmerge".into());
        }
        if self.no_liquids {
            args.push("-noliquids".into());
        }
        if self.free_bsp_tree {
            args.push("-freetree".into());
        }
        if self.disable_brush_chopping {
            args.push("-nocsg".into());
        }
        if self.breadth_first_bsp {
            // [sic]
            args.push("-breath".into());
        }
        args.extend(self.additional_args);
        args
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Output {
    exit: ExitStatus,
    exit_code: Option<i32>,
    files: Vec<OutputFile>,
    args: Vec<String>,
    logs: Vec<LogLine>,
}

#[derive(Debug, thiserror::Error)]
pub enum ConversionError {
    #[error("provided path to bspc executable (\"{0}\") does not exist or is not a file")]
    ExecutableNotFound(PathBuf),
    #[error("failed to create a temporary directory to store inputs/outputs")]
    TempDirectoryCreationFailed(#[source] IoError),
    #[error("failed to read/write to the temporary directory (at \"{1}\") storing inputs/outputs")]
    TempDirectoryIo(#[source] IoError, PathBuf),
    #[error("failed to start child \"bspc\" process")]
    ProcessStartFailure(#[source] IoError),
    #[error("failed to wait for child \"bspc\" process to exit")]
    ProcessWaitFailure(#[source] IoError),
    #[error("conversion was cancelled by the cancellation token")]
    Cancelled,
    #[error("child \"bspc\" process was provided unknown argument '{unknown_argument}': full argument list: {args:?}")]
    UnknownArgument {
        unknown_argument: String,
        args: Vec<String>,
    },
    #[error("the temporary input written to \"{0}\" was not found by \"bspc\": {1:?}")]
    TemporaryInputFileNotFound(PathBuf, Output),
    #[error("child \"bspc\" process exited with a non-zero exit code: {0:?}")]
    ProcessExitFailure(Output),
    #[error("child \"bspc\" process resulted in no output files: {0:?}")]
    NoOutputFiles(Output),
    #[error("child \"bspc\" process resulted in more than 1 output file: {0:?}")]
    MultipleOutputFiles(Output),
}

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
    let (command_args, temp_input_file_path) = cmd.prepare_args(&temp_dir).await?;
    args.extend(command_args);
    args.push("-output".into());
    args.push(output_directory_path.as_os_str().to_owned());
    args.extend(option_args);

    let debug_args: Vec<String> = args
        .iter()
        .map(|arg| arg.to_string_lossy().into_owned())
        .collect::<Vec<_>>();

    // Spawn the child process
    let mut child = TokioCommand::new(executable_path)
        .env_clear()
        .current_dir(temp_dir.path())
        .stdin(Stdio::null())
        // BSPC writes all logs to stdout
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .args(args)
        .spawn()
        .map_err(ConversionError::ProcessStartFailure)?;

    let stdout = child
        .stdout
        .take()
        .expect("child should have a piped stdout stream");
    let consume_log_task: ChildTask<Result<Vec<LogLine>, IoError>> =
        ChildTask::from(tokio::spawn(async move {
            crate::logs::collect_logs(stdout, log_stream).await
        }));

    // Wait for the child process to exit, or for the cancellation token to be
    // cancelled. Use `wait` instead of `wait_with_output` because the latter
    // requires moving the child process into the future, which is incompatible
    // with cancellation.
    let exit: ExitStatus = {
        #[allow(clippy::redundant_pub_crate)]
        let cancellation_result: Result<Result<ExitStatus, IoError>, ()> = tokio::select! {
            result = child.wait() => Ok(result),
            _ = cancellation_token.cancelled() => Err(()),
        };
        match cancellation_result {
            Ok(Ok(exit)) => exit,
            Ok(Err(wait_err)) => {
                // Try to ensure the child process is killed before returning
                let _err = child.kill().await;
                return Err(ConversionError::ProcessWaitFailure(wait_err));
            }
            Err(_) => {
                // The cancellation token was cancelled, so we should kill the child
                // process.
                let _err = child.kill().await;
                return Err(ConversionError::Cancelled);
            }
        }
    };
    let log_lines = consume_log_task
        .await
        .expect("log collection task should not panic")
        .map_err(ConversionError::ProcessWaitFailure)?;

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
        exit_code: exit.code(),
        exit,
        files: output_files,
        args: debug_args,
        logs: log_lines,
    };

    if no_files_found {
        return Err(ConversionError::TemporaryInputFileNotFound(
            temp_input_file_path,
            output,
        ));
    }

    if !output.exit.success() {
        return Err(ConversionError::ProcessExitFailure(output));
    }

    if output.files.is_empty() {
        return Err(ConversionError::NoOutputFiles(output));
    }

    Ok(output)
}
