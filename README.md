# quake-bspc

[![License]][apache]
[![Latest Version]][crates.io]
[![Documentation]][docs.rs]

[License]: https://img.shields.io/crates/l/quake-bspc.svg
[apache]: LICENSE-APACHE

[Latest Version]: https://img.shields.io/crates/v/quake-bspc.svg
[crates.io]: https://crates.io/crates/quake-bspc

[Documentation]: https://docs.rs/quake-bspc/badge.svg
[docs.rs]: https://docs.rs/quake-bspc


This library wraps around the [bspc](https://github.com/bnoordhuis/bspc) Quake utility tool
to make it easier to use it from Rust.
It does so by spawning a child process and asynchronously waiting for its output.

Some features include:

- setting up a temporary directory to store input/output files in
- parsing output logs to look for errors/warnings
- streaming the output logs in real-time (via `OptionsBuilder::log_stream`)

## Links

The BSPC tool itself is not included with the library.
Instead, it needs to already exist in the filesystem before the library is used.

- Old binary downloads for v1.2: [link](https://web.archive.org/web/20011023020820/http://www.botepidemic.com:80/gladiator/download.shtml)
- Source: [bnoordhuis/bspc](https://github.com/bnoordhuis/bspc)
- Fork with more recent commits: [TTimo/bspc](https://github.com/TTimo/bspc)

## Example

Basic example showing the conversion of a Quake BSP file to a MAP file:

```rs
use bspc::{Command, Options};
use tokio_util::sync::CancellationToken;

let bsp_contents = b"...";
let result = bspc::convert(
    "./path/to/bspc.exe",
    Command::BspToMap(bsp_contents),
    Options::builder()
        .verbose(true)
        .build(),
)
.await;
match result {
    Ok(output) => {
        assert_eq!(output.files.len(), 1);
        println!("{}", output.files[0].name);
        println!("{}", String::from_utf8_lossy(&output.files[0].contents));
    }
    Err(err) => {
        println!("Conversion failed: {}", err);
    }
}
```

### Example with cancellation

The following snippet demonstrates how to cancel the conversion (in this
case, using a timeout) via the cancellation token. Note that the
cancellation is not done simply by dropping the future (as is normally done),
since we want to ensure that the child process is killed and the temporary
directory deleted before the future completes.

```rust
use bspc::{Command, Options, ConversionError};
use tokio_util::sync::CancellationToken;

let bsp_contents = b"...";
let cancel_token = CancellationToken::new();
let cancel_task = {
    let cancel_token = cancel_token.clone();
    tokio::spawn(async move {
        tokio::time::sleep(std::time::Duration::from_millis(10)).await;
        cancel_token.cancel();
    })
};
let result = bspc::convert(
    "./path/to/bspc.exe",
    Command::BspToMap(bsp_contents),
    Options::builder()
        .verbose(true)
        .cancellation_token(cancel_token)
        .build(),
)
.await;
match result {
    Ok(output) => {
        assert_eq!(output.files.len(), 1);
        println!("{}", output.files[0].name);
        println!("{}", String::from_utf8_lossy(&output.files[0].contents));
    }
    Err(ConversionError::Cancelled) => {
        println!("Conversion timed out after 10 seconds");
    }
    Err(err) => {
        println!("Conversion failed: {}", err);
    }
}
```

## License

Licensed under either of

- Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
- MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be dual licensed as above, without any
additional terms or conditions.
