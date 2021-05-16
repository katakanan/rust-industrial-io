# Rust Industrial I/O for Windows

This is an experimental libiio.dll wrapper for Windows.
Based on [Rust Industrial I/O for Linux](https://github.com/fpagliughi/rust-industrial-io).
Just added [windows-dll](https://crates.io/crates/windows-dll) crate and some modifications.
Not all functions will work correctly. (I didn't check yet)

## Done
- Replaced bindings.
- Added windows-dll.
- Modified error handle.
- Added "fn autodetect_context()"

## ToDo
- Implement proper error handling
- Use this library on Windows