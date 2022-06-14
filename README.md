# Unicode String implementation for Rust

The goal of this project is to implement a fast `UnicodeString` type as a direct replacement for the `String` type.

The publicly available implementation of the `String` type is super fast for dealing with ASCII characters, but as we know people don't always speak English, or use ASCII characters. The `String.chars()` function in Rust does a good job of converting a `Vec<u8>` to a `Vec<char>`, but it is done in a O(n) time.

This implementation changes this behaviour and makes the operation of getting characters out of a string a O(1) operation, and makes it very similar to the way Strings work in Go Lang.
