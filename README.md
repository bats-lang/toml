# toml

Minimal TOML parser for bats.toml files.

## API

- `parse(input)` — parse a TOML byte string into a dict of string keys to string values; section headers become dot-prefixed keys (e.g. `[package]` key `name` becomes `package.name`)
- Supported syntax:
  - `[section]` headers
  - `key = "value"` string values
  - `key = true` / `key = false` boolean values (stored as `"true"` / `"false"`)
- Returns `result(dict, err)` — Ok with the parsed dict, or Err on malformed input

## Dependencies

- array
- arith
- str
- result
- dict
