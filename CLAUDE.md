# toml

## parse-limits: parse cuts silently, parse_whole says so

`parse` copies at most TOML_MAX_BUF bytes and keeps at most TOML_MAX_ENTRIES
entries (a [section] header is an entry), and returns ok with no sign that
anything was left out, so a caller cannot tell a cut document from a whole
one. `parse_whole` is the form that says so: its type has `Whole`,
`Too_many_bytes` and `Too_many_entries`. Package API changes are additive,
so `parse` stays for one published version and is removed by
bats-lang/toml#48; the test `tests/dynamic/limits` calls it, so an edit
cannot drop it early.
