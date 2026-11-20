# Reproduce this source-qualified B2 checkpoint

Use a disposable checkout with the existing pinned Rust 1.99.1 and Verus
0.2026.10.18.7d82994 installation. Preserve all committed evidence.

The executed whole command is recorded in `promotion-qualification.json` and
`whole-crate.log`. `whole-source-start.json` hashes every verified core input.
Every one of those source bytes matches the promoted workspace; all runtime
commands/results are recorded separately against that workspace. The tool
identities match the preceding byte gate and the post-promotion snapshot.
The complete inherited process environment is not archived.

For an independent rerun, restore `verified-core-source.tar.gz` into a fresh
`target/b3c-b2-permanent-proof03/` in the disposable checkout. Copy
`whole-source-start.json` there. Run the recorded whole command first and retain
its new output as `target/b3c-b2-permanent-proof03/whole-crate.log`. Verify the
actual entire-crate result succeeds before running any faults.

Restore `m1-gate-helpers.py.txt` as `target/m1-r-final-gate/driver.py` and
`control-driver.py.txt` as a private `.py` file. Execute the latter from the
checkout with:

```sh
DEVELOPER_DIR=/Library/Developer/CommandLineTools RUSTUP_TOOLCHAIN=1.99.1 /opt/homebrew/bin/python3 path/to/restored-control-driver.py
```

It requires that complete whole positive, verifies the core hashes, makes six
private copies and preserves each header while injecting the recorded body
fault. The unchanged strict classifier excludes resource/type/tool failures.
Use a fresh private candidate directory; do not overwrite the preserved
`controls` tree. The two restored scripts must be the exact archived bytes.

Run the four commands from `runtime-results.json` against the checkout for its
compiled-library validation. The final source/test/build closure is archived in
`final-build-inputs.tar.gz`; all mutated control source closures are retained in
`control-source.tar.gz`. `earlier-candidates.tar.gz` retains actual partial and
failed attempts, not additional whole positives or control passes.
`final-preservation-audit.py.txt` compares the checkout with the recorded parent.
