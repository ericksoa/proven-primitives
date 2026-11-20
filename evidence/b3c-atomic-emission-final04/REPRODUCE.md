# Reproduce the atomic-emission gate

Use a disposable checkout of the delivered commit and the already-pinned Rust
1.99.1 / Verus 0.2026.10.18.7d82994 installation. The archived gate records its
actual tool paths/hashes and explicit environment overrides; it does not record
the complete inherited process environment.

`gate.py.txt` is the exact executed driver. Its bundled
`m1-gate-helpers.py.txt` supplies the existing source/tool snapshots, command
lists, suite discovery, whole-proof parser and unchanged strict rejection
classifier. Its SHA must match `m1_gate_helpers_sha256` in `source-start.json`.
The historical M1 main function and old 318-case inventory are not executed.

Restore scripts in that disposable checkout:

```sh
mkdir -p target/m1-r-final-gate target/b3c-emission
cp evidence/b3c-atomic-emission-final04/m1-gate-helpers.py.txt target/m1-r-final-gate/driver.py
cp evidence/b3c-atomic-emission-final04/gate.py.txt target/b3c-emission/reproduce.py
```

Replace the single `evidence/b3c-atomic-emission-final04` output literal in the
private reproduction copy with a fresh absent directory. Preserve the committed
attempt. This changes the driver hash only to select its new output location.

```sh
DEVELOPER_DIR=/Library/Developer/CommandLineTools RUSTUP_TOOLCHAIN=1.99.1 /opt/homebrew/bin/python3 target/b3c-emission/reproduce.py
```

The driver runs the four runtime lanes and actual entire-crate `--no-cheating`
positive first. Only after success does it execute the three exact native
private-copy control suites, in parallel, requiring 28/6/10 unique fresh case
logs and strict semantic rejection for all 44 identities. It checks source and
tool stability and archives the actual frozen source. Selected-function checks,
resource/type/syntax failures and interrupted results do not replace the full
positive or controls.

`gate-artifact-sha256.json` preserves the gate's original artifact map;
`artifact-sha256.json` additionally covers bundled static preservation and
reproduction/diagnostic material. `preservation-audit.py.txt` can be restored and
run from the checkout to reproduce comparison against the recorded parent.
`diagnostic-manifest.json` and `diagnostics.tar.gz` preserve earlier partial
queries with their actual statuses. They do not add to gate counts.


The frozen legacy harness repairs one stale selector and uses matched selected
allowances of 300 for emission. Its terminal-control source copies temporarily
raise only `step`'s allowance from 60 to 300 for both positive and negative, then
restore the file. Production annotations, requirements, guarantees, executable
bodies and all rejection assertions/classifiers remain unchanged. See
`legacy-repair.json` and the static reconstruction audit. Historical `final01`
through `final03` statuses remain separate and must not be promoted to passes.
The accepted B2 caller fault and 24-versus-eight write inventory are separate
open findings; neither is an accepted rejection nor a completed resource proof.
