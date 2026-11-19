# Reproduce the constructor checkpoint

Run from a disposable checkout of the delivered commit using the existing
pinned Rust 1.99.1 and Verus 0.2026.10.18.7d82994 installation. No dependency,
workspace, quota or tool change is required. The gate uses the verifier path
and tool identities in `source-start.json` and the explicit environment
overrides in the archived driver; it does not record the full inherited process
environment.

`gate.py.txt` is the exact executed constructor gate. Its import is the exact
`m1-gate-helpers.py.txt` bundled here, also byte-identical to the committed
`evidence/m1-source-receipts-final04/gate-driver.py.txt`. The helper SHA must
match `m1_gate_helpers_sha256` in this gate's `source-start.json`. Importing it
does not execute its historical M1 main routine. Only its source/tool snapshot,
runtime command list, whole-proof command, proof parser, hash and strict semantic
classification helpers are used. This gate does not select or run the old
318-case M1 control inventory.

Restore the scripts in the disposable checkout:

```sh
mkdir -p target/m1-r-final-gate target/b3c-constructor-i2
cp evidence/b3c-constructor-i2-final02/m1-gate-helpers.py.txt target/m1-r-final-gate/driver.py
cp evidence/b3c-constructor-i2-final02/gate.py.txt target/b3c-constructor-i2/reproduce.py
```

Before running, replace the single output directory literal
`evidence/b3c-constructor-i2-final02` in the private `reproduce.py` copy with a
fresh, absent evidence directory name. Preserve the committed attempt records.
This changes the reproduced driver hash only to select its new output location;
it does not change commands, sources or checks.

```sh
DEVELOPER_DIR=/Library/Developer/CommandLineTools RUSTUP_TOOLCHAIN=1.99.1 /opt/homebrew/bin/python3 target/b3c-constructor-i2/reproduce.py
```

The gate runs the four runtime lanes, requires successful actual entire-crate
`--no-cheating` verification, then runs exactly the six-case constructor control
suite. It checks that source/build inputs and recorded tools did not change,
requires fresh uniquely named semantic rejection logs, and writes its result,
source archive and artifact hashes. A selected-function success is not a whole
positive; resource/type/syntax/tool failures are not accepted controls.

`gate-artifact-sha256.json` retains the gate's original artifact map before
supplemental preservation/diagnostic/reproduction files were packaged.
`artifact-sha256.json` additionally hashes those bundled files. The root
`evidence/brotli-b3c-constructor-i2.json` binds the final package and documents.

`preservation-audit.py.txt` is the separately executed static audit. Restore it
as a private `.py` file and run it from the same checkout to compare against the
recorded M1 base. This audit does not run the verifier or establish binary
identity. `diagnostics/` contains selected-function checks and the successful
isolated distance-symbol diagnostic; these are not additional whole positives
or defect cases. The failed `final01` whole proof and its frozen source remain
in a separate immutable attempt directory; its resource failure is not counted
as a passing gate or control.
