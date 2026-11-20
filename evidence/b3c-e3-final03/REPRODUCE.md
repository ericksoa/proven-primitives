# Reproduce the E3 checkpoint

Use a disposable checkout of the delivered commit and the existing pinned Rust
1.99.1 / Verus 0.2026.10.18.7d82994 stack. Preserve the committed evidence.

`gate.py.txt` is the exact executed driver. Its bundled `m1-gate-helpers.py.txt`
supplies the existing source/tool snapshots, runtime/whole commands, control
inventory parser and unchanged strict semantic classifier. It is byte-identical
to the previously committed M1 driver and is imported without executing its
historical M1 main routine or 318-case inventory.

Restore the helper as `target/m1-r-final-gate/driver.py` and the driver as a
private `.py` file. Replace only its one output directory literal with a fresh
absent evidence directory. Run from the checkout:

```sh
DEVELOPER_DIR=/Library/Developer/CommandLineTools RUSTUP_TOOLCHAIN=1.99.1 /opt/homebrew/bin/python3 path/to/restored-gate.py
```

It runs the four actual runtime lanes, then the actual entire crate with
`--no-cheating`. Only after that succeeds does it run all four native private-copy
fault suites. Cases, suite-body hashes and counts are discovered and frozen in
`required-controls.json`. Every accepted case requires a fresh actual log and
the strict classifier; source/build inputs and tool hashes must remain stable.
The script records explicit overrides and tool identities, not every inherited
environment variable.

The preserved native harness uses matched solver effort for positive/negative
copies. The older terminal-control copies temporarily use allowance 300 and
are restored after each query; production `step` stays at 60. Emission-root
queries use 300 as in the whole gate. No contract, assertion or classifier is
relaxed. See the frozen final test source and harness-adaptation records.

`audit-preservation.py.txt` and the baseline source archive reproduce the
constrained-diff, counter-origin and ordering audit. `static-origin-guards.json`
records three static negative guards; they do not add semantic-verifier cases.
For the two static audits, restore their `.py.txt` files as `.py` files in
`target/b3c-e3/`. Extract `baseline-source.tar.gz` into that directory so the
files live under `target/b3c-e3/baseline/`. Copy `baseline.json`,
`local-proof-bindings.json`, `advisory-harness-update.json`,
`retained-checker-effort.json` and `legacy-control-adaptations.json` there too.
With the helper restored as above, run `audit-preservation.py` and
`audit-harness.py` from the repository root using the same prefixed Python
command. They reproduce the full source audit and the byte-exact reconstruction
of the existing test source.

`diagnostics.tar.gz` retains earlier selected/provisional source, logs and
controller results. `historical-attempts.json` binds failed/interrupted full
gates separately. None of that diagnostic material adds to final gate totals.

`gate-artifact-sha256.json` is the gate's original artifact map;
`artifact-sha256.json` also covers the preservation, diagnosis and reproduction
material added during sealing. The root `evidence/brotli-b3c-e3.json` binds the
source, approval/scope records, final gate and checkpoint documentation.


The selected legacy-core and retained emission harness uses
`--no-auto-recommends-check` on both its positive and negative copies. As pinned
`verus --help` states, this omits automatic advisory recommends checks only
after a primary failure. The actual whole positive uses its original complete
command. All primary proof/lifetime/erasure/no-cheating checks and the strict
raw-resource exclusion remain. The original mixed primary/advisory outputs,
pinned help and matched diagnostic pair are preserved.
