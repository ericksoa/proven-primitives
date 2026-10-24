# Local verification and release pipeline P1

P1 implements the approved local, fail-closed evidence architecture in
[`tools/pipeline.py`](tools/pipeline.py) with Python 3.14.6's standard library.
It adds no service, database, CI authority, dependency, verifier or publication
mechanism. It does not adopt a security profile.

The command has six explicit operations:

- `inventory` and `case` strictly validate supported-object and CVE records.
- `freeze` hashes a sorted path/NUL/SHA-256/newline closure and rejects paths
  outside the selected root.
- `verify` runs the pinned Verus executable with the fixed whole-crate,
  `--no-cheating`, one-thread option set and records raw outcomes separately
  from untrusted candidate metadata.
- `coverage` joins approved profile obligations, semantic capabilities,
  supported inventory and exact-source receipts. It never infers composition
  support from component support.
- `gate` revalidates frozen files and hashes, external expected profile and
  approval digests, complete applicable coverage, actual verifier success,
  locked dependencies and independent-review status. Any missing or unknown
  value denies release.

The standard-library test suite performs one passing exact-evidence gate and
requires denial for omitted obligations, invented non-applicability, stale
source, profile retargeting, removal of `--no-cheating`, partial verification,
a forged checked result or theorem binding, lockfile drift, a narrowed domain,
deletion of a failing supported item, test-only evidence and unknown fields.
Escaping paths are also rejected before any referenced file is read.

These controls validate bookkeeping behavior. They do not prove a primitive,
review the threat model or make the draft `PP-Security/1.0.0` profile normative.
The first profile's clauses, applicability matrix, proof bindings and human
independent-review record remain separate release prerequisites.
