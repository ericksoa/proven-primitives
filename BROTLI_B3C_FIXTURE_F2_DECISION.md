# F1 fixture classification correction

Status: **Candidate F2 approved explicitly by the human on 2026-11-04:**
“Approve F2 as written.” F2 supersedes the two F1 classifications below.

F1's claim that both `monkey` and `quickfox_repeated` omit an advertised tree
was false. After correcting the serialized parser to drain an already-pending
implicit zero span before advancing, the following diagnostics hold:

| Fixture | Current observed result | Header evidence |
|---|---|---|
| `quickfox_repeated` | `Finished`, all 176,128 bytes equal the pinned expected file in nine input/output chunk combinations | Literal map contains 0, 1, 2, 3, 4 for five advertised trees; distance map contains 0 for one advertised tree. No tree is missing. |
| `monkey` | `InvalidFormat`, zero output in all nine combinations | W1 reports `ContextMapRepeat` at byte 11 with 60 of 64 literal-map entries initialized. Coverage checking has not been reached. |

The diagnostics used input chunks of one byte, seven bytes and the entire
fixture, and output chunks of one byte, 31 bytes and the expected output size.
They used a separate copy of the production source; the ongoing frozen
whole-crate check was not modified. Exact fixture hashes, diagnostic snippets
and transcripts are bound in
`evidence/brotli-m1-f1-classification-diagnostic.json`. These are runtime
diagnostics, not formal equivalence proofs or a new native-reference run.

## Candidate F2

1. Replace only `quickfox_repeated`'s F1 rejection expectation with successful
   decoding to the pinned expected bytes. Cover whole input, one-byte input,
   seven-byte input, every input split, output chunking and untouched output
   suffixes using the existing comparison-test structure.
2. Retain `monkey` as an expected zero-output, sticky `InvalidFormat` result
   for this checkpoint. Correct its recorded observed reason to
   `ContextMapRepeat`; do not claim it is a demonstrated RFC coverage
   difference or that native acceptance proves it malformed. Its disagreement
   with the native reference remains an unresolved format-equivalence issue.
3. Preserve strict every-advertised-tree coverage checking, including the
   synthetic missing-tree rejection tests and their checked contracts.
4. Preserve the approved fixed `compression` dictionary-transform stream and
   its successful comparisons.
5. Rerun the affected tests and final-source proof/defect controls. Keep M1,
   complete Brotli equivalence and the release gate incomplete.

This changes only the F1 comparison classification and related assertions and
documentation. It does not change decoder interfaces, workspace, budget
policy, dependencies, algorithms or proof trust. The human explicitly approved
this comparison correction on 2026-11-04.
