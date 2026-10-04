# Recorded verification

The logs in this directory were produced by actual local commands, not written
as predicted output.

| Check | Result |
| --- | --- |
| `lake build` | Exit 0; all sixteen source modules and the root import compiled |
| `lake env lean Audit.lean` | Exit 0; 170 declarations audited, including 141 theorem declarations |
| Handwritten `theorem` declarations | 90; the remaining theorem declarations in the audit are compiler/tactic/structure-generated |
| Allowed axiom dependencies | `propext`, `Classical.choice`, `Quot.sound` |
| `sorryAx` or any other unexpected axiom | None in the audited dependency closures |
| mathlib tracked source changes | None |
| Full geometric no-go theorem | Not formalized or verified |
| GitHub Actions | See the repository's Actions tab for current remote run status |

## Local runtime compatibility

Lean's official Linux executable initially could not locate itself in this
container: `/proc/<getpid()>/exe` was unavailable whereas `/proc/self/exe`
worked. A local `LD_PRELOAD` compatibility library redirected only that exact
process-self `readlink` request. Its complete C source is recorded in
`self_exe_compat.c` so that this environmental workaround is inspectable.
It does not change Lean's elaborator, kernel, mathematical sources, or proofs.
The project and its ordinary GitHub Actions workflow do not require this shim.

The local invocation was:

```sh
PATH=/root/.elan/bin:$PATH \
LD_PRELOAD=/workspace/scratch/84e095cf47c4/lean-tools/self_exe_compat.so \
lake build

PATH=/root/.elan/bin:$PATH \
LD_PRELOAD=/workspace/scratch/84e095cf47c4/lean-tools/self_exe_compat.so \
lake env lean Audit.lean
```

The build also required unpacking the standard `leantar` archive with
`--no-same-owner` due to the container's ownership restrictions. No Lean or
mathlib source was changed to work around that restriction.

## What the axiom check does not certify

The audit inspects the actual declarations in the `EvenQuinticConic`
namespace and their transitive axiom dependencies. It does not verify external
mathematical prose, the missing geometry, or the original informal statement.
An axiom-free theorem with the wrong hypotheses would still not settle that
statement. The scope is therefore recorded separately in the README and
`docs/PROOF_GAPS.md`.
