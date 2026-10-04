# Recorded verification

The logs in this directory were produced by actual local commands, not written
as predicted output.

| Check | Result |
| --- | --- |
| `lake build` | Exit 0; all sixty-three source modules and the root import compiled |
| `lake env lean Audit.lean` | Exit 0; 932 declarations audited, including 732 theorem declarations |
| Handwritten `theorem` declarations | 387 total: 382 public and 5 private helpers; comments and strings are excluded from this source count |
| Allowed axiom dependencies | `propext`, `Classical.choice`, `Quot.sound` |
| `sorryAx` or any other unexpected axiom | None in the audited dependency closures |
| mathlib tracked source changes | None |
| Conditional theta ineffectivity | Proved for actual sheaves with explicit local and restriction-map hypotheses |
| Theta finite-dimensionality and hyperplane dimension three | Derived from the restriction data, not separately assumed |
| Actual plane-curve scheme and hyperplane sheaf | Constructed using the reduced induced closed scheme and coordinate cocycle descent |
| Actual hyperplane square pairing | Constructed; tensor-perfectness proved on every chart subopen |
| Quartic restriction on actual coordinate sections | Proved, including on arbitrary nonempty chart refinements |
| Concrete conditional theta theorem | `planeQuintic_even_theta_sections_eq_zero_of_normal_frames`; both restriction hypotheses are discharged |
| Actual quadratic-section surjectivity | Proved for the constructed curve over an infinite field, with homogeneous prime equation of degree greater than one |
| Coordinate choice and denominator clearing | Constructed through explicit polynomial and cone quotient equivalences; monicity is not a final hypothesis |
| Actual sections on arbitrary linear charts | Constructed using genuine regular functions and structure-sheaf gluing |
| Concrete smooth plane-quintic instantiation | Not yet formalized |
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
namespace and their transitive axiom dependencies, including the private helpers
used by those declarations. The audited theorem count includes generated
declarations and differs from the handwritten source count. It does not verify external
mathematical prose, the missing geometry, or the original informal statement.
An axiom-free theorem with the wrong hypotheses would still not settle that
statement. The scope is therefore recorded separately in the README and
`docs/PROOF_GAPS.md`.
