# Recorded verification

The logs in this directory were produced by actual local commands, not written
as predicted output.

| Check | Result |
| --- | --- |
| `lake build` | Exit 0; all 144 source modules and the root import compiled |
| `lake env lean Audit.lean` | Exit 0; 2045 declarations audited, including 1600 theorem declarations |
| Handwritten `theorem` declarations | 759 total: 752 public and 7 private helpers; comments and strings are excluded from this source count |
| Allowed axiom dependencies | `propext`, `Classical.choice`, `Quot.sound` |
| `sorryAx` or any other unexpected axiom | None in the audited dependency closures |
| mathlib tracked source changes | None |
| Conditional theta ineffectivity | Proved for actual sheaves with explicit local and restriction-map hypotheses |
| Theta finite-dimensionality and hyperplane dimension three | Derived from the restriction data, not separately assumed |
| Actual plane-curve scheme and hyperplane sheaf | Constructed using the reduced induced closed scheme and coordinate cocycle descent |
| Actual hyperplane square pairing | Constructed; tensor-perfectness proved on every chart subopen |
| Quartic restriction on actual coordinate sections | Proved, including on arbitrary nonempty chart refinements |
| Concrete conditional theta theorem | `planeQuintic_even_theta_sections_eq_zero_of_cotangent_square`; adjunction, primality, actual smoothness, restriction maps, normality and refined local technical inputs are discharged |
| Actual quadratic-section surjectivity | Proved for the constructed curve over an infinite field, with homogeneous prime equation of degree greater than one |
| Coordinate choice and denominator clearing | Constructed through explicit polynomial and cone quotient equivalences; monicity is not a final hypothesis |
| Actual sections on arbitrary linear charts | Constructed using genuine regular functions and structure-sheaf gluing |
| Local line-sheaf descent and actual square isomorphism | Construct cocycle, actual descent isomorphism, pairing and local tensor-perfectness |
| Product-cocycle tensor universal property | Proved for natural bilinear pairings, including transport to independently given actual line sheaves |
| Actual smooth integral curve normality | Proved over a perfect field from `IsSmoothOfRelativeDimension 1` |
| Common nonempty affine refinement | Constructed from the original line trivializing cover and coordinate cover |
| Explicit Jacobian condition to primality and actual smooth morphism | Proved over an algebraically closed field for the original homogeneous quintic equation |
| Actual chart polynomial maps | Surjective with full kernel `(F, Xᵢ - 1)` |
| Positive-degree homogeneous ternary forms | A common nonzero zero exists over an algebraically closed field |
| Vector and projective-prime Jacobian conditions | Proved equivalent for the homogeneous equation over an algebraically closed field |
| Actual differential sheaf | Sheafification with the original structure morphism's constants; universal property for sheaf-valued derivations proved |
| Canonical affine differential-sheaf comparison | Actual isomorphism to `ModuleCat.tilde Ω[A/K]`, preserving the differential of every regular section; no added localization or stalk-isomorphism input |
| Differential principal-open and stalk localization | Proved for the actual affine differential presheaf |
| Actual curve differential-presheaf frames | Basis and coefficient trivialization on derivative principal opens; scalar action and coordinate derivative identified |
| Residue differential identities | Chain rule, cotangent relation, same-chart swap, common-derivative and radial-derivative cross-chart degree-two transitions |
| Differential-sheaf frames on actual curve restrictions | Constructed from the actual Jacobian module bases via affine comparison, open-subscheme restriction and original-site transport; generator formulas proved |
| Actual differential-sheaf restriction and open-immersion transport | Isomorphisms proved, preserving actual derivations and sheafification units |
| Complete signed residue transitions | Proved on every actual chart overlap, including mixed derivative cases, with the actual hyperplane-square cocycle |
| Actual plane-quintic differential adjunction | `planeQuinticAdjunctionIsoOfJacobian`; actual relative differential sheaf is isomorphic to the constructed hyperplane-square sheaf, without an adjunction or local-frame input |
| Model restrictions and overlaps | Actual scalar-extension models, trace naturality, coordinate cocycles, transition-unit square and scalar-change formulas proved |
| Actual structure-sheaf coefficient rings | Models on Γ(V,O) tensor_R A for all chart subopens, with both coordinate restriction laws; actual module-sheaf section comparison still pending |
| Principal-open unit Kummer cover | Constructed for a module-finitely-presented flat formally unramified algebra with 2 invertible and rank two at every prime; coherent sheaf atlas still pending |
| Local finite flat rank-two algebra, with no supplied basis | Unit Kummer model, actual trace-kernel coordinate and multiplication tensor-square equivalence constructed over a local ring |
| Unit Kummer model from an actual basis and formal unramifiedness | Constructed; actual multiplication coefficients, completed-square algebra isomorphism, and unit parameter are derived |
| Actual based algebra's trace-kernel square | Actual tensor linear equivalence constructed and proved to induce multiplication in the original algebra |
| Global trace and categorical trace kernel from a coherent quadratic atlas | Constructed internally; actual kernel frames, extracted cocycle and descent isomorphism proved |
| Actual trace-kernel square pairing | Locally tensor-perfect and proved to agree with multiplication in each supplied quadratic algebra chart |
| Atlas-relative theta endpoint | `planeQuintic_even_trace_kernel_twist_sections_eq_zero`; tensor universal property uses the actual kernel, parity remains an input |
| Atlas extracted from the specified finite étale discriminant cover | Not yet constructed; pushforward trace identification remains open |
| Original conic-bundle hypotheses to the equation and Jacobian condition | Not yet formalized |
| Original cover's theta identification, cotangent square and parity | Not yet constructed from the original discriminant cover; remain explicit geometric inputs |
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
PATH=/workspace/scratch/84e095cf47c4/lean-tools/lean-4.24.0-linux/bin:$PATH \
LD_PRELOAD=/workspace/scratch/84e095cf47c4/lean-tools/self_exe_compat.so \
lake build

PATH=/workspace/scratch/84e095cf47c4/lean-tools/lean-4.24.0-linux/bin:$PATH \
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

The new constructed endpoint is `planeQuintic_even_twoTorsion_twist_sections_eq_zero`. Its input includes the original line cocycle on an arbitrary cover, an actual square trivialization, and even finrank of its constructed hyperplane twist. The theta sheaf, original-factor tensor universal property, and cotangent square are constructed internally. Extraction from a discriminant double cover is not yet formalized.

The local-model endpoint is now `planeQuintic_even_kummer_twist_sections_eq_zero`. Unlike the earlier two-torsion interface, it constructs the global line-square isomorphism from actual local quadratic-algebra maps and their generator-coordinate compatibility with a supplied cocycle. The actual algebra trace kernel, its tensor square, and algebra-isomorphism transition units are separately formalized. This does not assert extraction of the local data from the specified finite étale cover; see `docs/LOCAL_KUMMER_BRIDGE.md`.

The atlas-relative endpoint is `planeQuintic_even_trace_kernel_twist_sections_eq_zero`. It takes an actual module sheaf with coherent quadratic charts and constructs the trace morphism, actual kernel, frames, cocycle, descent isomorphism and square pairing. Local multiplication agreement is proved. The supplied atlas has not yet been extracted from the specified cover. See `docs/GLOBAL_TRACE_KERNEL_BRIDGE.md`.

The previous remote run [38343667957](https://github.com/taobaozhe-amoy/EvenQuinticConic-lean/actions/runs/38343667957) failed during dependency download with `Recv failure: Connection reset by peer`; its source build and axiom audit steps were skipped. That does not supply a remote proof check. The workflow now retries dependency setup at most three times and still fails after three unsuccessful attempts; source build and axiom audit remain required. Current remote status must be read from the new commit's Actions run.

## Shared dependency traversal

`Audit.lean` now runs Lean 4.24.0's official `Lean.CollectAxioms.collect`
over every declaration in the project namespace using one shared visited
set. The official traversal still examines both declaration types and
values (and the same constructor/recursor dependencies). Its resulting
axiom set is the union of all audited dependency closures. The audited
roots and the allowlist are unchanged; only duplicate traversal is removed.
The log lists checked theorem names and the aggregate axiom set, rather
than repeating a separate axiom set for each theorem.

Two isolated temporary copies of the audit were tested: one inserted an
extra project axiom and the other a theorem proved with `sorry`. Both
failed with the expected unexpected-axiom diagnostics. The exact inserted
text and observed results are recorded in `audit-regression.json`. These
negative fixtures are not imported into the project.

The subsequent remote run [38503276211](https://github.com/taobaozhe-amoy/EvenQuinticConic-lean/actions/runs/38503276211), for commit `05cb95da542be9651fb4fd80a7e9d1d28ac3a476`, completed successfully. This records the preceding revision; the current revision is checked by its own run.

Remote run [38508183649](https://github.com/taobaozhe-amoy/EvenQuinticConic-lean/actions/runs/38508183649), for commit `d1c76c04870de59aa34d063d8539d698a27203bd`, completed successfully. Later revisions have their own Actions runs.
