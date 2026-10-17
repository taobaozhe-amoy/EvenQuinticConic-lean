# Recorded verification

The logs in this directory were produced by actual local commands, not written
as predicted output.

| Check | Result |
| --- | --- |
| `lake build` | Exit 0; all 187 source modules and the root import compiled |
| `lake env lean Audit.lean` | Exit 0; 2895 declarations audited, including 2267 theorem declarations |
| Handwritten `theorem` declarations | 1063 total: 1050 public and 13 private helpers; comments and strings are excluded from this source count |
| Allowed axiom dependencies | `propext`, `Classical.choice`, `Quot.sound` |
| `sorryAx` or any other unexpected axiom | None in the audited dependency closures |
| mathlib tracked source changes | None |
| Actual projective standard chart | Degree-zero homogeneous localization identified with the polynomial ring in three variables, preserving the coefficient field |
| Actual projective incidence open | Literal quotient scheme isomorphic to D₊(yₚ) ∩ D₊(Δᵢⱼ); canonical projection and projective structure-map compatibility proved |
| Nonemptiness and density | Derived from actual net/common-point/Jacobian inputs; density is in actual projective three-space, not in an unconstructed global incidence scheme |
| Actual incidence function field | Coordinate algebra integrality, fraction-field K-algebra equivalence and actual generic-stalk K-algebra equivalence to K(u,v,w) proved |
| Common point to polar independence | Derived from the actual determinant Jacobian; the adjugate outer-product formula is proved internally |
| Arbitrary common point to coordinate point | An invertible matrix is constructed; congruence determinant and partial derivatives scale by its nonzero determinant square |
| Polar coordinate normalization | Actual inverse polynomial algebra substitutions are constructed and preserve all homogeneous degrees |
| Actual common point to nonempty incidence minor | An assembled theorem uses only the matrix net, common point and Jacobian inputs; all independence, coordinate, factor-exclusion and determinant-nonzero inputs are discharged |
| Actual affine cone incidence scheme | Nonemptiness derived under those same inputs through the actual localized quotient and Spec isomorphism; global projective identification remains open |
| Ternary conic line splitting | Actual factorization into two independent linear polynomials iff the negative pivot cofactor is a square; equivalent to actual cofactor roots |
| Actual determinant derivative and gradient | Jacobi formula proved from the determinant expansion; a nonzero evaluated partial gives a nonzero adjugate and, for a symmetric singular matrix, a nonzero diagonal cofactor |
| Adjugate pivot identities and transitions | Derived from determinant zero and symmetry; square ratios and actual Kummer algebra equivalences constructed |
| Real Kummer algebra points | Actual algebra maps classified by square roots; for a nonzero parameter, existence is equivalent to positivity |
| Actual cofactor-vector fibers | Equivalent to actual Kummer algebra maps; positive signed pivot gives two elements and negative signed pivot gives none |
| Normalized affine incidence chart | Actual quotient-algebra equivalence and Spec isomorphism constructed; the map is the original projection and the localized target is the actual principal open |
| Nonempty normalized incidence chart | Vanishing coordinate minors forces a common linear factor; absence of that factor yields a nonzero minor and a nonempty chart over an infinite field |
| Global discriminant-cover comparison and projective incidence identification | Still open; see [the precise scope of these additions](../docs/REAL_COFACTOR_AND_INCIDENCE.md) |
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
| Actual affine pushforward covering atlas | Constructed from module finite presentation, flatness, formal unramifiedness, 2 invertible and rank two at each prime; no supplied atlas |
| Actual pushforward and base-open restriction | Canonical module-sheaf isomorphism, with multiplicative section comparison and actual scalar/restriction compatibility |
| Kummer atlas transport from actual open subschemes | Parameters, coordinates, restrictions, algebra overlaps and image-cover statements proved |
| Actual multiplicative charts on a general scheme | Algebra overlaps constructed through actual section rings; resulting global trace independent of covering chart family |
| Geometric affine presentation and Kummer models | Actual restricted arrow identified with Spec of f.app U; finite, étale, explicit Flat, Noetherian, invertible-two and rank-two inputs give principal models and an atlas on that spectrum |
| Multiplicative atlas on the original general base | Constructed from explicit geometric hypotheses through actual arrow-isomorphism transport and open-image cover assembly; no supplied chart |
| Unique actual trace from geometric hypotheses | Constructed without an atlas input and characterized by local algebra trace on every multiplicative chart |
| Actual geometric trace kernel and rank-one frames | Constructed; invertibility of two on every open is derived from the supplied cover |
| Actual geometric trace kernel-square pairing | Global natural pairing; tensor map locally bijective; explicitly agrees with multiplication in the original source section rings via kernel inclusion |
| Trace and kernel independence of affine cover | Equality of traces, canonical inclusion-preserving kernel isomorphism and its uniqueness proved |
| Geometric plane-cover-to-theta endpoint | `planeQuintic_even_finiteEtale_theta_sections_eq_zero`; actual finite/étale/explicit-flat morphism, canonical-chart rank two, quintic/Jacobian and parity inputs; no supplied atlas or square |
| Canonical plane chart ring hypotheses | Noetherianity and all-open invertibility of two derived from the base field |
| Specified discriminant cover | Geometric/rank hypotheses and theta correspondence still not instantiated |
| Canonical tensor-to-actual-section comparison | Ring isomorphism on principal opens and all subopens of a Kummer chart, with restriction-compatible inverse |
| Model restrictions and overlaps | Actual scalar-extension models, trace naturality, coordinate cocycles, transition-unit square and scalar-change formulas proved |
| Actual structure-sheaf coefficient rings | Models on Γ(V,O) tensor_R A for all chart subopens, with both coordinate restriction laws; actual pushforward section comparison now proved on every chart subopen |
| Principal-open unit Kummer cover | Constructed for a module-finitely-presented flat formally unramified algebra with 2 invertible and rank two at every prime; actual affine pushforward sheaf atlas now constructed |
| Local finite flat rank-two algebra, with no supplied basis | Unit Kummer model, actual trace-kernel coordinate and multiplication tensor-square equivalence constructed over a local ring |
| Unit Kummer model from an actual basis and formal unramifiedness | Constructed; actual multiplication coefficients, completed-square algebra isomorphism, and unit parameter are derived |
| Actual based algebra's trace-kernel square | Actual tensor linear equivalence constructed and proved to induce multiplication in the original algebra |
| Global trace and categorical trace kernel from a coherent quadratic atlas | Constructed internally; actual kernel frames, extracted cocycle and descent isomorphism proved |
| Actual trace-kernel square pairing | Locally tensor-perfect and proved to agree with multiplication in each supplied quadratic algebra chart |
| Atlas-relative theta endpoint | `planeQuintic_even_trace_kernel_twist_sections_eq_zero`; tensor universal property uses the actual kernel, parity remains an input |
| Atlas extracted from the specified finite étale discriminant cover | Not yet constructed; pushforward trace identification remains open |
| Original conic-bundle hypotheses to the equation and Jacobian condition | Not yet formalized |
| Original cover's theta identification and parity transfer | Not yet identified with the geometrically constructed twist after base change; original evenness must be transferred to that object |
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
PATH=/tmp/lean-4.24.0-linux/bin:$PATH \
LD_PRELOAD=/tmp/self_exe_compat.so \
lake build

PATH=/tmp/lean-4.24.0-linux/bin:$PATH \
LD_PRELOAD=/tmp/self_exe_compat.so \
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

Remote run [38509507186](https://github.com/taobaozhe-amoy/EvenQuinticConic-lean/actions/runs/38509507186), for commit `bd2e926891d60afad0530734c1748b37b9f979a6`, completed successfully. The new revision has its own Actions run.

The current geometric endpoint eliminates the atlas and square inputs for a
given actual plane-curve cover satisfying explicit finite, étale, flat and
canonical-chart rank-two hypotheses. It does not instantiate the original
conic bundle. The distinction between checked conditional implications and
the unproved original conclusion is recorded in `docs/PROOF_STATUS.md`.

Remote run [38669519380](https://github.com/taobaozhe-amoy/EvenQuinticConic-lean/actions/runs/38669519380),
for preceding commit `57973b7e82a430fe8254429d6a92c8c547fd91cd`, completed successfully.
The new revision is checked by its own run.
