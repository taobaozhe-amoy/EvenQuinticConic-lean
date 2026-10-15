# Actual affine pushforward Kummer atlas

The new endpoint is `exists_affinePushforwardKummerAtlas` in
`EvenQuinticConic/AffinePushforwardKummerAtlas.lean`.

## Exact inputs and output

Inputs are commutative rings R,A in the same universe, an actual R-algebra
structure, `Module.FinitePresentation R A`, `Module.Flat R A`,
`Algebra.FormallyUnramified R A`, `Invertible (2 : R)`, and rank two for
`Localization.AtPrime p tensor_R A` at every prime p of R.

The conclusion supplies f : PrimeSpectrum R → R, proves that the basic
opens D(f(p)) cover Spec R, and constructs a `KummerModuleAtlas` on
`affinePushforwardModule`. That module is mathlib's actual pushforward of
the source structure module along `Spec A → Spec R`; its sections,
restrictions and scalar action are not substituted by an abstract model.
No basis, covering atlas, section comparison or overlap law is an input.

## Canonical comparison, including nonaffine opens

`affinePushforwardTensorMap V` is a ring homomorphism

Γ(V,O_Spec R) tensor_R A → Γ(π⁻¹V,O_Spec A).

It sends s tensor a to the product of the actual pulled-back coefficient
s and the actual constant section a, and commutes with restrictions.
For V=D(g), both rings are localizations of A at the image of g, so the
canonical map is bijective, with no finite or flat assumptions needed.

For arbitrary V contained in a principal Kummer chart D(f), all principal
opens contained in V form a cover. Local preimages under the canonical
map agree on intersections, since those intersections are principal and
the comparison there is injective. The existing Kummer model converts the
preimages into two actual structure-sheaf sections. Gluing the two
coordinates and applying the inverse Kummer coordinate map gives a tensor
section over V. Actual target-sheaf separation proves it maps to the
original target section. Source coordinate separation proves injectivity.
Thus the canonical map and its inverse commute with all chart-subopen
restrictions, including for nonaffine V.

## From comparison to the actual module atlas

`affinePushforwardKummerRingModel` composes the inverse comparison with the
existing tensor Kummer model. It is a genuine ring equivalence preserving
the pulled-back Γ(V,O) scalars. It therefore supplies a linear coordinate
map for the actual pushforward module action. Its two coordinates satisfy
the required restriction laws.

The chart parameter is the image of the original localization unit in
Γ(D(f),O). Every overlap map is constructed by going through the same
actual pushforward section ring; scalar preservation makes the comparison
an algebra equivalence. Coordinate compatibility follows from the inverse
law. This fills the actual `KummerModuleChart` and `KummerModuleAtlas`
structures used by the earlier global trace-kernel construction.

The final existence theorem first invokes the proved principal-open model
cover, then builds these actual charts and overlaps internally.

## Remaining geometric scope

This is an affine-base theorem for an actual algebra-induced scheme map.
The subsequent [general-base bridge](GENERAL_BASE_PUSHFORWARD.md) supplies
actual open-restriction comparisons, canonical affine presentations,
extraction of ring hypotheses under explicit geometric assumptions, and
chart independence of the trace. The original discriminant cover over the
projective curve has not yet been instantiated: multiplicative charts
still need transport through the affine presentation isomorphisms and
assembly over that base. Its global trace and trace-zero line, the theta
correspondence, parity after base change, and real topology remain open.
The full original existence/nonexistence problem is not yet proved.
