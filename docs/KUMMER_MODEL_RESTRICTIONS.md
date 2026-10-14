# Restriction of Kummer models and actual structure-sheaf coefficients

## Checked constructions

`kummerBaseChangeEquiv S u` is an actual algebra equivalence
`S tensor_R KummerAlgebra u ≃ₐ[S] KummerAlgebra (algebraMap R S u)`.
Its two coordinates on a pure tensor s tensor x are s times the respective
image coordinates of x. Multiplication preservation is proved, so this
is more than a module-coordinate identification.
`kummerModelBaseChange` transports an actual model of an arbitrary algebra.

`tensorBaseChangeRestriction` is the canonical algebra map along R→S→T.
Its identity and composition laws are proved. `kummerModelRestrict`
uses cancellation of iterated base change to give a model on T tensor_R A.
`kummerModelRestrict_naturality` proves the coordinate square commutes,
and `kummerModelRestrict_trace` proves the corresponding identity for the
actual mathlib algebra trace.

`kummerModelOverlap ei ej` compares two actual models through their common
algebra. The overlap equivalence is constructed, not postulated. With two
invertible, its extracted unit changes every imaginary coordinate by
multiplication; its square relates the Kummer parameters, and the units
satisfy the triple-overlap cocycle. `kummerModelOverlap_changeUnit_baseChange`
and `kummerModelRestrict_changeUnit` prove that these units are carried
to their scalar images under extension/restriction.

## Actual opens and coefficient rings

For an affine scheme Spec R and any V contained in D(f),
`principalOpenSectionMap` constructs R_f→Γ(V,O) by restricting the canonical
map into Γ(D(f),O). It extends the original R scalars and commutes with
all further structure-sheaf restrictions. The local algebra structure is
explicit rather than a global instance, since an open may lie in several
principal charts with different localization rings.

Given an actual model of R_f tensor_R A,
`principalOpenKummerSectionModel` constructs a model of Γ(V,O) tensor_R A
for every such V, including nonaffine opens. The parameter is the actual
section obtained from the original parameter. Theorems
`principalOpenKummerSectionModel_re_restrict` and
`principalOpenKummerSectionModel_im_restrict` prove exactly the two
coordinate restriction formulas for every W contained in V. Here the
restriction on the tensor algebra uses the genuine structure-sheaf
restriction on its coefficient factor.

## Subsequent actual pushforward comparison

The domain of these coordinates is Γ(V,O) tensor_R A. The subsequent
`AffinePushforwardComparison` module now proves that its canonical ring
map to Γ(π⁻¹V,O) is bijective on every subopen of a principal Kummer chart,
including nonaffine opens. This uses principal-localization comparisons,
actual structure-sheaf separation and explicit gluing of the two tensor
coordinates. It is not an unproved general assertion about arbitrary
modules on arbitrary opens.

`AffinePushforwardKummerAtlas` then constructs the compatible chart on
mathlib's actual pushforward module sheaf. See
[AFFINE_PUSHFORWARD_ATLAS.md](AFFINE_PUSHFORWARD_ATLAS.md). The remaining
geometric comparison is to the specified cover on its nonaffine base,
and to its global trace, theta characteristic, parity and real geometry.
