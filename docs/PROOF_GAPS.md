# Proof obligations that remain open in this project

The following is a work plan for scrutinizing a proposed mathematical argument, not a list of verified consequences. Every implication below needs both a precise statement and a proof. Finding a missing hypothesis or a false implication would require revising the argument, not adding an axiom to Lean.

## 1. State the geometric problem

Define the real base, the smooth projective total space, the conic-bundle morphism, geometric standardness, the smooth discriminant curve of degree five, its étale double cover, and the associated theta characteristic. Define evenness using the parity of the actual dimension of global sections after the appropriate base change. Relate the topology on real points to the intended real algebraic variety.

This complete collection of geometric hypotheses is not currently assembled into a Lean statement of the target theorem. The actual plane curve and hyperplane sheaves constructed below do not yet supply the conic bundle, specified double cover, or real topology. Generic propositions named `EvenTheta` or `Rational` would not accomplish this task.

## 2. Even theta and symmetric determinantal representation

The section-theoretic implication is now a **conditional theorem about
actual schemes and actual module sheaves**. `ThetaIneffectivity.lean` proves
that two independent actual sections force `Θ ≅ H`. The same restriction
inputs imply `h⁰(H)=3` and finite-dimensional theta sections, so even
dimension implies that every actual theta section is zero. No desired
comparison `Θ ≅ H` or vanishing statement is an input.
The final `PlaneThetaAdjunction` endpoint derives differential adjunction
and normality from the equation, and the local technical data from actual
line-sheaf trivializations and a square isomorphism to the differential
sheaf. It still does not construct those
geometric objects from the original conic bundle.

The checked chain now includes:

- `SchemeScalarAction`: base-field actions and scalar towers induced by the
  actual structure morphism `X → Spec K`, and an injective `K`-linear generic
  coefficient map preserving independence.
- `QuadraticSections`: an actual linear map from homogeneous quadratics to
  actual global sections, built from three sections and a natural pairing.
  Surjectivity of this map supplies the three polynomial lifts; their
  generic product formulas are derived, not separately assumed.
- `RankOnePairing` and `ModulePairing`: an actual locally tensor-perfect
  pairing has a unit coefficient in local rank-one frames and supplies one
  common generic multiplier for `s²`, `st`, and `t²`.
- The existing degree and factorization modules: quartic injectivity gives
  `AD=B²`, then `A=ca², B=cab, D=cb²` with homogeneous linear `a,b`.
- `ThetaSectionBridge`, `PairingComparison`, `FrameComparison`, and
  `ModuleHomGluing`: construct the actual linear section, the global square
  identity, local unit comparison maps, their overlap compatibility, and
  an actual isomorphism `Θ ≅ H`. This uses the established actual generic
  injection, normal-affine unit extension, and sheaf gluing results.
- `ThetaFiniteDimension`: actual quadratic surjectivity makes the square
  section space a quotient of `K⁶`; pairing with a nonzero theta section is
  injective, so theta sections are finite-dimensional (the zero space case
  is handled separately).
- `HyperplaneDimension`: quartic injectivity makes the three coordinate
  sections independent, and quadratic surjectivity forces them to span.
  Their actual basis gives `h⁰(H)=3` without an extra dimension hypothesis.
- `GlobalSectionDimension` and `ThetaIneffectivity`: the actual isomorphism
  induces a base-field-linear equivalence of global section spaces; the
  internally proved dimensions and parity give the conditional vanishing
  theorem `even_theta_ineffective_of_restriction_maps`.

Finite-dimensionality is proved before using finite rank zero to deduce
that every section is zero. The final theorem does not treat an unrestricted
`finrank = 0` as a vanishing statement and does not assume either
finite-dimensionality or `h⁰(H)=3` as a separate hypothesis.

The actual geometric realization now goes further than this general theorem:

- `PlaneCurveScheme` constructs the reduced induced closed scheme `V(F)` in
  the actual projective plane, its structure morphism over `K`, its generic
  point, and its three nonempty affine coordinate charts. Integrality is
  proved from homogeneous primality and the degree condition.
- `ProjectiveCoordinateSections`, `PullbackTransition`, and the four
  `LineBundle*` construction modules descend actual coordinate-ratio unit
  cocycles to an actual module sheaf. The sheaf axiom is proved using the
  structure sheaf, and compatible local frames are explicitly constructed.
- `LineBundlePairing` constructs the product-cocycle sheaf and the actual
  hyperplane square pairing. Its tensor lift is proved bijective on every
  subopen of a chart, via explicit local linear equivalences.
- `PlaneHyperplaneSheaf` constructs three actual global coordinate sections
  of that hyperplane sheaf and identifies their generic coefficients with
  the actual normalized projective coordinates.
- `ProjectiveQuarticRestriction` proves low-degree injectivity in the
  actual curve function field through the actual inclusion's generic prime.
  `ProjectiveBaseScalars` identifies the coefficient map with the canonical
  base-field action induced by the structure morphism.

`PlaneHyperplaneRestriction` carries the exact quartic statement to every
nonempty subopen of a coordinate chart. `PlaneQuadraticSurjectivity` now
proves `planeCurve_quadraticSectionMap_surjective` on the actual constructed
curve over any infinite field: the equation is homogeneous, has total
degree greater than one, and generates a prime ideal. Neither monicity nor
a coordinate choice or lifting property is a theorem input.

`PlaneThetaVanishing` uses that theorem to prove
`planeQuintic_even_theta_sections_eq_zero_of_normal_frames`. The curve, its
integrality, the hyperplane and square sheaves, their coordinate sections,
hyperplane multiplication pairing and local perfectness, quadratic
surjectivity, and quartic injectivity are all supplied internally. The
remaining inputs are a nonempty affine refinement with integrally closed
coordinate rings and theta frames, a locally tensor-perfect theta pairing,
and evenness, over an algebraically closed field. This permits an arbitrary
common refinement; it does not require theta to be trivial on the three
entire standard charts. The older `PlaneThetaIneffectivity` interface with
an explicit `h2` remains available as a lower-level theorem.

The intermediate `PlaneThetaSmooth` interface proves
`planeQuintic_even_theta_sections_eq_zero_of_smooth`. Its inputs are the
homogeneous prime quintic equation, actual relative-dimension-one smoothness
of `planeCurveStructure F`, an actual module sheaf with local unit-sheaf
isomorphisms on a cover, an actual isomorphism from their descended square
to the hyperplane square, and even section dimension. It has **no separate
normality, affine-refinement, frame, pairing, or tensor-perfectness input**.

`SmoothCurveNormality` proves that a standard smooth domain of relative
dimension one over a perfect field is integrally closed, using the actual
cotangent injection, finite separable maximal residue fields, differential
base change, and the local DVR criterion. `SmoothSchemeNormality` applies
this to the affine charts supplied by the actual scheme smoothness predicate,
then localizes to the stalks. `NormalSchemeSections` supplies the normal
section rings on the common refinement constructed by `AffineCommonRefinement`.

`LocalTrivializationFrames` and `FrameCocycleDescent` extract the actual
unit cocycle and prove its descended sheaf is isomorphic to the original
line sheaf. `LineBundleSquareIso` constructs the square pairing and proves
local perfectness from the given square isomorphism.
`UnitTransition.productHomEquivOfIso` in `LineBundleTensorUniversal` proves
that the product-cocycle sheaf represents natural bilinear pairings on the
original line sheaves, for every target module sheaf. This is a genuine
tensor universal property; no global-section tensor surjectivity is asserted.
The square is not yet packaged as an isomorphism to mathlib's sheafification
of the presheaf tensor product.

`PlaneThetaJacobian` supplies the equation-based interface:
`planeQuintic_even_theta_sections_eq_zero_of_jacobian`. Besides the actual
line-sheaf inputs and parity above, it takes only an algebraically closed
field and a homogeneous polynomial of total degree five satisfying

```text
for every v ≠ 0, F(v) = 0 implies some ∂ᵢF(v) ≠ 0.
```

Neither homogeneous primality nor actual scheme smoothness is an independent
input. The checked proof has two branches:

- `HomogeneousFactors`, `PlaneOriginHeight`, and `HomogeneousCommonZero`
  prove that a nontrivial homogeneous factorization has a nonzero common
  zero. The last result uses the actual affine Nullstellensatz and the
  two-generator Krull height bound, contradicted by an explicit prime chain
  of length three at the origin. `JacobianIrreducible` then derives
  irreducibility and primality from the actual partial derivatives.
- `ChartHomogenization` and `PlaneChartPolynomialMap` prove surjectivity and
  the complete kernel `(F, Xᵢ−1)` for actual chart sections. The generators
  are actual coordinate-ratio sections and the coefficient map is proved
  equal to the actual structure morphism's pullback. `PlaneJacobianPresentation`
  computes the two-relation Jacobian. `JacobianLocalization` and
  `PlaneGradientCover` supply actual standard-smooth derivative principal
  opens covering the curve. `PlaneJacobianSmooth` constructs the actual
  `IsSmoothOfRelativeDimension 1` structure.

`ProjectiveJacobianPoints` constructs the actual projective prime associated
to each nonzero vector. `ProjectiveJacobianCriterion` proves that the
ordinary vector criterion above is equivalent to the gradient condition on
all actual projective prime points. The reverse direction uses the
Nullstellensatz. No closed-point density or rational-point correspondence
is assumed without proof.

The equation is deliberately distinguished from its reduced locus:
`X₀^5` has a smooth reduced projective line, but its principal ideal is not
prime. The new Jacobian hypothesis rejects that example. The smoothness
of the reduced locus alone is never used to infer primality.

The differential adjunction bridge is now closed. `SchemeKaehlerRestriction`
and `SchemeKaehlerIsoTransport` prove actual open-subscheme restriction and
open-immersion transport, including the actual derivation formulas.
`TildeModuleFrames`, `AffineKaehlerFrames`, and `AffineOpenKaehlerComparison`
turn the proved Jacobian module bases into genuine sheaf trivializations.
`SchemeOpenModuleFrames` and `SchemeOpenDifferentialFrames` transport those
to the original site, including the precise generator on every subopen.

`PlaneCurveResidueFrames` rescales those actual frames by actual derivative
units and permutation signs. `PlaneCurveSignedResidueTransitions` proves
all overlap formulas, including the two mixed derivative choices, with
coefficients equal to the actual hyperplane-square cocycle. Genuine local
maps are glued by `FrameTransitionComparison`. The resulting endpoint is
`planeQuinticAdjunctionIsoOfJacobian`:

```text
schemeKaehlerSheaf (planeCurveStructure F) ≅ PlaneCurveQuadraticSheaf F
```

Its only inputs are an algebraically closed field, a homogeneous quintic
of total degree five, and the nonzero-vector Jacobian condition. The lower
`planeCurveAdjunctionIsoOfGradient` interface works over any field with
explicit primality and the projective-prime gradient criterion. Neither
endpoint assumes adjunction or differential-sheaf local freeness. No claim
about arbitrary-open section rings replacing differential-sheaf sections
is used.

`PlaneThetaAdjunction` now accepts an actual square isomorphism to this
actual relative differential sheaf. Its theorem
`planeQuintic_even_theta_sections_eq_zero_of_cotangent_square` supplies
adjunction internally, then applies the already checked section argument.
The specified cover's theta sheaf, its square to the differential sheaf,
and parity remain genuine geometric inputs.

The remaining **geometric instantiation** must supply:

1. Construct the actual equation and its complexification from the original
   conic-bundle discriminant, and verify the explicit polynomial Jacobian
   condition. From that condition, prime ideal, actual smooth morphism,
   normality, and all subsequent local technical data are now proved.
   A converse Jacobian theorem starting with an arbitrary scheme-theoretic
   smooth hypersurface has not been proved here.
2. Extract the actual trace-zero line sheaf η and its square trivialization
   from the specified finite étale discriminant double cover. The new twist
   construction then supplies Θ=η⊗H, its local frames and its cotangent
   square; identify this constructed twist with the specified theta object.
3. Relate the conic bundle's specified real double cover, its theta line
   bundle, and geometric parity, including the real base-change step.

The former quadratic-surjectivity gap is closed by the following checked
chain. `PlaneChartRepresentatives` lifts actual affine-chart functions to
homogeneous fractions; `QuadraticFractionBridge` proves the square sheaf's
weight-two transitions. `PlaneLinearChartRepresentatives` compares actual
fractions on arbitrary linear-form charts with standard generic
coordinates. `LinearChartQuadraticSections` glues the actual regular
function `s/L²` on such a chart and produces its homogeneous numerator.
`PlaneHomogeneousKernel` proves that every homogeneous vanishing relation
belongs to `(F)`, so generic compatibility gives an actual cone equality.

`HomogeneousCoordinateChoice`, `PlaneMonicModel`, and
`PlaneCoordinateClearing` construct an actual polynomial coordinate
equivalence and nonzero scalar normalization making the equation monic.
The monic quotient's finite free basis gives simultaneous denominator
clearing, transported back to the original cone for two actual linear
forms. `LinearDenominatorClearing` extracts the degree-two homogeneous
representative. Finally `PlaneQuadraticSurjectivity` uses the actual global
section generic injection to show that this polynomial restricts to the
original section. Affine restriction surjectivity alone is not treated as
global surjectivity; the intervening compatibility and denominator arguments
are proved. No projective scheme automorphism or sheaf transport is needed.

The curve construction uses the reduced induced subscheme, not a declared
isomorphism with `Proj(K[X₀,X₁,X₂]/(F))`. That alternate presentation is not
proved here. The whole affine-cone fraction field is never identified with
the curve function field: degree-zero ratios are compared directly, while
the full cone embeds in `k(C)[T]` with `T` retaining homogeneous degree.

[THETA_BRIDGE_REVIEW.md](THETA_BRIDGE_REVIEW.md) retains the mathematical
proof and records the exact conditional Lean theorem. The formalized route
now directly constructs `Θ ≅ H`; it does not need to assume or perform
cancellation in the Picard group. The alternative paper proof cancels two
only in the actual divisor group after obtaining a section identity.

Beauville's Proposition 4.2(a) works over the real field for an actual real
ineffective theta line bundle (his §0.3 allows arbitrary fields, and the
symmetric-resolution theorem applies in characteristic different from two).
Consequently the informal proof can invoke the theorem over `ℝ` directly,
without descending an arbitrarily chosen complex matrix. This theorem,
its hypotheses for the actual curve, and the cover comparison remain
unformalized.

## Mathematical audit of the remaining route

[REAL_OBSTRUCTION_AUDIT.md](REAL_OBSTRUCTION_AUDIT.md) now records the precise
nonformal route through the real cover comparison, Brauer evaluation,
Albert/Pfister argument, zero cycles and rational incidence construction.
It checks the signs and the real twist instead of assuming that complex
cover agreement suffices. These are mathematical deductions using cited
classical results; the Lean obligations below remain open.

## 3. Identify the double cover and the Clifford class

Show that the cover obtained from the rank-four degeneration of the symmetric matrix agrees with the conic bundle's discriminant cover, with the correct real twist. A statement over the complex numbers alone does not settle the real twist.

`CofactorCover.lean` now also constructs a vector root from a nonzero square
pivot and explicit rank-one minor identities, and proves that the solution set
has exactly two elements when the characteristic is not two and a nonzero root
exists. It does not derive the minor identities from geometric corank,
construct a cover of schemes, prove étaleness, or associate a line bundle or
theta characteristic to it.

The root equation now has an explicit twist parameter. In particular, the
negative-adjugate equation must not automatically be used for the rank-four
degeneration of a five-dimensional form: the proposed signed-discriminant
convention differs from the rank-two degeneration of a three-dimensional
conic form. Identification of the correct geometric cover and twist remains
an obligation, even though the algebraic root lemmas support either sign.

The proposed argument also needs Brauer residues, an unramified/constant-class comparison, a real evaluation fixing the constant class, and a proof that the relevant even Clifford class has index at most two. These are absent from this project.

## 4. Prove isotropy of the five-dimensional form

The proposed route must justify:

1. Indefiniteness at every ordering of `ℝ(x,y)`, including the passage from real specializations to arbitrary orderings.
2. The exact quadratic-form classification turning anisotropy plus the Clifford index bound into a Pfister-neighbor situation; any scaling and discriminant conventions must be checked.
3. The signature and torsion argument in the Witt ring, and the needed result on the third power of its fundamental ideal for this field.
4. The resulting split eight-dimensional form and an actual isometric embedding of the five-dimensional form into it.

`IsotropicDimension.lean` proves only the final dimension argument. It also constructs the concrete split form `q(x,y)=Σ xᵢyᵢ` and proves that every five-dimensional subspace of its eight-dimensional space has isotropic restriction. It does not derive a split form from the geometry.

## 5. From generic isotropy to a real point of the net's base locus

The intended argument uses a zero-cycle theorem for systems of quadrics and a real-point consequence. Precisely state the theorem, check its field and dimension hypotheses, construct the zero-cycle of odd degree, and prove the required real closed field implication. Generic isotropy is not, by itself, a Lean proof that the intersection of three quadrics has a real point.

This bridge is not formalized. A precise primary-source version is
Colliot-Thélène–Levine, *Une version du théorème d’Amer et Brumer pour les
zéro-cycles*, [arXiv:0911.4644](https://arxiv.org/abs/0911.4644): for `r+1`
forms of common degree `d≥2` in `n+1≥r+2` variables, their common projective
locus has a degree-one zero-cycle if and only if the generic member has one.
Three quadrics in five variables satisfy these numerical conditions.
A rational point on that generic member supplies the required zero-cycle;
over `ℝ`, a degree-one zero-cycle forces a residue-degree-one closed point.
This identifies a mathematically applicable route, not a Lean proof of it.

## 6. Incidence correspondence and rationality

Starting from a real base point, construct the hyperbolic reduction and identify the resulting equations with the intended conic bundle, including the relevant Clifford-class comparison. Prove a suitable minor is nonzero on a nonempty dense open set. Upgrade the cross-product formulas to inverse regular morphisms of scheme charts.

`Incidence.lean` gives explicit solutions of two linear equations and an equivalence of sets on a minor chart. The minor chart could be empty for a given parameter family. No density, regularity, birational map, or rationality theorem is proved.

## 7. Real rationality and connectedness

Precisely state and prove the necessary invariance/connectedness result for smooth projective real varieties, including nonemptiness. Apply it to the actual total space.

`ConnectedComponents.lean` only proves the elementary consequence of an explicit `ConnectedSpace` assumption using the genuine connected-component quotient. It does not establish that assumption for any conic bundle.

## Acceptance criterion for the full theorem

A completed proof would have an actual geometric statement, explicit original hypotheses, and a Lean proof depending only on accepted foundational axioms and proved mathematics. It would neither take rationality/connectedness as an extra unexplained premise nor encode the desired conclusion inside a definition of the hypotheses. The current repository does not meet this full-theorem criterion and does not claim to.

## Constructed two-torsion twist

`PlaneThetaTwoTorsion.lean` constructs the actual module sheaf Θ=η⊗H from a unit cocycle on any open cover. `LineBundleRefinement.lean` constructs the common-cover comparisons, and `planeTorsionThetaHomEquiv` proves the tensor universal property for the original two factors. Given an actual trivialization η²≅O, `planeTorsionThetaCotangentSquareIso` constructs Θ²≅Ω¹(C/K) using proved quintic adjunction. Neither Θ nor its local frames nor its cotangent square is an additional input.

`planeQuintic_even_twoTorsion_twist_sections_eq_zero` then proves that every global section vanishes, conditional on even finrank of the constructed twist, over an algebraically closed field with the stated homogeneous quintic and Jacobian hypotheses. Two-torsion here means order dividing two, including the trivial line sheaf.

Remaining: extract the trace-zero line sheaf and its square trivialization from the specified finite étale discriminant double cover; identify this twist with the specified theta characteristic and establish its parity; connect real base change and real geometry. No existence or nonexistence conclusion for the original real conic bundle follows from this milestone alone.

## Local quadratic multiplication update

The actual local trace-zero module and its multiplication tensor square are now proved in `QuadraticTraceZero`. Actual algebra isomorphisms supply trace-zero transition units and their composition law in `QuadraticTraceZeroTransition`. For given compatible local Kummer models and a given line cocycle, `squareIsoOfKummerMaps` constructs the global square trivialization, and `planeQuintic_even_kummer_twist_sections_eq_zero` uses it internally. Extraction of those models and their global trace-zero sheaf from the specified finite étale cover remains open. See [the exact local-model inputs and remaining obligations](LOCAL_KUMMER_BRIDGE.md).
