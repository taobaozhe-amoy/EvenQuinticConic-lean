# Status against the pinned mathlib checkout

This project pins Lean **v4.24.0** and mathlib commit
[`f897ebcf72cd16f89ab4577d0c826cd14afaafc7`](https://github.com/leanprover-community/mathlib4/tree/f897ebcf72cd16f89ab4577d0c826cd14afaafc7)
(the mathlib v4.24.0 release).

The observations below come from searching and reading **that checkout**.
They are not claims about every Lean project or a later version of mathlib.
Absence of a search result is not a theorem of nonexistence.

## Existing foundations used here

| Mathematical object or fact | Exact API / source | Role in this project |
| --- | --- | --- |
| Quadratic forms and anisotropy | `QuadraticForm`, `QuadraticMap.Anisotropic`, `QuadraticMap.not_anisotropic_iff_exists`; `Mathlib/LinearAlgebra/QuadraticForm/Basic.lean` | Actual quadratic forms, rather than an uninterpreted predicate named “quadratic form” |
| Restriction by a linear map | `QuadraticMap.comp`, `Submodule.subtype` | The restriction of an ambient quadratic form to a subspace |
| Products of linear forms | `QuadraticMap.linMulLin` | The concrete split form `q(x,y) = ∑ i, x i * y i` |
| Dimension of a sum and intersection | `Submodule.finrank_sup_add_finrank_inf_eq`, `Submodule.finrank_le`; `Mathlib/LinearAlgebra/FiniteDimensional/Lemmas.lean` | A nonzero intersection when the dimensions sum to more than the ambient dimension |
| Positive dimension gives a nonzero vector | `Module.finrank_pos_iff_exists_ne_zero`; `Mathlib/LinearAlgebra/Dimension/Finite.lean` | A genuine witness to isotropy |
| First factor as a subspace | `Submodule.fst`, `Submodule.fstEquiv`; `Mathlib/LinearAlgebra/Prod.lean` | The explicitly constructed totally isotropic subspace of the split form |
| Dimensions of function spaces and products | `Module.finrank_fin_fun`, `Module.finrank_prod`; `Mathlib/LinearAlgebra/Dimension/Constructions.lean` | The dimension counts for `Kⁿ × Kⁿ` |
| Exact total degree of a nonzero product | `MvPolynomial.totalDegree_mul_of_isDomain`; `Mathlib/RingTheory/MvPolynomial/MonomialOrder/DegLex.lean` | The polynomial degree step in the proposed theta-characteristic argument |
| Extracting relatively prime factors | `extract_gcd`, `gcd_isUnit_iff_isRelPrime`; `Mathlib/Algebra/GCDMonoid/Basic.lean` | Factoring a symmetric rank-one matrix over a gcd domain |
| Coprime cancellation of divisibility | `IsRelPrime.mul_right`, `IsRelPrime.dvd_of_dvd_mul_right`; `Mathlib/Algebra/Divisibility/Units.lean` | Deducing `a ∣ g` from `a ∣ g * b²` when `a` and `b` are relatively prime |
| Actual integral schemes and function fields | `Scheme`, `IsIntegral`, `Scheme.functionField`, `Scheme.germToFunctionField`; `Mathlib/AlgebraicGeometry/FunctionField.lean` | The function field is the actual stalk at the generic point, not a separate field postulated to model it |
| Generic injectivity and affine fraction fields | `Scheme.germToFunctionField_injective`, `functionField_isFractionRing_of_isAffineOpen` | Equality of regular functions is reflected by the actual generic map; affine coordinate rings have the actual function field as fraction field |
| Genuine sheaf gluing | `TopCat.Sheaf.existsUnique_gluing'`, `TopCat.Sheaf.eq_of_locally_eq'`; `Mathlib/Topology/Sheaves/SheafCondition/UniqueGluing.lean` | Local compatibility gives actual global sections; local bijectivity of a sheaf morphism gives global bijectivity |
| Invertibility is local | `RingedSpace.isUnit_of_isUnit_germ`; `Mathlib/Geometry/RingedSpace/Basic.lean` | A regular function that restricts to units on a cover is a unit globally |
| Actual sheaves of modules | `SheafOfModules`, `Scheme.Modules`, `SheafOfModules.unitHomEquiv`; `Mathlib/Algebra/Category/ModuleCat/Sheaf.lean`, `Mathlib/AlgebraicGeometry/Modules/Sheaf.lean` | Construct the morphism `r ↦ r • s` from a compatible section and an actual isomorphism from a local generator |
| Coherent frames and transition functions | `LinearEquiv`, `PresheafOfModules.isoMk`, actual module restriction maps | Local rank-one coordinates, restriction compatibility, and genuine changes of frame |


`EvenQuinticConic/IsotropicDimension.lean` proves the dimension argument and
also supplies an actual split quadratic form with its actual isotropic
subspace. In particular, a five-dimensional subspace of
`(Fin 4 → K) × (Fin 4 → K)`, equipped with `q(x,y) = ∑ i, x i * y i`,
has a nonzero isotropic vector.

`EvenQuinticConic/RankOneFactorization.lean` proves, for every commutative
cancellative monoid with zero equipped with a gcd structure, that
`A * D = B²` implies the existence of `h, a, b` with
`A = h * a²`, `B = h * a * b`, and `D = h * b²`.
When `A ≠ 0`, it also supplies `h ≠ 0`, `a ≠ 0`, and relatively prime `a, b`.
This is an actual factorization theorem, with no square-root hypothesis.
Applying it to sections of a line bundle still requires constructing and
justifying the polynomial lifts and their relations.

These results do **not** show that the conic-bundle hypotheses in the proposed
geometric theorem supply a Pfister form, an embedding into this split form,
or a rational point on an intersection of quadrics.

## Relevant foundations present but not sufficient

- `Mathlib/LinearAlgebra/CliffordAlgebra/Even.lean` defines
  `CliffordAlgebra.even` and its universal property. This is not the
  arithmetic classification of its Brauer class or index.
- `Mathlib/LinearAlgebra/QuadraticForm/Real.lean` contains real diagonalization
  results, including
  `QuadraticForm.equivalent_one_neg_one_weighted_sum_squared` and
  `QuadraticForm.equivalent_one_zero_neg_one_weighted_sum_squared`.
  This does not by itself give the real Clifford-algebra classification,
  real-closed-field transfer, or a signature argument over `ℝ(x,y)`.
- `Mathlib/Algebra/BrauerGroup/Defs.lean` defines central simple algebras,
  Brauer equivalence, and the quotient called `BrauerGroup`.
  Its introductory TODO list explicitly includes the abelian group operation
  and functoriality. It does not provide the Brauer-purity and residue
  machinery required by the proposed argument.
- The `Mathlib/RingTheory/WittVector` directory concerns **Witt vectors**.
  It is not a formalization of the Witt ring of quadratic forms used in the
  Pfister-form argument.

## Unfulfilled bridges in the proposed geometric proof

The following are obligations of the proposed proof, not theorems proved by
this repository. Searches of the pinned checkout did not locate the required
results under the indicated mathematical concepts or names.

| Proposed bridge | Work not supplied here |
| --- | --- |
| A smooth plane quintic and its even theta characteristic give a real symmetric linear matrix | Theta characteristics and their parity; the sheaf resolution; the real Dixon correspondence; identification of the resulting discriminant cover |
| The original conic and the matrix have the same Brauer class | Residue maps, purity, evaluation, the possible real twist of a cover, and the pseudoline argument |
| The matrix has no definite real member | The real signature / Clifford-class calculation and the local geometry of the conic bundle near a smooth discriminant point |
| The five-dimensional form is a Pfister neighbor | The Clifford-index criterion and the theory of Pfister forms and neighbors |
| Zero signatures force the required Pfister form to split | Orderings and real-closed extensions, the relevant local-global principle for the Witt ring, and the required torsion statement for `I³(ℝ(x,y))` |
| A point on the generic quadric gives a real common zero of the net | The precise zero-cycle version of the Amer–Brumer-type theorem and its application over `ℝ` |
| Hyperbolic reduction produces the needed birational model | Construction and comparison of the conic bundle with the incidence model, including the descent over `ℝ` |
| Real rationality gives the asserted number of real connected components | The real-point topology and the requisite birational invariance theorem for smooth proper real varieties |

Search terms included `Dixon`, `Pfister`, `Amer`/`Brumer`,
`theta characteristic`, `zero cycle`, Brauer purity and residues, virtual
cohomological dimension, and `birational` in the algebraic-geometry sources.
The table records the outcomes of this source audit; it does not replace a
mathematical audit of whether each proposed bridge is true with exactly the
hypotheses needed here.

## What a successful build establishes

The project now additionally uses `MvPolynomial.IsHomogeneous`, coefficient
and total-degree APIs, `IsAlgClosed.exists_pow_nat_eq`, actual
`LinearIndependent` pairs, algebra homomorphisms, and `RingHom.ker` to join the
polynomial argument in `RestrictionModel.lean`. This supplies a proved
implication for a specified algebraic restriction model. The geometric
construction of that model remains open; the additional coefficient-level
construction and local algebra are described below. The cofactor module also supports an
explicit scalar twist, so either sign may be stated without silently changing
the equation; no geometric discriminant-sign comparison is thereby proved.

A successful Lean build establishes the statements actually declared and
proved in the `.lean` files, with their displayed hypotheses. It does not
turn prose in this document, an external citation, or an unimplemented
geometric implication into a checked theorem. In particular, the partial
results here must not be reported as a completed formal proof that an even
quintic conic bundle with two real connected components cannot exist.

## New coefficient and local-algebra bridges

`GradedRestriction` constructs an actual map to `Polynomial L` retaining
homogeneous degrees, proves its coefficient formula and kernel criteria,
and checks that injective coefficient extension preserves its kernel.
`SquareExtension` uses `AlgebraicClosure L`, a genuine field, and an injective
`K`-linear map to realize the twisted products. `WeightedRestriction` avoids
that extension by leaving the common nonzero factor explicit.

`FiniteDegreeRestriction` reduces the required geometric input to injectivity
on homogeneous quartics. `GenericCoefficientModel` combines these actual
polynomial statements and produces the rational ratio with constant weighted
square. It does not construct a function field from a specified curve.

`LocalSquareUnit` uses
`IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow`,
`IsFractionRing.injective`, and `isUnit_pow_iff` to prove that a rational
positive-power root of a unit extends to a unit. `GenericPointInjection`
now applies this result to actual affine coordinate rings and actual function
fields, and the following modules supply the sheaf gluing step.

## Actual scheme and sheaf bridges now checked

`GenericPointInjection` works with `X : Scheme [IsIntegral X]` and the
actual rings `Γ(X,U)`. It proves compatibility of the canonical generic map
with restrictions and reflects equality of local representatives and units.
For a nonempty affine open, with the explicit hypothesis
`IsIntegrallyClosed Γ(X,U)`, a rational positive-power root of a unit extends
uniquely to a regular unit. The weighted square-quotient variant does not
require its denominator to be a unit in the coordinate ring.

`SheafGluing` proves unique gluing of these representatives through the
actual structure sheaf. On an integral scheme every nonempty open contains
the generic point; consequently intersections of the specified nonempty
opens are nonempty and generic injectivity applies there. A separate theorem
uses actual sheaf gluing to turn local bijectivity of a sheaf morphism on
all subopens of a cover into bijectivity on every open. None of these results
assumes a gluing operation as an extra input.

`SheafTrivialization` constructs actual morphisms and isomorphisms in
`SheafOfModules`. A compatible section gives the morphism `r ↦ r • s`;
unit coordinates in rank-one frames imply its local bijectivity, and
`SheafGluing` supplies global bijectivity. `LocalFrames` packages the local
linear equivalences together with compatibility with the actual restriction
maps. It reduces the unit checks to the covering opens, propagates those
checks to every subopen, and constructs a global generator from compatible
local generators. The resulting conclusion is an actual isomorphism
`SheafOfModules.unit R ≅ M`, not a proposition whose definition already
asserts that conclusion.

`ModuleGenericInjection` constructs the generic coefficient of a genuine
module-sheaf section in a chosen frame on a nonempty open. A cover by
coherent rank-one frames makes this map injective: equality on one nonempty
open propagates through overlaps by the integral scheme's injective
restriction maps, then the actual sheaf condition gives global equality.
Thus generic injectivity for an actual locally framed module sheaf is now
proved rather than assumed. The corresponding map from genuine global
sections is linear over the ring of global functions, with its canonical
action on the function field. Applying this construction to the specific
theta sheaf still requires the geometric object and frames. The base-field
actions for any actual scheme over `Spec K` are now supplied by
`SchemeScalarAction`, rather than being separate coherence assumptions.

`RationalSectionFrames` joins these constructions on an actual integral
scheme. Its input consists of nonempty affine opens covering the scheme,
integrally closed coordinate rings, coherent frames of an actual module
sheaf, and rational coefficients `r_i : X.functionField`. The coefficients
must transform by the transition functions **computed from those frames**,
and their positive powers must equal images of regular units. The theorem
`exists_global_generator_of_rational_frame_powers` then constructs the local
regular units, proves compatibility of the resulting module sections,
glues a global generator, and produces an actual module-sheaf isomorphism.
Its direct square-quotient variant,
`exists_global_generator_of_rational_frame_square_ratios`, starts from
`germ(a_i) x_i² = germ(b_i) y_i²` with unit coefficients and `y_i ≠ 0`.
If the quotients `x_i/y_i` satisfy the computed frame-transition equations,
it constructs local units `w_i` satisfying `a_i w_i² = b_i`, a global
generator, and the same actual isomorphism. No denominator is assumed to be
a unit in an affine coordinate ring.

## Pairings, comparison morphisms, and conditional theta vanishing

The next modules remove several former interfaces rather than assuming
them. `SchemeScalarAction` constructs the base-field algebra and module
structures from the actual structure morphism to `Spec K`. The injective
generic coefficient map is then canonically base-field-linear.

`RankOnePairing` and `ModulePairing` use actual bilinear maps on actual
modules of sections, with naturality under actual restrictions. Their
computed coefficient is a unit when the local induced tensor map is
bijective. The same coefficient gives all three generic products. The
pinned checkout provides a monoidal structure on **presheaves** of modules;
this is not used to assert that tensoring global sections computes sections
of a tensor-product sheaf. Perfection is required only on the framed local
opens.

`ModuleHomGluing` glues actual local linear morphisms, including their
naturality, and constructs an actual isomorphism from local bijectivity.
`FrameComparison` derives their compatibility using actual global sections
and generic injectivity. `PairingComparison` derives the local unit weights
from a genuine global square-pairing identity. In particular, no separate
ratio-transition equations are needed in this stronger comparison theorem.

`ThetaSectionBridge` combines these results with the polynomial argument to
construct an actual `Θ ≅ H`. `QuadraticSections` constructs the linear map
from homogeneous quadratics to actual global sections and proves its
six-monomial evaluation and generic-coefficient formulas. The final theorem
uses **surjectivity of this actual map**, instead of taking the three
generic lifting identities as independent hypotheses.

`GlobalSectionDimension` proves that an actual sheaf isomorphism induces a
base-field-linear equivalence of actual global sections. `ThetaFiniteDimension`
derives finite-dimensional theta sections from actual quadratic surjectivity:
the target square sections are generated by six monomials, and pairing with
a nonzero section gives an injection. `HyperplaneDimension` proves that the
three coordinate sections form an actual basis from quadratic surjectivity
and quartic injectivity, giving `h⁰(H)=3`. `ThetaIneffectivity` proves the
conditional implication

```
normal affine framed cover + locally tensor-perfect pairings
+ actual quadratic-map surjectivity + quartic injectivity
  ⇒ (two independent theta sections ⇒ Θ ≅ H).
```

With even dimension, the final theorem
`even_theta_ineffective_of_restriction_maps` proves every theta section is
zero. Both finite-dimensionality and `h⁰(H)=3` are now internal conclusions,
not additional assumptions. The proof establishes finite-dimensionality
before applying the finite-rank-zero criterion for actual vanishing.

## Plane-quintic algebra and remaining instantiation

`PlaneQuintic` uses the actual homogeneous ideal and `ProjectiveSpectrum`
vanishing locus, an actual quotient ring `K[X₀,X₁,X₂]/(F)`, its fraction
field, and normalized coordinate ratios. Primality and degree five imply
injectivity on homogeneous polynomials of degrees below five, including the
precise quartic input. The fraction field used here belongs to the affine
cone, not the curve. The needed next step concerns the degree-zero
coordinate ratios and their comparison with actual curve sections; it
cannot equate the whole cone fraction field with the curve's function field.
The full ungraded normalized evaluation is not asserted to be injective.

It remains to construct the actual curve scheme and its twist/theta sheaves,
obtain their normal affine framed cover and square pairings, prove actual
quadratic surjectivity, and identify their generic
coordinates with the algebraic chart model. These are explicit geometric
instantiation tasks. The later real determinantal, Brauer, quadratic-form,
birational, and connectedness bridges also remain unproved. The complete
original conic-bundle theorem is therefore still not formalized.
