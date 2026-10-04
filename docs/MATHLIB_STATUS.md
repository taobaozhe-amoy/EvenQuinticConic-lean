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
positive-power root of a unit extends to a unit. This is the required local
algebra for a normal scheme, but the sheaf restriction and gluing argument
is not supplied by this ring theorem.
