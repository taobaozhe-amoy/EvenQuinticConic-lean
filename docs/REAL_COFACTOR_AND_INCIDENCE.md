# Real cofactor parameters and affine incidence charts

This stage formalizes concrete local steps in the paper proof
[EVEN_THETA_CONNECTEDNESS_PROOF.md](EVEN_THETA_CONNECTEDNESS_PROOF.md).
It does not assert the final real connectedness theorem.

## Determinant gradient and cofactor charts

`DeterminantGradient.lean` proves Jacobi's formula for an actual algebraic
derivation from the determinant permutation expansion and the Leibniz rule.
Its polynomial specialization proves

\[
\partial_i\det M=\sum_{r,c}\partial_i(M_{rc})\operatorname{adj}(M)_{cr}.
\]

The evaluated formula uses the adjugate of the evaluated matrix. Thus a
nonzero evaluated partial derivative forces that adjugate to be nonzero.
`exists_diagonal_adjugate_ne_zero_of_gradient` combines this result with
the symmetric-matrix results below. Its inputs are the actual polynomial
matrix, a field-valued point, symmetry of the evaluated matrix, the
determinant equation, and nonvanishing of an actual partial derivative.
No derivative formula or corank-one conclusion is supplied as a hypothesis.

`AdjugateRankOne.lean` proves the pivot-minor identities previously supplied
to `CofactorCover.lean`. Replacing a row by a coordinate row constructs an
invertible matrix when the corresponding cofactor is nonzero. This shows
that the kernel coordinate is injective and forces adjugate minors to vanish.
For a symmetric singular matrix with nonzero adjugate, a nonzero diagonal
cofactor exists. On two nonzero diagonal charts,

\[
\frac{\operatorname{adj}(M)_{jj}}{\operatorname{adj}(M)_{kk}}
=\left(\frac{\operatorname{adj}(M)_{jk}}
{\operatorname{adj}(M)_{kk}}\right)^2,
\]

and the displayed transition factor is nonzero. The file also constructs
an explicit equivalence between cofactor-root vectors and roots of the
signed pivot parameter.

## Actual real quadratic algebras and signs

`RealKummer.lean` uses the existing actual algebra
`KummerAlgebra u = QuadraticAlgebra R u 0`. Evaluation at a root is an
actual algebra homomorphism; conversely every scalar-valued algebra map
is determined by its generator image. These give an explicit equivalence
between algebra maps and scalar roots.

Over the reals it proves

\[
\operatorname{Hom}_{\mathbb R\text{-alg}}(\mathbb R[t]/(t^2-u),\mathbb R)
\ne\varnothing\iff u\ge0.
\]

For a nonzero parameter this is equivalent to strict positivity. If
`v ≠ 0`, an actual real-algebra isomorphism between the parameters `u,v`
exists exactly when `u/v > 0`. Necessity follows from the actual trace-zero
transition unit. Sufficiency constructs both maps explicitly using
`t ↦ sqrt(u/v) t` and its inverse.

`RealCofactor.lean` connects these results to actual symmetric singular
matrices. A chosen nonzero diagonal pivot gives an equivalence of types
between vector cofactor roots and actual real-algebra points of the signed
Kummer algebra. A positive signed pivot gives exactly two vector roots;
a negative signed pivot gives none. The ternary convention uses twist `-1`
and the quinary convention uses twist `1` in separate named theorems.
`cofactorPivotKummerEquiv` constructs the algebra isomorphism attached to two
nonzero diagonal cofactors from the proved matrix transition formula. This
isomorphism itself also permits a zero twist; the real positivity and
two-point assertions require a nonzero twist.

These are local algebra and field-valued statements. They do not yet
identify the cofactor equations with the geometric discriminant cover.
In particular, an isomorphism of two real fiber algebras is not a proof
that two covers over the whole discriminant curve are isomorphic.

## Incidence equations as actual affine schemes

`IncidenceAffineChart.lean` starts with the actual quotient algebra

\[
R[T_0,T_1]/(a_0T_0+a_1T_1+a_2,\ b_0T_0+b_1T_1+b_2).
\]

When the minor `a₀b₁-a₁b₀` has a specified inverse, elimination constructs
an `R`-algebra equivalence with `R` and proves both inverse identities.
Applying `Spec` constructs an actual scheme isomorphism, whose forward
map is proved to be the original base projection. The localized version
inverts the minor internally and identifies the result with the actual
principal open of `Spec R`. This works even for an empty principal open;
nonemptiness is a separate conclusion requiring a witness.

`IncidenceNonzeroMinor.lean` proves the polynomial obstruction for the
normalized independent linear row `(X₀,X₁,X₂)` in four variables. If all
minors with a row `rᵢ` vanish, coefficientwise divisibility and cancellation
construct a single polynomial `h` with `rᵢ=Xᵢh`. If the `rᵢ` are homogeneous
quadrics, `h` is homogeneous linear, and every pencil member factors.
Consequently, excluding this common linear factor gives a nonzero minor.
Over an infinite field it constructs a nonzero parameter vector at which
the minor does not vanish and nonempty existing incidence set charts,
with all three selected column indices distinct.

## Remaining connections

- Construct the symmetric determinantal representation from the actual real
  ineffective theta characteristic.
- Identify cofactor/Kummer charts with the actual discriminant-cover
  morphism, including the real line bundle and global square trivialization.
- Prove the global real twist comparison, Brauer-class equality, Clifford
  index bound, and indefiniteness at every ordering.
- Formalize the Albert/Pfister and zero-cycle inputs and their application.
- Derive independence and coordinate normalization of the three linear
  forms from the actual smooth determinant geometry; derive exclusion of
  the common linear factor rather than supplying it as a hypothesis.
- Identify the affine incidence scheme with the corresponding open of the
  global projective incidence scheme, prove density and dominance, and
  compare its generic conic to the original bundle.
- Derive real rationality and connectedness of the original real-point
  space without a connectedness input.

The actual Jacobian-to-nonzero-adjugate implication is now proved. This
does not by itself instantiate a polynomial matrix from the original
geometric conic-bundle data. Compilation and the namespace axiom audit
certify the precise source statements, not these remaining connections.
