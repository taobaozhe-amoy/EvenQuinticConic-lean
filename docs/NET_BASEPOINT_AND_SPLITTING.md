# From an actual common point to a nonempty incidence minor

This update formalizes an assembled algebraic part of §7 of
[the paper argument](EVEN_THETA_CONNECTEDNESS_PROOF.md), together with the
local line-splitting interpretation needed in §2. It does not claim the
final real connectedness theorem.

## The assembled matrix-net endpoint

Work over an infinite field `K` of characteristic different from two. The
inputs are actual symmetric matrices `M : Fin 3 → Matrix (Fin 5) (Fin 5) K`,
an actual vector `P ≠ 0` with `Pᵀ Mᵢ P = 0` for each `i`, and the explicit
Jacobian condition for the actual polynomial determinant:

```text
for every t ≠ 0, det M(t) = 0 implies some ∂ᵢ(det M)(t) ≠ 0.
```

The theorem
`Incidence.exists_projective_netIncidenceMinor_after_common_point_normalization`
constructs an invertible matrix `B` whose first column is `P`, and distinct
indices `i,j` and a nonzero vector `y : Fin 4 → K` such that

\[
(l_i r_j-l_j r_i)(y)\ne0.
\]

Here `Aᵢ = Bᵀ Mᵢ B`, and both rows are extracted from these actual matrices:

\[
l_i=\sum_{a=0}^3 (A_i)_{a+1,0}y_a,\qquad
r_i=\sum_{a,b=0}^3(A_i)_{a+1,b+1}y_ay_b.
\]

No coordinate choice, linear independence, normalized polynomial expression,
nonzero generic determinant, absence of common factors, nonzero minor, or
nonempty minor chart is an extra hypothesis of this endpoint.

The further theorem `Incidence.exists_nonempty_affineConeIncidenceChart_of_common_point`
uses the same inputs and the field-valued evaluation to prove that an actual
scheme `netAffineConeIncidenceChart` is nonempty. This scheme is `Spec` of the
two-equation incidence quotient over the localization of `K[y₀,…,y₃]` at the
chosen minor; the three selected columns are proved distinct. The previously
constructed scheme isomorphism identifies it with the actual minor principal
open of this affine coefficient spectrum. It remains an affine cone chart.

Its proof combines the following checked steps:

1. `NetCoordinateChange.lean` constructs `B` and proves the actual polynomial
   identities `det A(t)=det(B)² det M(t)` and the corresponding identities for
   every formal partial derivative. The Jacobian condition is transported.
2. `NetBasePoint.lean` derives `adj A = c P Pᵀ` from a nonzero kernel vector
   when the adjugate is nonzero. Jacobi's formula then shows that a common
   point in a matrix kernel annihilates all determinant partials. This yields
   actual independence of the polar coefficients.
3. `LinearCoordinateNormalization.lean` extends those independent coefficient
   vectors to a basis and constructs inverse polynomial substitutions. Both
   directions preserve homogeneous degrees. The three polar forms become
   the first three coordinate variables.
4. `NetIncidenceNonempty.lean` uses that equivalence to descend the common
   factor forced by vanishing minors back to the original rows. It proves
   directly from the matrix entries that `Qᵢ=2x₀lᵢ+rᵢ`.
5. `IncidenceMinorFromDeterminant.lean` computes the Hessian of `xᵀMx` as
   `M+Mᵀ`. The Hessian at zero of a linear polynomial times any polynomial
   factors through a two-dimensional space. Thus the purported common
   factor would force the actual five-by-five generic determinant to vanish.
6. The Jacobian condition excludes an identically zero determinant. A
   nonzero polynomial minor takes a nonzero value over the infinite field,
   and that witnessing vector is proved nonzero.

The lower-level normalized-row theorem remains available with an explicit
normalized polynomial expression; the assembled endpoint discharges that
expression internally for the actual extracted rows.

## Local line factors of the actual ternary conic

`TernaryConicSplitting.lean` treats an actual symmetric three-by-three matrix
`M` with `det M = 0` and `adj M 0 0 ≠ 0`. It proves

\[
q_M=L_1L_2\text{ with }L_1,L_2\text{ linearly independent}
\iff -\operatorname{adj}(M)_{00}\text{ is a square}
\iff \exists w,\ w_iw_j=-\operatorname{adj}(M)_{ij}.
\]

The `Lᵢ` are actual homogeneous degree-one polynomials. Their linear
independence excludes zero or proportional factors, so the two lines are
distinct. The polynomial `q_M` is proved to evaluate to the actual matrix
form `xᵀMx`. The forward direction extracts the signed-cofactor square; the
reverse constructs factors by completing the nondegenerate binary block,
including the case where its first diagonal entry is zero.

Over `ℝ` the equivalent condition is `adj M 0 0 < 0`. This checks the
geometric meaning of the negative sign used for ternary conics. It does not
replace the positive sign for the rank-four quotient of a five-dimensional
net, and does not construct the global relative Fano scheme.

## Remaining boundaries

- Existence of the real net from the original even theta, and existence of
  its common real point, still require the unformalized earlier steps of the
  paper argument. The endpoint above receives these matrices and point.
- Its smoothness input is the explicit polynomial Jacobian condition; a
  converse from the original scheme-theoretic hypotheses is not supplied.
- The nonzero vector `y` represents a projective point, but this fact alone
  is not a scheme isomorphism with a projective incidence chart.
- A principal open in the four-variable affine coefficient spectrum is an
  open of the affine cone. Identifying the quotient by projective scaling
  with an open of `ℙ³`, proving density and dominance, and comparing its
  generic conic with the original conic bundle remain necessary.
- The global real cover comparison, Brauer argument, Albert–Pfister and
  zero-cycle inputs, and real connectedness conclusion remain unformalized.

See [the renewed correctness review](RECHECK_2026_10_16.md) for the distinction
between the paper-level audit and these kernel-checked conditional results.
