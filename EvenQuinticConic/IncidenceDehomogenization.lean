import EvenQuinticConic.NetIncidenceNonempty
import EvenQuinticConic.GradedRestriction
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Actual incidence equations in a projective affine chart

Setting a chosen nonzero homogeneous coordinate equal to one is an actual
polynomial algebra homomorphism from four variables to three. Homogeneity
of the linear and quadratic rows, and hence of their cubic minors, proves
that a nonzero minor remains nonzero after this normalization. The final
existence result derives such a three-dimensional affine chart from the
actual symmetric net, common point, and determinant Jacobian condition.

The definitions in this file concern coordinate polynomials. Identification
with an open subscheme of projective space is a separate scheme-theoretic
construction, rather than part of the meaning of the word "chart" here.
-/

noncomputable section
namespace EvenQuinticConic.Incidence
open MvPolynomial

section ChartCoordinates

variable {K : Type*} [CommSemiring K] {n : ℕ}

/-- The representative whose chosen homogeneous coordinate is one. -/
def chartLift (p : Fin (n + 1)) (x : Fin n → K) : Fin (n + 1) → K :=
  Fin.insertNth p 1 x

/-- Set the chosen coordinate equal to one and retain the other coordinates
in their original order. -/
def dehomogenizeAt (p : Fin (n + 1)) :
    MvPolynomial (Fin (n + 1)) K →ₐ[K] MvPolynomial (Fin n) K :=
  aeval (Fin.insertNth p 1 X)

@[simp] theorem chartLift_pivot (p : Fin (n + 1)) (x : Fin n → K) :
    chartLift p x p = 1 := by simp [chartLift]

@[simp] theorem chartLift_succAbove (p : Fin (n + 1)) (x : Fin n → K) (j : Fin n) :
    chartLift p x (p.succAbove j) = x j := by simp [chartLift]

@[simp] theorem dehomogenizeAt_C (p : Fin (n + 1)) (c : K) :
    dehomogenizeAt p (C c) = C c := by simp [dehomogenizeAt]

@[simp] theorem dehomogenizeAt_X_pivot (p : Fin (n + 1)) :
    dehomogenizeAt (K := K) p (X p) = 1 := by simp [dehomogenizeAt]

@[simp] theorem dehomogenizeAt_X_succAbove (p : Fin (n + 1)) (j : Fin n) :
    dehomogenizeAt (K := K) p (X (p.succAbove j)) = X j := by
  simp [dehomogenizeAt]

/-- Evaluation of the dehomogenized polynomial is evaluation at the
representative with pivot coordinate one. -/
theorem eval_dehomogenizeAt (p : Fin (n + 1)) (x : Fin n → K)
    (F : MvPolynomial (Fin (n + 1)) K) :
    eval x (dehomogenizeAt p F) = eval (chartLift p x) F := by
  change eval x (eval₂ C (Fin.insertNth p 1 X) F) = _
  rw [← eval_assoc]
  congr 2
  apply Fin.eq_insertNth_iff.mpr
  constructor
  · simp
  · funext j
    simp [Fin.removeNth]

/-- Every polynomial in the retained affine coordinates comes from an
actual homogeneous-coordinate polynomial under this algebra map. -/
theorem dehomogenizeAt_rename_succAbove (p : Fin (n + 1))
    (F : MvPolynomial (Fin n) K) :
    dehomogenizeAt p (rename p.succAbove F) = F := by
  have h : (dehomogenizeAt p).comp (rename p.succAbove) =
      AlgHom.id K (MvPolynomial (Fin n) K) := by
    ext j
    simp
  exact congrArg (fun f : MvPolynomial (Fin n) K →ₐ[K] MvPolynomial (Fin n) K => f F) h

end ChartCoordinates

section Normalization

variable {K : Type*} [Field K] {n : ℕ}

/-- Affine coordinates obtained by dividing by the selected homogeneous
coordinate. The nonzero-pivot condition is used in the normalization proofs. -/
def chartCoordinates (p : Fin (n + 1)) (y : Fin (n + 1) → K) : Fin n → K :=
  fun j => y (p.succAbove j) / y p

/-- The normalized representative differs from the original vector by
multiplication by one common nonzero scalar. -/
theorem chartLift_chartCoordinates (p : Fin (n + 1)) (y : Fin (n + 1) → K)
    (hp : y p ≠ 0) :
    chartLift p (chartCoordinates p y) = fun i => y i * (y p)⁻¹ := by
  apply Fin.insertNth_eq_iff.mpr
  constructor
  · exact (mul_inv_cancel₀ hp).symm
  · funext j
    simp [chartCoordinates, Fin.removeNth, div_eq_mul_inv]

/-- Dehomogenizing a degree-`d` form multiplies its value by precisely the
inverse `d`-th power of the chosen homogeneous coordinate. -/
theorem eval_dehomogenizeAt_chartCoordinates (p : Fin (n + 1))
    (y : Fin (n + 1) → K) (hp : y p ≠ 0)
    (F : MvPolynomial (Fin (n + 1)) K) (d : ℕ) (hF : F.IsHomogeneous d) :
    eval (chartCoordinates p y) (dehomogenizeAt p F) = eval y F * (y p)⁻¹ ^ d := by
  rw [eval_dehomogenizeAt, chartLift_chartCoordinates p y hp]
  exact homogeneous_eval₂_scale (RingHom.id K) y (y p)⁻¹ F d hF

/-- Nonvanishing survives normalization in every chart containing the
original representative. -/
theorem eval_dehomogenizeAt_ne_zero (p : Fin (n + 1))
    (y : Fin (n + 1) → K) (hp : y p ≠ 0)
    (F : MvPolynomial (Fin (n + 1)) K) (d : ℕ) (hF : F.IsHomogeneous d)
    (hy : eval y F ≠ 0) :
    eval (chartCoordinates p y) (dehomogenizeAt p F) ≠ 0 := by
  rw [eval_dehomogenizeAt_chartCoordinates p y hp F d hF]
  exact mul_ne_zero hy (pow_ne_zero _ (inv_ne_zero hp))

/-- A nonzero representative where a homogeneous form does not vanish
supplies an actual affine-coordinate point in some projective chart. -/
theorem exists_dehomogenizeAt_eval_ne_zero
    (F : MvPolynomial (Fin (n + 1)) K) (d : ℕ) (hF : F.IsHomogeneous d)
    (y : Fin (n + 1) → K) (hy : y ≠ 0) (hFy : eval y F ≠ 0) :
    ∃ (p : Fin (n + 1)) (x : Fin n → K), eval x (dehomogenizeAt p F) ≠ 0 := by
  obtain ⟨p, hp⟩ : ∃ p, y p ≠ 0 := by
    by_contra h
    push_neg at h
    exact hy (funext h)
  exact ⟨p, chartCoordinates p y, eval_dehomogenizeAt_ne_zero p y hp F d hF hFy⟩

end Normalization

section NetRows

variable {K : Type*} [Field K]

/-- The quadratic polynomial extracted from a matrix is homogeneous of
degree two, without a symmetry assumption. -/
theorem matrixQuadraticPolynomial_homogeneous {ι : Type*} [Fintype ι]
    (M : Matrix ι ι K) : (matrixQuadraticPolynomial M).IsHomogeneous 2 := by
  classical
  apply IsHomogeneous.sum
  intro i _
  apply IsHomogeneous.sum
  intro j _
  exact (isHomogeneous_C_mul_X (M i j) i).mul (isHomogeneous_X K j)

/-- The actual polar row consists of linear homogeneous forms. -/
theorem netLinearRow_homogeneous (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (i : Fin 3) :
    (netLinearRow M i).IsHomogeneous 1 :=
  coefficientLinearPolynomial_homogeneous _

/-- The actual restricted row consists of quadratic homogeneous forms. -/
theorem netQuadraticRow_homogeneous (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (i : Fin 3) :
    (netQuadraticRow M i).IsHomogeneous 2 :=
  matrixQuadraticPolynomial_homogeneous _

/-- Each actual incidence minor is a cubic homogeneous form. -/
theorem netIncidenceMinor_homogeneous (M : Fin 3 → Matrix (Fin 5) (Fin 5) K)
    (i j : Fin 3) : (netIncidenceMinor M i j).IsHomogeneous 3 :=
  ((netLinearRow_homogeneous M i).mul (netQuadraticRow_homogeneous M j)).sub
    ((netLinearRow_homogeneous M j).mul (netQuadraticRow_homogeneous M i))

/-- The actual cubic minor after passing to the selected projective affine
coordinates. -/
def netDehomogenizedMinor (M : Fin 3 → Matrix (Fin 5) (Fin 5) K)
    (p : Fin 4) (i j : Fin 3) : MvPolynomial (Fin 3) K :=
  dehomogenizeAt p (netIncidenceMinor M i j)

/-- Dehomogenization respects the displayed two-by-two determinant. -/
theorem netDehomogenizedMinor_eq (M : Fin 3 → Matrix (Fin 5) (Fin 5) K)
    (p : Fin 4) (i j : Fin 3) :
    netDehomogenizedMinor M p i j =
      dehomogenizeAt p (netLinearRow M i) * dehomogenizeAt p (netQuadraticRow M j) -
      dehomogenizeAt p (netLinearRow M j) * dehomogenizeAt p (netQuadraticRow M i) := by
  simp [netDehomogenizedMinor, netIncidenceMinor]

/-- The original nonvanishing minor produces an actual nonvanishing
polynomial evaluation in three, rather than four, affine coordinates. -/
theorem exists_netDehomogenizedMinor_eval_ne_zero
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K)
    (i j : Fin 3) (y : Fin 4 → K) (hy : y ≠ 0)
    (hminor : eval y (netIncidenceMinor M i j) ≠ 0) :
    ∃ (p : Fin 4) (x : Fin 3 → K), eval x (netDehomogenizedMinor M p i j) ≠ 0 :=
  exists_dehomogenizeAt_eval_ne_zero _ 3 (netIncidenceMinor_homogeneous M i j) y hy hminor

/-- Starting from the actual matrix net and arbitrary common point, derive
an invertible point normalization and an actual affine chart of projective
three-space on which an incidence minor is nonzero. -/
theorem exists_netDehomogenizedMinor_after_common_point_normalization
    [Infinite K] (h2 : (2 : K) ≠ 0)
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K)
    (hM : ∀ i, (M i).IsSymm)
    (P : Fin 5 → K) (hP : P ≠ 0)
    (hisotropic : ∀ i, dotProduct P ((M i).mulVec P) = 0)
    (hsmooth : ∀ t : Fin 3 → K, t ≠ 0 → eval t (linearMatrixNet M).det = 0 →
      ∃ i, eval t (pderiv i (linearMatrixNet M).det) ≠ 0) :
    ∃ B : Matrix (Fin 5) (Fin 5) K, B.det ≠ 0 ∧ (∀ j, B j 0 = P j) ∧
      ∃ (i j : Fin 3) (p : Fin 4) (x : Fin 3 → K), i ≠ j ∧
        eval x (netDehomogenizedMinor (matrixNetCongruence M B) p i j) ≠ 0 := by
  obtain ⟨B, hB, hcol, i, j, y, hij, hy, hminor⟩ :=
    exists_projective_netIncidenceMinor_after_common_point_normalization
      h2 M hM P hP hisotropic hsmooth
  obtain ⟨p, x, hx⟩ := exists_netDehomogenizedMinor_eval_ne_zero
    (matrixNetCongruence M B) i j y hy hminor
  exact ⟨B, hB, hcol, i, j, p, x, hij, hx⟩

end NetRows
end EvenQuinticConic.Incidence
