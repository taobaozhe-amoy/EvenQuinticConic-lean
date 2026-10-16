import EvenQuinticConic.IncidenceNonzeroMinor
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Excluding the incidence common factor using the actual determinant

A product of a linear polynomial and any polynomial has a Hessian at the
origin of rank at most two. We apply this calculation to a normalized net
of symmetric five-by-five matrices. Consequently a nonzero generic
determinant excludes the common-factor case in `IncidenceNonzeroMinor`.

The coordinate normalization remains an explicit hypothesis. No smoothness,
projective-coordinate change, or global incidence identification is inferred.
-/

noncomputable section

set_option maxRecDepth 4096

namespace EvenQuinticConic.Incidence

open MvPolynomial

section Hessian

variable {R : Type*} [CommRing R]

/-- The polynomial `xᵀ M x`, with both off-diagonal entries included. -/
def matrixQuadraticPolynomial {n : Type*} [Fintype n] (M : Matrix n n R) :
    MvPolynomial n R := ∑ i, ∑ j, C (M i j) * X i * X j

/-- The actual formal Hessian evaluated at the origin. -/
def hessianAtZero {n : Type*} (p : MvPolynomial n R) : Matrix n n R :=
  fun i j => eval (fun _ => 0) (pderiv i (pderiv j p))

/-- A homogeneous linear polynomial with its displayed coefficients. -/
def linearPolynomial {n : Type*} [Fintype n] (a : n → R) : MvPolynomial n R :=
  ∑ i, C (a i) * X i

@[simp] theorem pderiv_linearPolynomial {n : Type*} [Fintype n] (a : n → R) (j : n) :
    pderiv j (linearPolynomial a) = C (a j) := by
  classical
  simp [linearPolynomial, Pi.single_apply]

@[simp] theorem eval_zero_linearPolynomial {n : Type*} [Fintype n] (a : n → R) :
    eval (fun _ => 0) (linearPolynomial a) = 0 := by
  simp [linearPolynomial]

/-- This calculation does not assume that the second factor is linear. -/
theorem hessianAtZero_linear_mul {n : Type*} [Fintype n]
    (a : n → R) (g : MvPolynomial n R) (i j : n) :
    hessianAtZero (linearPolynomial a * g) i j =
      a j * eval (fun _ => 0) (pderiv i g) +
      a i * eval (fun _ => 0) (pderiv j g) := by
  classical
  simp [hessianAtZero, linearPolynomial, Pi.single_apply]
  ring

theorem hessianAtZero_matrixQuadraticPolynomial {n : Type*} [Fintype n]
    (M : Matrix n n R) :
    hessianAtZero (matrixQuadraticPolynomial M) = M + M.transpose := by
  classical
  ext i j
  simp [hessianAtZero, matrixQuadraticPolynomial,
    Pi.single_apply, Finset.sum_add_distrib, Matrix.transpose_apply,
    Matrix.add_apply]

/-- Every five-by-five matrix of the form `a bᵀ + b aᵀ` is singular.
The proof factors it through a two-dimensional vector space. -/
theorem det_outer_sum_eq_zero_field {K : Type*} [Field K]
    (a b : Fin 5 → K) : Matrix.det (fun i j => a i * b j + b i * a j : Matrix (Fin 5) (Fin 5) K) = 0 := by
  let A : Matrix (Fin 5) (Fin 2) K := fun i j => if j = 0 then a i else b i
  let B : Matrix (Fin 2) (Fin 5) K := fun i j => if i = 0 then b j else a j
  have hfactor : (fun i j => a i * b j + b i * a j : Matrix (Fin 5) (Fin 5) K) = A * B := by
    ext i j
    simp [Matrix.mul_apply, Fin.sum_univ_two, A, B]
  rw [hfactor]
  by_contra hdet
  have hunit : IsUnit (A * B) := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  have hfull := Matrix.rank_of_isUnit (A * B) hunit
  have hle := (Matrix.rank_mul_le_left A B).trans (Matrix.rank_le_card_width A)
  simp only [Fintype.card_fin] at hfull hle
  omega

/-- The singularity identity also holds over any integral domain. -/
theorem det_outer_sum_eq_zero [IsDomain R] (a b : Fin 5 → R) :
    Matrix.det (fun i j => a i * b j + b i * a j : Matrix (Fin 5) (Fin 5) R) = 0 := by
  let f := algebraMap R (FractionRing R)
  apply IsFractionRing.injective R (FractionRing R)
  rw [map_zero, RingHom.map_det]
  change Matrix.det (fun i j => f (a i * b j + b i * a j)) = 0
  simpa only [map_add, map_mul] using
    det_outer_sum_eq_zero_field (fun i => f (a i)) (fun i => f (b i))

theorem det_hessianAtZero_linear_mul [IsDomain R]
    (a : Fin 5 → R) (g : MvPolynomial (Fin 5) R) :
    (hessianAtZero (linearPolynomial a * g)).det = 0 := by
  have heq : hessianAtZero (linearPolynomial a * g) =
      (fun i j => a i * eval (fun _ => 0) (pderiv j g) +
        eval (fun _ => 0) (pderiv i g) * a j) := by
    ext i j
    rw [hessianAtZero_linear_mul]
    ring
  rw [heq]
  exact det_outer_sum_eq_zero (R := R) a (fun i => eval (fun _ => 0) (pderiv i g))

/-- A symmetric five-dimensional quadratic form divisible by a linear
polynomial has zero determinant, with characteristic two explicitly excluded. -/
theorem det_eq_zero_of_matrixQuadraticPolynomial_factor [IsDomain R]
    (h2 : (2 : R) ≠ 0) (M : Matrix (Fin 5) (Fin 5) R)
    (hM : M.IsSymm) (a : Fin 5 → R) (g : MvPolynomial (Fin 5) R)
    (hfactor : matrixQuadraticPolynomial M = linearPolynomial a * g) : M.det = 0 := by
  have hh := det_hessianAtZero_linear_mul a g
  rw [← hfactor, hessianAtZero_matrixQuadraticPolynomial, hM] at hh
  have hdouble : M + M = (2 : R) • M := by ext i j; simp [two_mul]
  rw [hdouble, Matrix.det_smul] at hh
  exact (mul_eq_zero.mp hh).resolve_left (pow_ne_zero _ h2)

end Hessian

section GenericNet

variable {K : Type*} [Field K]

/-- The actual generic matrix of a net, over the three-variable parameter ring. -/
def genericNetMatrix (A : Fin 3 → Matrix (Fin 5) (Fin 5) K) :
    Matrix (Fin 5) (Fin 5) (MvPolynomial (Fin 3) K) :=
  fun i j => ∑ k, X k * C (A k i j)

/-- Extending coefficients of the four-variable row and adjoining the
first, distinguished coordinate. -/
def liftedQuadraticRow (r : MvPolynomial (Fin 4) K) :
    MvPolynomial (Fin 5) (MvPolynomial (Fin 3) K) :=
  map C (rename Fin.succ r)

/-- The coefficient vector of the generic linear row `Σ tᵢ yᵢ`. -/
def genericLinearCoefficients : Fin 5 → MvPolynomial (Fin 3) K :=
  fun j => ∑ i : Fin 3, if i.castSucc.succ = j then X i else 0

theorem genericLinearPolynomial :
    linearPolynomial (genericLinearCoefficients (K := K)) =
      ∑ i : Fin 3, C (X i) * X i.castSucc.succ := by
  classical
  simp only [linearPolynomial, genericLinearCoefficients, map_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp [apply_ite, eq_comm]

theorem matrixQuadraticPolynomial_genericNetMatrix
    (A : Fin 3 → Matrix (Fin 5) (Fin 5) K) :
    matrixQuadraticPolynomial (genericNetMatrix A) =
      ∑ k, C (X k) * map C (matrixQuadraticPolynomial (A k)) := by
  simp only [matrixQuadraticPolynomial, genericNetMatrix, map_sum, map_mul,
    MvPolynomial.map_C, MvPolynomial.map_X, Finset.sum_mul, Finset.mul_sum]
  calc
    _ = ∑ i : Fin 5, ∑ k : Fin 3, ∑ j : Fin 5,
        C (X k) * C (C (A k i j)) * X i * X j := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = ∑ k : Fin 3, ∑ i : Fin 5, ∑ j : Fin 5,
        C (X k) * C (C (A k i j)) * X i * X j := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

theorem genericNetMatrix_isSymm
    (A : Fin 3 → Matrix (Fin 5) (Fin 5) K) (hA : ∀ i, (A i).IsSymm) :
    (genericNetMatrix A).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  simp only [genericNetMatrix]
  apply Finset.sum_congr rfl
  intro k _
  rw [(hA k).apply]

/-- The actual generic matrix represents the normalized polynomial net. -/
theorem genericNetMatrix_normalized_polynomial
    (A : Fin 3 → Matrix (Fin 5) (Fin 5) K)
    (r : Fin 3 → MvPolynomial (Fin 4) K)
    (hA : ∀ i, matrixQuadraticPolynomial (A i) =
      2 * X 0 * X i.castSucc.succ + rename Fin.succ (r i)) :
    matrixQuadraticPolynomial (genericNetMatrix A) =
      ∑ i, C (X i) * (2 * X 0 * X i.castSucc.succ + liftedQuadraticRow (r i)) := by
  rw [matrixQuadraticPolynomial_genericNetMatrix]
  apply Finset.sum_congr rfl
  intro i _
  rw [hA i]
  simp [liftedQuadraticRow]

/-- A common factor of the normalized row forces the actual generic
five-by-five determinant to vanish. -/
theorem genericNetMatrix_det_eq_zero_of_common_factor
    (h2 : (2 : K) ≠ 0)
    (A : Fin 3 → Matrix (Fin 5) (Fin 5) K)
    (hsym : ∀ i, (A i).IsSymm)
    (r : Fin 3 → MvPolynomial (Fin 4) K)
    (hA : ∀ i, matrixQuadraticPolynomial (A i) =
      2 * X 0 * X i.castSucc.succ + rename Fin.succ (r i))
    (h : MvPolynomial (Fin 4) K)
    (hh : ∀ i, r i = coordinateLinear i * h) :
    (genericNetMatrix A).det = 0 := by
  refine det_eq_zero_of_matrixQuadraticPolynomial_factor
    (R := MvPolynomial (Fin 3) K) ?_ (genericNetMatrix A) ?_
    genericLinearCoefficients (2 * X 0 + liftedQuadraticRow h) ?_
  · intro hz
    apply h2
    have hzK := congrArg (constantCoeff (σ := Fin 3) (R := K)) hz
    simpa only [map_ofNat, map_zero] using hzK
  · exact genericNetMatrix_isSymm A hsym
  · rw [genericNetMatrix_normalized_polynomial A r hA, genericLinearPolynomial,
      Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [hh i]
    simp only [liftedQuadraticRow, coordinateLinear, map_mul, rename_X,
      MvPolynomial.map_X]
    ring

/-- This supplies the missing no-common-linear-factor hypothesis directly
from the determinant of the actual normalized net. -/
theorem no_common_linear_factor_of_genericNetMatrix_det_ne_zero
    (h2 : (2 : K) ≠ 0)
    (A : Fin 3 → Matrix (Fin 5) (Fin 5) K)
    (hsym : ∀ i, (A i).IsSymm)
    (r : Fin 3 → MvPolynomial (Fin 4) K)
    (hA : ∀ i, matrixQuadraticPolynomial (A i) =
      2 * X 0 * X i.castSucc.succ + rename Fin.succ (r i))
    (hdet : (genericNetMatrix A).det ≠ 0) :
    ¬ ∃ h : MvPolynomial (Fin 4) K, h.IsHomogeneous 1 ∧
      ∀ i, r i = coordinateLinear i * h := by
  rintro ⟨h, _, hh⟩
  exact hdet (genericNetMatrix_det_eq_zero_of_common_factor h2 A hsym r hA h hh)

/-- A nonsingular generic normalized net has a nonzero incidence minor. -/
theorem exists_coordinateMinor_ne_zero_of_genericNetMatrix_det_ne_zero
    (h2 : (2 : K) ≠ 0)
    (A : Fin 3 → Matrix (Fin 5) (Fin 5) K)
    (hsym : ∀ i, (A i).IsSymm)
    (r : Fin 3 → MvPolynomial (Fin 4) K)
    (hr : ∀ i, (r i).IsHomogeneous 2)
    (hA : ∀ i, matrixQuadraticPolynomial (A i) =
      2 * X 0 * X i.castSucc.succ + rename Fin.succ (r i))
    (hdet : (genericNetMatrix A).det ≠ 0) :
    ∃ i j, coordinateMinor r i j ≠ 0 :=
  exists_coordinateMinor_ne_zero r hr
    (no_common_linear_factor_of_genericNetMatrix_det_ne_zero h2 A hsym r hA hdet)

/-- Over an infinite field the resulting incidence chart is genuinely
nonempty, with all three columns represented once. -/
theorem exists_nonempty_reorderedIncidenceChart_of_genericNetMatrix_det_ne_zero
    [Infinite K] (h2 : (2 : K) ≠ 0)
    (A : Fin 3 → Matrix (Fin 5) (Fin 5) K)
    (hsym : ∀ i, (A i).IsSymm)
    (r : Fin 3 → MvPolynomial (Fin 4) K)
    (hr : ∀ i, (r i).IsHomogeneous 2)
    (hA : ∀ i, matrixQuadraticPolynomial (A i) =
      2 * X 0 * X i.castSucc.succ + rename Fin.succ (r i))
    (hdet : (genericNetMatrix A).det ≠ 0) :
    ∃ i j k : Fin 3, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      Nonempty (IncidenceChart (selectedCoordinateRow i j k) (selectedQuadraticRow r i j k)) :=
  exists_nonempty_reorderedIncidenceChart r hr
    (no_common_linear_factor_of_genericNetMatrix_det_ne_zero h2 A hsym r hA hdet)

end GenericNet

end EvenQuinticConic.Incidence
