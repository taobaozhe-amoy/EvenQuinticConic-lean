import EvenQuinticConic.IncidenceFiberNondegeneracy
import EvenQuinticConic.GeometricJacobianTransfer

/-!
# Actual matrix-net Jacobian data over parameter extension fields

The radical-ideal Jacobian certificate transfers to every coefficient
extension. We apply it to the actual determinant matrix, so a nonzero
parameter always has nonzero adjugate, even when its determinant vanishes.
This is the precise geometric input needed for fiberwise conic elimination.
-/

noncomputable section
set_option maxRecDepth 4096
namespace EvenQuinticConic.Incidence
open Matrix MvPolynomial

variable {K E : Type*} [Field K] [Field E]

/-- Vanishing of the adjugate implies vanishing of the determinant in the
actual positive matrix size used by the conic construction. -/
theorem det_eq_zero_of_adjugate_eq_zero_five
    (A : Matrix (Fin 5) (Fin 5) K) (h : A.adjugate = 0) : A.det = 0 := by
  have he := congrFun (congrFun (Matrix.mul_adjugate A) 0) 0
  simpa [h] using he.symm

/-- At every nonzero parameter the Jacobian condition ensures a nonzero
actual adjugate; determinant-zero parameters are included. -/
theorem linearMatrixNet_adjugate_ne_zero_of_jacobian
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K)
    (hJac : ∀ t : Fin 3 → K, t ≠ 0 → eval t (linearMatrixNet M).det = 0 →
      ∃ i, eval t (pderiv i (linearMatrixNet M).det) ≠ 0)
    (t : Fin 3 → K) (ht : t ≠ 0) :
    ((linearMatrixNet M).map (eval t)).adjugate ≠ 0 := by
  intro ha
  have hd := det_eq_zero_of_adjugate_eq_zero_five _ ha
  have he : eval t (linearMatrixNet M).det = 0 :=
    ((eval t).map_det (linearMatrixNet M)).trans hd
  obtain ⟨i, hi⟩ := hJac t ht he
  exact hi (eval_pderiv_det_eq_zero_of_adjugate_eq_zero (linearMatrixNet M) t ha i)

/-- Extending the coefficients of each actual matrix commutes with forming
the actual polynomial matrix of the net. -/
theorem linearMatrixNet_map_coefficients
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (f : K →+* E) :
    linearMatrixNet (fun i => (M i).map f) =
      (linearMatrixNet M).map (MvPolynomial.map f) := by
  ext i j
  simp [linearMatrixNet, Matrix.map_apply]

theorem linearMatrixNet_det_map_coefficients
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (f : K →+* E) :
    (linearMatrixNet (fun i => (M i).map f)).det =
      MvPolynomial.map f (linearMatrixNet M).det := by
  rw [linearMatrixNet_map_coefficients]
  exact ((MvPolynomial.map f).map_det (linearMatrixNet M)).symm

/-- The original determinant's geometric certificate supplies the actual
vector Jacobian hypothesis after any extension of coefficients. -/
theorem linearMatrixNet_jacobian_over_field
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K)
    (hCert : ProjectiveJacobianCertificate (linearMatrixNet M).det) (f : K →+* E) :
    ∀ t : Fin 3 → E, t ≠ 0 →
      eval t (linearMatrixNet (fun i => (M i).map f)).det = 0 →
      ∃ i, eval t (pderiv i (linearMatrixNet (fun i => (M i).map f)).det) ≠ 0 := by
  have hc : ProjectiveJacobianCertificate
      (linearMatrixNet (fun i => (M i).map f)).det := by
    rw [linearMatrixNet_det_map_coefficients]
    exact hCert.map f
  exact hc.rational_jacobian

/-- The actual matrix at a nonzero extension-field parameter has nonzero
adjugate, with no assumption on the determinant of that member. -/
theorem linearMatrixNet_adjugate_ne_zero_over_field
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K)
    (hCert : ProjectiveJacobianCertificate (linearMatrixNet M).det)
    (f : K →+* E) (t : Fin 3 → E) (ht : t ≠ 0) :
    ((linearMatrixNet (fun i => (M i).map f)).map (eval t)).adjugate ≠ 0 :=
  linearMatrixNet_adjugate_ne_zero_of_jacobian _
    (linearMatrixNet_jacobian_over_field M hCert f) t ht

/-- In particular no geometric member of the normalized net can collapse
to a product of a linear form and another polynomial. -/
theorem linearMatrixNet_no_linear_factor_over_field
    (h2 : (2 : E) ≠ 0) (M : Fin 3 → Matrix (Fin 5) (Fin 5) K)
    (hM : ∀ i, (M i).IsSymm)
    (hCert : ProjectiveJacobianCertificate (linearMatrixNet M).det)
    (f : K →+* E) (t : Fin 3 → E) (ht : t ≠ 0)
    (a : Fin 5 → E) (g : MvPolynomial (Fin 5) E) :
    matrixQuadraticPolynomial ((linearMatrixNet (fun i => (M i).map f)).map (eval t)) ≠
      linearPolynomial a * g := by
  apply linearMatrixNet_no_linear_factor_of_jacobian h2 _
    (fun i => ?_) (linearMatrixNet_jacobian_over_field M hCert f) t ht a g
  apply Matrix.IsSymm.ext
  intro r c
  simp only [Matrix.map_apply]
  rw [(hM i).apply]

/-- A genuine affine polar coefficient is nonzero. This generic-field lemma
keeps the polar-independence argument separate from the large concrete
intermediate-field expression used by the incidence function field. -/
theorem linearMatrixNet_exists_affine_polar_coefficient_ne_zero
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (hM : ∀ i, (M i).IsSymm)
    (hbase : ∀ i, M i 0 0 = 0)
    (hJac : ∀ t : Fin 3 → K, t ≠ 0 → eval t (linearMatrixNet M).det = 0 →
      ∃ i, eval t (pderiv i (linearMatrixNet M).det) ≠ 0)
    (t : Fin 3 → K) (ht : t ≠ 0) (f : K →+* E)
    (p : Fin 4) (x : Fin 3 → E)
    (hlinear : (∑ j : Fin 3,
      f (∑ i, t i * M i (p.succAbove j).succ 0) * x j) +
      f (∑ i, t i * M i p.succ 0) = 0) :
    ∃ q : Fin 3, (∑ i, t i * M i (p.succAbove q).succ 0) ≠ 0 := by
  have hind := linearMatrixNet_polar_tails_linearIndependent M hM hbase hJac
  by_contra hh
  push_neg at hh
  have hc : (∑ i, t i * M i p.succ 0) = 0 := by
    simp only [hh, map_zero, zero_mul, Finset.sum_const_zero, zero_add] at hlinear
    exact f.injective (hlinear.trans (map_zero f).symm)
  have htail (j : Fin 4) : (∑ i, t i * M i j.succ 0) = 0 := by
    obtain rfl | ⟨i, rfl⟩ := Fin.eq_self_or_eq_succAbove p j
    · exact hc
    · exact hh i
  have hsum : (∑ i, t i • (fun j : Fin 4 => M i j.succ 0)) = 0 := by
    funext j
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using htail j
  exact ht (funext (Fintype.linearIndependent_iff.mp hind t hsum))

end EvenQuinticConic.Incidence
