import EvenQuinticConic.PlaneMonicModel
import EvenQuinticConic.HomogeneousCoordinateChoice

/-!
# Denominator clearing after an actual change of plane coordinates

The equivalence here identifies the original affine cone with the quotient
of a transformed and nonzero-scalar-normalized equation. Denominator clearing
therefore applies to the two actual pulled-back linear coordinates in the
original cone. A coordinate change is represented by a genuine polynomial
algebra equivalence, not by an assumed equivalence of geometric conclusions.
-/

noncomputable section

namespace EvenQuinticConic

variable {K : Type*} [Field K]

/-- An actual coordinate change and nonzero scalar normalization induce an
actual equivalence of the two cone quotients. -/
def planeConeNormalizedCoordinateEquiv (F : PlanePolynomial K)
    (E : PlanePolynomial K ≃ₐ[K] PlanePolynomial K) (c : K) (hc : c ≠ 0) :
    PlaneConeQuotient F ≃ₐ[K] PlaneConeQuotient (MvPolynomial.C c * E F) :=
  Ideal.quotientEquivAlg (Ideal.span {F}) (Ideal.span {MvPolynomial.C c * E F}) E
    (by rw [Ideal.span_singleton_mul_left_unit
          ((isUnit_iff_ne_zero.mpr hc).map MvPolynomial.C)]
        simp [Ideal.map_span])

@[simp] theorem planeConeNormalizedCoordinateEquiv_mk (F P : PlanePolynomial K)
    (E : PlanePolynomial K ≃ₐ[K] PlanePolynomial K) (c : K) (hc : c ≠ 0) :
    planeConeNormalizedCoordinateEquiv F E c hc (Ideal.Quotient.mk (Ideal.span {F}) P) =
      Ideal.Quotient.mk (Ideal.span {MvPolynomial.C c * E F}) (E P) := rfl

@[simp] theorem planeConeNormalizedCoordinateEquiv_coordinate (F : PlanePolynomial K)
    (E : PlanePolynomial K ≃ₐ[K] PlanePolynomial K) (c : K) (hc : c ≠ 0) (i : Fin 3) :
    planeConeNormalizedCoordinateEquiv F E c hc
      (Ideal.Quotient.mk (Ideal.span {F}) (E.symm (MvPolynomial.X i))) =
      Ideal.Quotient.mk (Ideal.span {MvPolynomial.C c * E F}) (MvPolynomial.X i) := by
  rw [planeConeNormalizedCoordinateEquiv_mk, AlgEquiv.apply_symm_apply]

/-- Monicity after a genuine coordinate change clears powers of the two
pulled-back base coordinates in the original cone ring. -/
theorem planeCone_coordinate_clear_denominators (F : PlanePolynomial K)
    (E : PlanePolynomial K ≃ₐ[K] PlanePolynomial K) (c : K) (hc : c ≠ 0)
    (hF : (planeMonicPolynomial (MvPolynomial.C c * E F)).Monic)
    (m n : ℕ) (a b : PlaneConeQuotient F)
    (h : (Ideal.Quotient.mk (Ideal.span {F}) (E.symm (MvPolynomial.X 1))) ^ n * a =
      (Ideal.Quotient.mk (Ideal.span {F}) (E.symm (MvPolynomial.X 0))) ^ m * b) :
    ∃ z : PlaneConeQuotient F,
      a = (Ideal.Quotient.mk (Ideal.span {F}) (E.symm (MvPolynomial.X 0))) ^ m * z ∧
      b = (Ideal.Quotient.mk (Ideal.span {F}) (E.symm (MvPolynomial.X 1))) ^ n * z := by
  let e := planeConeNormalizedCoordinateEquiv F E c hc
  have he :
      (Ideal.Quotient.mk (Ideal.span {MvPolynomial.C c * E F}) (MvPolynomial.X 1)) ^ n * e a =
      (Ideal.Quotient.mk (Ideal.span {MvPolynomial.C c * E F}) (MvPolynomial.X 0)) ^ m * e b := by
    simpa only [map_mul, map_pow, e, planeConeNormalizedCoordinateEquiv_coordinate] using
      congrArg e h
  obtain ⟨z, ha, hb⟩ := planeCone_monic_clear_denominators
    (MvPolynomial.C c * E F) hF m n (e a) (e b) he
  refine ⟨e.symm z, e.injective ?_, e.injective ?_⟩
  · simpa only [map_mul, map_pow, AlgEquiv.apply_symm_apply, e,
      planeConeNormalizedCoordinateEquiv_coordinate] using ha
  · simpa only [map_mul, map_pow, AlgEquiv.apply_symm_apply, e,
      planeConeNormalizedCoordinateEquiv_coordinate] using hb

/-- Every nonzero positive-degree homogeneous plane equation over an infinite
field admits two actual nonzero linear denominators with the finite-free
clearing property in its original cone quotient. The coordinate choice,
scalar normalization, and quotient equivalence are all constructed. -/
theorem exists_good_linear_denominators [Infinite K]
    (F : PlanePolynomial K) (d : ℕ) (hF : F.IsHomogeneous d)
    (hF0 : F ≠ 0) (hd : 0 < d) :
    ∃ L₀ L₁ : PlanePolynomial K,
      L₀.IsHomogeneous 1 ∧ L₁.IsHomogeneous 1 ∧ L₀ ≠ 0 ∧ L₁ ≠ 0 ∧
      ∀ (m n : ℕ) (a b : PlaneConeQuotient F),
        (Ideal.Quotient.mk (Ideal.span {F}) L₁) ^ n * a =
          (Ideal.Quotient.mk (Ideal.span {F}) L₀) ^ m * b →
        ∃ z : PlaneConeQuotient F,
          a = (Ideal.Quotient.mk (Ideal.span {F}) L₀) ^ m * z ∧
          b = (Ideal.Quotient.mk (Ideal.span {F}) L₁) ^ n * z := by
  obtain ⟨E, c, hc, _hE, hEinv, hhom, hcoeff, _hideal⟩ :=
    homogeneous_exists_normalized_last_coordinate_both hF hF0 hd
  have hmonic : (planeMonicPolynomial (MvPolynomial.C c * E F)).Monic :=
    planeMonicPolynomial_monic_of_coefficient_one _ d hhom.totalDegree_le hcoeff
  refine ⟨E.symm (MvPolynomial.X 0), E.symm (MvPolynomial.X 1),
    hEinv (MvPolynomial.isHomogeneous_X K 0),
    hEinv (MvPolynomial.isHomogeneous_X K 1), ?_, ?_, ?_⟩
  · simpa only [map_zero] using E.symm.injective.ne (MvPolynomial.X_ne_zero (R := K) 0)
  · simpa only [map_zero] using E.symm.injective.ne (MvPolynomial.X_ne_zero (R := K) 1)
  · intro m n a b h
    exact planeCone_coordinate_clear_denominators F E c hc hmonic m n a b h

end EvenQuinticConic
