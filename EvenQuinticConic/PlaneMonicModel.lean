import EvenQuinticConic.HomogeneousLocalizationSections
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Data.Fin.Rev

/-!
# A monic presentation of the actual affine cone

The coordinate permutation and polynomial equivalences in this file are
explicit. The third plane coordinate is the outer polynomial variable;
the other two are the independent base coordinates. The monicity assumption
is an algebraic assumption on that actual defining equation, not a statement
about projective sections.
-/

noncomputable section

set_option maxSynthPendingDepth 3

namespace EvenQuinticConic

variable (K : Type*) [Field K]

/-- One variable expressed as an ordinary polynomial ring. -/
def oneCoordinatePolynomialEquiv :
    MvPolynomial (Fin 1) K ≃ₐ[K] Polynomial K :=
  (MvPolynomial.finSuccEquiv K 0).trans
    (Polynomial.mapAlgEquiv (MvPolynomial.isEmptyAlgEquiv K (Fin 0)))

/-- Two variables expressed as iterated ordinary polynomial rings. -/
def twoCoordinatePolynomialEquiv :
    MvPolynomial (Fin 2) K ≃ₐ[K] TwoCoordinatePolynomial K :=
  (MvPolynomial.finSuccEquiv K 1).trans
    (Polynomial.mapAlgEquiv (oneCoordinatePolynomialEquiv K))

/-- Three plane coordinates expressed as iterated polynomials, with `X₂`
as the outer variable and `X₀` as the innermost variable. -/
def planeIteratedPolynomialEquiv :
    PlanePolynomial K ≃ₐ[K] Polynomial (TwoCoordinatePolynomial K) :=
  (MvPolynomial.renameEquiv K Fin.revPerm).trans
    ((MvPolynomial.finSuccEquiv K 2).trans
      (Polynomial.mapAlgEquiv (twoCoordinatePolynomialEquiv K)))

@[simp] theorem oneCoordinatePolynomialEquiv_X :
    oneCoordinatePolynomialEquiv K (MvPolynomial.X 0) = Polynomial.X := by
  simp [oneCoordinatePolynomialEquiv, MvPolynomial.finSuccEquiv_X_zero]

@[simp] theorem planeIteratedPolynomialEquiv_X_zero :
    planeIteratedPolynomialEquiv K (MvPolynomial.X 0) =
      Polynomial.C (Polynomial.C (Polynomial.X : Polynomial K)) := by
  simp only [planeIteratedPolynomialEquiv, AlgEquiv.trans_apply,
    MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X]
  change Polynomial.map (twoCoordinatePolynomialEquiv K).toRingHom ((MvPolynomial.finSuccEquiv K 2)
    (MvPolynomial.X (Fin.succ (Fin.succ 0)))) = _
  rw [MvPolynomial.finSuccEquiv_X_succ, Polynomial.map_C]
  change Polynomial.C (Polynomial.map (oneCoordinatePolynomialEquiv K).toRingHom ((MvPolynomial.finSuccEquiv K 1)
    (MvPolynomial.X (Fin.succ 0)))) = _
  rw [MvPolynomial.finSuccEquiv_X_succ, Polynomial.map_C]
  change Polynomial.C (Polynomial.C (oneCoordinatePolynomialEquiv K
    (MvPolynomial.X 0))) = _
  rw [oneCoordinatePolynomialEquiv_X]

@[simp] theorem planeIteratedPolynomialEquiv_X_one :
    planeIteratedPolynomialEquiv K (MvPolynomial.X 1) =
      Polynomial.C (Polynomial.X : TwoCoordinatePolynomial K) := by
  simp only [planeIteratedPolynomialEquiv, AlgEquiv.trans_apply,
    MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X]
  change Polynomial.map (twoCoordinatePolynomialEquiv K).toRingHom ((MvPolynomial.finSuccEquiv K 2)
    (MvPolynomial.X (Fin.succ 0))) = _
  rw [MvPolynomial.finSuccEquiv_X_succ, Polynomial.map_C]
  change Polynomial.C (Polynomial.map (oneCoordinatePolynomialEquiv K).toRingHom ((MvPolynomial.finSuccEquiv K 1)
    (MvPolynomial.X 0))) = _
  rw [MvPolynomial.finSuccEquiv_X_zero, Polynomial.map_X]

@[simp] theorem planeIteratedPolynomialEquiv_X_two :
    planeIteratedPolynomialEquiv K (MvPolynomial.X 2) = Polynomial.X := by
  simp only [planeIteratedPolynomialEquiv, AlgEquiv.trans_apply,
    MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X]
  change Polynomial.map (twoCoordinatePolynomialEquiv K).toRingHom ((MvPolynomial.finSuccEquiv K 2) (MvPolynomial.X 0)) = _
  rw [MvPolynomial.finSuccEquiv_X_zero, Polynomial.map_X]

variable {K}

/-- The given plane equation, now viewed as a polynomial in `X₂` over
`K[X₀][X₁]`. -/
def planeMonicPolynomial (F : PlanePolynomial K) :
    Polynomial (TwoCoordinatePolynomial K) := planeIteratedPolynomialEquiv K F

/-- The actual cone quotient is the root-adjoining quotient for exactly
the transformed defining polynomial. This equivalence needs no monicity. -/
def planeConeMonicEquiv (F : PlanePolynomial K) :
    PlaneConeQuotient F ≃ₐ[K] AdjoinRoot (planeMonicPolynomial F) := by
  change PlaneConeQuotient F ≃ₐ[K]
    Polynomial (TwoCoordinatePolynomial K) ⧸ Ideal.span {planeMonicPolynomial F}
  exact Ideal.quotientEquivAlg (Ideal.span {F}) (Ideal.span {planeMonicPolynomial F})
    (planeIteratedPolynomialEquiv K) (by simp [Ideal.map_span, planeMonicPolynomial])

@[simp] theorem planeConeMonicEquiv_mk (F P : PlanePolynomial K) :
    planeConeMonicEquiv F (Ideal.Quotient.mk (Ideal.span {F}) P) =
      AdjoinRoot.mk (planeMonicPolynomial F) (planeIteratedPolynomialEquiv K P) := rfl

@[simp] theorem planeConeMonicEquiv_coordinate_zero (F : PlanePolynomial K) :
    planeConeMonicEquiv F (Ideal.Quotient.mk (Ideal.span {F}) (MvPolynomial.X 0)) =
      algebraMap (TwoCoordinatePolynomial K) (AdjoinRoot (planeMonicPolynomial F))
        (Polynomial.C (Polynomial.X : Polynomial K)) := by
  rw [planeConeMonicEquiv_mk, planeIteratedPolynomialEquiv_X_zero]
  rfl

@[simp] theorem planeConeMonicEquiv_coordinate_one (F : PlanePolynomial K) :
    planeConeMonicEquiv F (Ideal.Quotient.mk (Ideal.span {F}) (MvPolynomial.X 1)) =
      algebraMap (TwoCoordinatePolynomial K) (AdjoinRoot (planeMonicPolynomial F))
        Polynomial.X := by
  rw [planeConeMonicEquiv_mk, planeIteratedPolynomialEquiv_X_one]
  rfl

@[simp] theorem planeConeMonicEquiv_coordinate_two (F : PlanePolynomial K) :
    planeConeMonicEquiv F (Ideal.Quotient.mk (Ideal.span {F}) (MvPolynomial.X 2)) =
      AdjoinRoot.root (planeMonicPolynomial F) := by
  rw [planeConeMonicEquiv_mk, planeIteratedPolynomialEquiv_X_two, AdjoinRoot.mk_X]

/-- The coefficient at a total-degree bound contains no remaining variables. -/
theorem finSuccEquiv_top_coefficient {r : ℕ}
    (F : MvPolynomial (Fin (r + 1)) K) (d : ℕ) (hF : F.totalDegree ≤ d) :
    ((MvPolynomial.finSuccEquiv K r) F).coeff d =
      MvPolynomial.C (F.coeff (Finsupp.single 0 d)) := by
  let A := ((MvPolynomial.finSuccEquiv K r) F).coeff d
  have hA : A.totalDegree = 0 := by
    by_cases ha : A = 0
    · simp [ha]
    · have hb := MvPolynomial.totalDegree_coeff_finSuccEquiv_add_le F d ha
      change A.totalDegree + d ≤ F.totalDegree at hb
      omega
  have hcons : (0 : Fin r →₀ ℕ).cons d = Finsupp.single 0 d := by
    ext i
    refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp
  rw [MvPolynomial.totalDegree_eq_zero_iff_eq_C] at hA
  change A = _
  rw [hA]
  congr 1
  change MvPolynomial.coeff 0 (((MvPolynomial.finSuccEquiv K r) F).coeff d) = _
  rw [MvPolynomial.finSuccEquiv_coeff_coeff, hcons]

/-- Outer degree is bounded by the original total degree. -/
theorem planeMonicPolynomial_natDegree_le (F : PlanePolynomial K) :
    (planeMonicPolynomial F).natDegree ≤ F.totalDegree := by
  change (Polynomial.map (twoCoordinatePolynomialEquiv K).toRingHom
    ((MvPolynomial.finSuccEquiv K 2)
      ((MvPolynomial.renameEquiv K Fin.revPerm) F))).natDegree ≤ _
  calc
    _ ≤ ((MvPolynomial.finSuccEquiv K 2)
      ((MvPolynomial.renameEquiv K Fin.revPerm) F)).natDegree :=
        Polynomial.natDegree_map_le
    _ = ((MvPolynomial.renameEquiv K Fin.revPerm) F).degreeOf 0 :=
      MvPolynomial.natDegree_finSuccEquiv _
    _ ≤ ((MvPolynomial.renameEquiv K Fin.revPerm) F).totalDegree :=
      MvPolynomial.degreeOf_le_totalDegree _ _
    _ = F.totalDegree := MvPolynomial.totalDegree_renameEquiv _ _

/-- The coefficient of the highest possible outer power is the actual
coefficient of `X₂ ^ d` in the original equation. -/
theorem planeMonicPolynomial_coefficient_at_degree_bound (F : PlanePolynomial K)
    (d : ℕ) (hF : F.totalDegree ≤ d) :
    (planeMonicPolynomial F).coeff d =
      algebraMap K (TwoCoordinatePolynomial K) (F.coeff (Finsupp.single 2 d)) := by
  change (Polynomial.map (twoCoordinatePolynomialEquiv K).toRingHom
    ((MvPolynomial.finSuccEquiv K 2)
      ((MvPolynomial.renameEquiv K Fin.revPerm) F))).coeff d = _
  rw [Polynomial.coeff_map, finSuccEquiv_top_coefficient _ d
    (by simpa only [MvPolynomial.totalDegree_renameEquiv] using hF)]
  have hc : MvPolynomial.coeff (Finsupp.single 0 d)
      ((MvPolynomial.renameEquiv K Fin.revPerm) F) =
      F.coeff (Finsupp.single 2 d) := by
    simpa using MvPolynomial.coeff_rename_mapDomain
      (Fin.revPerm : Fin 3 ≃ Fin 3) Fin.revPerm.injective F (Finsupp.single 2 d)
  rw [hc]
  exact (twoCoordinatePolynomialEquiv K).commutes _

/-- A coefficient normalization in genuine plane coordinates supplies the
monicity assumption required for the finite-free denominator calculation. -/
theorem planeMonicPolynomial_monic_of_coefficient_one (F : PlanePolynomial K)
    (d : ℕ) (hF : F.totalDegree ≤ d) (hc : F.coeff (Finsupp.single 2 d) = 1) :
    (planeMonicPolynomial F).Monic := by
  apply Polynomial.monic_of_natDegree_le_of_coeff_eq_one d
    ((planeMonicPolynomial_natDegree_le F).trans hF)
  rw [planeMonicPolynomial_coefficient_at_degree_bound F d hF, hc, map_one]

/-- Clear powers of the two actual cone coordinates using the monic equation
in the third coordinate. No domain, degree, or factoriality hypothesis on
the cone quotient is needed for this finite-free-module calculation. -/
theorem planeCone_monic_clear_denominators (F : PlanePolynomial K)
    (hF : (planeMonicPolynomial F).Monic) (m n : ℕ)
    (a b : PlaneConeQuotient F)
    (h : (Ideal.Quotient.mk (Ideal.span {F}) (MvPolynomial.X 1)) ^ n * a =
      (Ideal.Quotient.mk (Ideal.span {F}) (MvPolynomial.X 0)) ^ m * b) :
    ∃ c : PlaneConeQuotient F,
      a = (Ideal.Quotient.mk (Ideal.span {F}) (MvPolynomial.X 0)) ^ m * c ∧
      b = (Ideal.Quotient.mk (Ideal.span {F}) (MvPolynomial.X 1)) ^ n * c := by
  let e := planeConeMonicEquiv F
  have he : (Polynomial.X : TwoCoordinatePolynomial K) ^ n • e a =
      (Polynomial.C (Polynomial.X : Polynomial K)) ^ m • e b := by
    have heq := congrArg e h
    simpa only [map_mul, map_pow, planeConeMonicEquiv_coordinate_zero,
      planeConeMonicEquiv_coordinate_one, Algebra.smul_def, e] using heq
  obtain ⟨c, ha, hb⟩ := monic_hypersurface_clear_denominators
    (planeMonicPolynomial F) hF
    (Polynomial.C (Polynomial.X : Polynomial K)) Polynomial.X (by simp)
    (two_polynomial_coordinates_relPrime K) m n (e a) (e b) he
  refine ⟨e.symm c, e.injective ?_, e.injective ?_⟩
  · simpa only [map_mul, map_pow, AlgEquiv.apply_symm_apply,
      planeConeMonicEquiv_coordinate_zero, Algebra.smul_def, e] using ha
  · simpa only [map_mul, map_pow, AlgEquiv.apply_symm_apply,
      planeConeMonicEquiv_coordinate_one, Algebra.smul_def, e] using hb

end EvenQuinticConic
