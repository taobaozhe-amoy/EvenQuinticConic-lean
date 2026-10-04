import EvenQuinticConic.PlaneThetaIneffectivity
import EvenQuinticConic.HomogeneousLocalizationSections
import EvenQuinticConic.QuadraticFractionBridge
import EvenQuinticConic.PlaneMonicModel
import EvenQuinticConic.LinearDenominatorClearing
import EvenQuinticConic.LinearChartQuadraticSections
import EvenQuinticConic.PlaneCoordinateClearing

/-!
# Polynomial lifts of actual quadratic-sheaf sections

The constructed multiplication pairing has coefficient one in the actual
coordinate frames. Consequently polynomial restriction into the actual
square sheaf has exactly the expected generic coefficient. Equality of
these coefficients determines actual global sections.

Actual regular functions on arbitrary linear charts give homogeneous
numerators. Explicit good linear coordinates permit clearing their two
denominators in the actual cone quotient. Taking the homogeneous component
of degree two then proves surjectivity over every infinite base field.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace MvPolynomial
open scoped EvenQuinticConic.SchemeScalars

namespace EvenQuinticConic

variable {K : Type} [Field K]

/-- The actual square pairing has coefficient one in its constructed frames. -/
theorem planeCurveSquarePairing_coefficient (F : PlanePolynomial K) (i : Fin 3) :
    modulePairingCoefficient (planeCurveSquarePairing F) (planeCurveCoordinateOpen F i)
      (planeCurveHyperplaneFrame F i) (planeCurveQuadraticFrame F i) = 1 :=
  UnitTransition.multiplicationPairing_square_coefficient
    (planeCurveHyperplaneTransition F) i

/-- Polynomial restriction into the actual square sheaf has its genuine
homogeneous evaluation as generic coefficient, without an unknown weight. -/
theorem planeCurveQuadraticPolynomialSection_generic (F : PlanePolynomial K)
    [IsIntegral (PlaneCurveScheme F)] (i : Fin 3)
    [Nonempty (planeCurveCoordinateOpen F i)]
    (P : PlanePolynomial K) (hP : P.IsHomogeneous 2) :
    schemeGenericLinearMap (K := K) (PlaneCurveQuadraticSheaf F)
      (planeCurveCoordinateOpen F i) (planeCurveQuadraticFrame F i)
      (quadraticPolynomialSection (planeCurveSquarePairing F)
        (planeCurveCoordinateSection F) P) =
      aeval (planeCurveGenericCoordinates F i) P := by
  rw [genericCoefficient_quadraticPolynomialSection
    (planeCurveSquarePairing F) (planeCurveCoordinateOpen F i)
    (planeCurveHyperplaneFrame F i) (planeCurveQuadraticFrame F i)
    (planeCurveCoordinateSection F) P hP]
  simp only [quadraticGenericRestriction, planeCurveSquarePairing_coefficient,
    map_one, one_mul, planeCurveCoordinateSection_generic]

/-- Actual global sections of the constructed square sheaf are determined
by their generic coordinate in any one nonempty standard chart. -/
theorem planeCurveQuadratic_genericMap_injective (F : PlanePolynomial K)
    [IsIntegral (PlaneCurveScheme F)]
    [∀ i, Nonempty (planeCurveCoordinateOpen F i)] (j : Fin 3) :
    Function.Injective (schemeGenericLinearMap (K := K) (PlaneCurveQuadraticSheaf F)
      (planeCurveCoordinateOpen F j) (planeCurveQuadraticFrame F j)) :=
  schemeGenericLinearMap_injective (PlaneCurveQuadraticSheaf F)
    (planeCurveCoordinateOpen F) (planeCurveCoordinateOpen_cover F)
    (planeCurveQuadraticFrame F) (planeCurveCoordinateOpen F j)
    (planeCurveQuadraticFrame F j)

/-- On an actual integral plane curve whose equation is monic in the third
coordinate, every actual quadratic-sheaf section is a homogeneous quadratic
polynomial section. Surjectivity is a conclusion, not a lifting hypothesis. -/
theorem planeCurve_quadraticSectionMap_surjective_of_monic
    (F : PlanePolynomial K) (e : ℕ) (hF : F.IsHomogeneous e)
    (hFdeg : 1 < F.totalDegree) (hprime : (Ideal.span {F}).IsPrime)
    (hmonic : (planeMonicPolynomial F).Monic) :
    Function.Surjective (quadraticSectionMap (K := K)
      (planeCurveSquarePairing F) (planeCurveCoordinateSection F)) := by
  letI := planeCurveScheme_isIntegral F e hF hFdeg hprime
  letI : (Ideal.span {F}).IsPrime := hprime
  letI : ∀ i, Nonempty (planeCurveCoordinateOpen F i) :=
    fun i => planeCurveCoordinateOpen_nonempty F e hF hFdeg hprime i
  intro s
  obtain ⟨n, B, hB, hval, hcross⟩ :=
    planeCurveQuadraticSection_cone_representatives F e hF hFdeg hprime 0 s
  obtain ⟨c, hc, _⟩ := planeCone_monic_clear_denominators F hmonic (n 0) (n 1)
    (Ideal.Quotient.mk (Ideal.span {F}) (B 0))
    (Ideal.Quotient.mk (Ideal.span {F}) (B 1)) (by
      simpa only [mul_comm] using hcross 0 1)
  obtain ⟨P, hP, hPc⟩ := plane_cone_homogeneous_representative F e hF hFdeg
    0 (n 0) 2 (B 0) (hB 0) c hc.symm
  have hmem : P * X 0 ^ n 0 - B 0 ∈ Ideal.span {F} := by
    apply (Ideal.Quotient.eq_zero_iff_mem).mp
    simp only [map_sub, map_mul, map_pow, hPc, hc, mul_comm, sub_self]
  have hhom : (P * X 0 ^ n 0 - B 0).IsHomogeneous (n 0 + 2) := by
    apply IsHomogeneous.sub _ (hB 0)
    convert hP.mul (by simpa using (isHomogeneous_X K (0 : Fin 3)).pow (n 0)) using 1
    omega
  have heq := (planeCurve_homogeneous_aeval_eq_zero_iff F e hF hFdeg hprime
    0 (n 0 + 2) _ hhom).mpr hmem
  simp only [map_sub, map_mul, map_pow, aeval_X, hval, sub_eq_zero] at heq
  have heval := mul_right_cancel₀
    (pow_ne_zero (n 0) (planeCurveGenericCoordinates_ne_zero F 0 0)) heq
  refine ⟨⟨P, hP⟩, ?_⟩
  apply planeCurveQuadratic_genericMap_injective F 0
  change schemeGenericLinearMap (K := K) (PlaneCurveQuadraticSheaf F)
      (planeCurveCoordinateOpen F 0) (planeCurveQuadraticFrame F 0)
      (quadraticPolynomialSection (planeCurveSquarePairing F)
        (planeCurveCoordinateSection F) P) = _
  rw [planeCurveQuadraticPolynomialSection_generic F 0 P hP]
  exact heval

/-- A cleared linear denominator gives a genuine homogeneous quadratic
lift of the actual section. The quotient equality and generic numerator
formula are algebraic data obtained from the actual chart construction. -/
theorem planeCurve_quadratic_lift_of_cleared_linear_numerator
    (F : PlanePolynomial K) (e : ℕ) (hF : F.IsHomogeneous e)
    (hFdeg : 1 < F.totalDegree) (hprime : (Ideal.span {F}).IsPrime)
    (L : PlanePolynomial K) (hL : L.IsHomogeneous 1) (hL0 : L ≠ 0)
    (m : ℕ) (B : PlanePolynomial K) (hB : B.IsHomogeneous (m + 2))
    (c : PlaneConeQuotient F)
    (hc : (Ideal.Quotient.mk (Ideal.span {F}) L) ^ m * c =
      Ideal.Quotient.mk (Ideal.span {F}) B) :
    letI := planeCurveScheme_isIntegral F e hF hFdeg hprime
    letI := planeCurveCoordinateOpen_nonempty F e hF hFdeg hprime 0
    ∀ s : (PlaneCurveQuadraticSheaf F).val.obj (op ⊤),
      aeval (planeCurveGenericCoordinates F 0) B =
        schemeGenericLinearMap (K := K) (PlaneCurveQuadraticSheaf F)
          (planeCurveCoordinateOpen F 0) (planeCurveQuadraticFrame F 0) s *
          (aeval (planeCurveGenericCoordinates F 0) L) ^ m →
      ∃ P : PlanePolynomial K, P.IsHomogeneous 2 ∧
        quadraticPolynomialSection (planeCurveSquarePairing F)
          (planeCurveCoordinateSection F) P = s := by
  letI := planeCurveScheme_isIntegral F e hF hFdeg hprime
  letI : (Ideal.span {F}).IsPrime := hprime
  letI : ∀ i, Nonempty (planeCurveCoordinateOpen F i) :=
    fun i => planeCurveCoordinateOpen_nonempty F e hF hFdeg hprime i
  intro s hval
  obtain ⟨P, hP, hPc⟩ := plane_cone_linear_homogeneous_representative
    F e hF hFdeg L hL hL0 m 2 B hB c hc
  have hmem : P * L ^ m - B ∈ Ideal.span {F} := by
    apply (Ideal.Quotient.eq_zero_iff_mem).mp
    simp only [map_sub, map_mul, map_pow, hPc]
    rw [mul_comm c, hc, sub_self]
  have hhom : (P * L ^ m - B).IsHomogeneous (m + 2) := by
    apply IsHomogeneous.sub _ hB
    convert hP.mul (by simpa using hL.pow m) using 1
    omega
  have heq := (planeCurve_homogeneous_aeval_eq_zero_iff F e hF hFdeg hprime
    0 (m + 2) _ hhom).mpr hmem
  simp only [map_sub, map_mul, map_pow, hval, sub_eq_zero] at heq
  have hnonzero : aeval (planeCurveGenericCoordinates F 0) L ≠ 0 := by
    intro hz
    exact plane_linear_not_mem_principal F L hFdeg hL hL0
      ((planeCurve_homogeneous_aeval_eq_zero_iff F e hF hFdeg hprime 0 1 L hL).mp hz)
  have heval := mul_right_cancel₀ (pow_ne_zero m hnonzero) heq
  refine ⟨P, hP, ?_⟩
  apply planeCurveQuadratic_genericMap_injective F 0
  rw [planeCurveQuadraticPolynomialSection_generic F 0 P hP]
  exact heval

/-- Every actual global section of the constructed quadratic sheaf on an
integral plane curve of degree greater than one over an infinite field
comes from a homogeneous quadratic polynomial.

Good linear denominators are constructed, their chart numerators come from
actual regular sections, and their compatibility is proved using the full
homogeneous kernel. No monicity, coordinate choice, local lifting property,
or global-section surjectivity is assumed. -/
theorem planeCurve_quadraticSectionMap_surjective [Infinite K]
    (F : PlanePolynomial K) (e : ℕ) (hF : F.IsHomogeneous e)
    (hFdeg : 1 < F.totalDegree) (hprime : (Ideal.span {F}).IsPrime) :
    Function.Surjective (quadraticSectionMap (K := K)
      (planeCurveSquarePairing F) (planeCurveCoordinateSection F)) := by
  letI := planeCurveScheme_isIntegral F e hF hFdeg hprime
  letI : ∀ i, Nonempty (planeCurveCoordinateOpen F i) :=
    fun i => planeCurveCoordinateOpen_nonempty F e hF hFdeg hprime i
  have hF0 : F ≠ 0 := by
    intro hz
    simp [hz] at hFdeg
  have he : 0 < e := by
    have := hF.totalDegree_le
    omega
  obtain ⟨L₀, L₁, hL₀, hL₁, hL₀0, hL₁0, hclear⟩ :=
    exists_good_linear_denominators F e hF hF0 he
  intro s
  obtain ⟨m, A, hA, hvalA⟩ := planeCurveQuadraticSection_linear_weighted_representative
    F e hF hFdeg hprime 0 L₀ hL₀ hL₀0 s
  obtain ⟨n, B, hB, hvalB⟩ := planeCurveQuadraticSection_linear_weighted_representative
    F e hF hFdeg hprime 0 L₁ hL₁ hL₁0 s
  have hleft : (A * L₁ ^ n).IsHomogeneous (m + 2 + n) :=
    hA.mul (by simpa using hL₁.pow n)
  have hright : (B * L₀ ^ m).IsHomogeneous (m + 2 + n) := by
    convert hB.mul (by simpa using hL₀.pow m) using 1
    omega
  have hmem : A * L₁ ^ n - B * L₀ ^ m ∈ Ideal.span {F} := by
    apply (planeCurve_homogeneous_aeval_eq_zero_iff F e hF hFdeg hprime
      0 (m + 2 + n) _ (hleft.sub hright)).mp
    simp only [map_sub, map_mul, map_pow, hvalA, hvalB]
    ring
  have hcross :
      (Ideal.Quotient.mk (Ideal.span {F}) L₁) ^ n *
          Ideal.Quotient.mk (Ideal.span {F}) A =
        (Ideal.Quotient.mk (Ideal.span {F}) L₀) ^ m *
          Ideal.Quotient.mk (Ideal.span {F}) B := by
    simpa only [map_mul, map_pow, mul_comm] using (Ideal.Quotient.eq.mpr hmem)
  obtain ⟨c, hc, _⟩ := hclear m n _ _ hcross
  obtain ⟨P, hP, hPs⟩ := planeCurve_quadratic_lift_of_cleared_linear_numerator
    F e hF hFdeg hprime L₀ hL₀ hL₀0 m A hA c hc.symm s hvalA
  exact ⟨⟨P, hP⟩, hPs⟩

end EvenQuinticConic
