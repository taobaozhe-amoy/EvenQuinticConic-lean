import EvenQuinticConic.QuadraticFractionBridge
import EvenQuinticConic.SheafGluing
import EvenQuinticConic.PlaneLinearChartRepresentatives

/-!
# Regular quadratic coefficients on arbitrary linear charts

Actual regular coordinate ratios on a linear chart multiply the chart
coefficients of the actual square sheaf to produce compatible regular
functions. Their gluing is performed by the actual structure sheaf.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace MvPolynomial
open scoped EvenQuinticConic.SchemeScalars

namespace EvenQuinticConic

variable {K : Type} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

private theorem linearChart_genericPoint_mem (F : PlanePolynomial K)
    [IsIntegral (PlaneCurveScheme F)] (U : (PlaneCurveScheme F).Opens) [Nonempty U] :
    genericPoint (PlaneCurveScheme F) ∈ U :=
  ((genericPoint_spec (PlaneCurveScheme F)).mem_open_set_iff U.isOpen).mpr (by
    simpa using (inferInstance : Nonempty U))

/-- Regular coordinate ratios on an open set glue the actual local
coefficients of a square section to one regular function. The ratios are
actual regular sections, and their stipulated generic identities are enough
because restriction to the function field is injective on nonempty opens. -/
theorem planeCurveQuadraticSection_regular_of_ratios (F : PlanePolynomial K)
    [IsIntegral (PlaneCurveScheme F)] [∀ i, Nonempty (planeCurveCoordinateOpen F i)]
    (j : Fin 3) (U : (PlaneCurveScheme F).Opens) [Nonempty U]
    (t : (PlaneCurveScheme F).functionField) (ht : t ≠ 0)
    (q : Fin 3 → Γ(PlaneCurveScheme F, U))
    (hq : ∀ i, (PlaneCurveScheme F).germToFunctionField U (q i) * t =
      planeCurveGenericCoordinates F j i)
    (s : (PlaneCurveQuadraticSheaf F).val.obj (op ⊤)) :
    ∃ r : Γ(PlaneCurveScheme F, U),
      (PlaneCurveScheme F).germToFunctionField U r * t ^ 2 =
        schemeGenericLinearMap (K := K) (PlaneCurveQuadraticSheaf F)
          (planeCurveCoordinateOpen F j) (planeCurveQuadraticFrame F j) s := by
  let W : Fin 3 → (PlaneCurveScheme F).Opens :=
    fun i ↦ U ⊓ planeCurveCoordinateOpen F i
  letI : ∀ i, Nonempty (W i) := fun i ↦ ⟨⟨genericPoint (PlaneCurveScheme F),
    linearChart_genericPoint_mem F U, linearChart_genericPoint_mem F _⟩⟩
  let localSections : ∀ i, Γ(PlaneCurveScheme F, W i) := fun i ↦
    (PlaneCurveScheme F).presheaf.map (homOfLE inf_le_right).op
        (planeCurveQuadraticCoefficient F s i) *
      ((PlaneCurveScheme F).presheaf.map (homOfLE inf_le_left).op (q i)) ^ 2
  let c := schemeGenericLinearMap (K := K) (PlaneCurveQuadraticSheaf F)
    (planeCurveCoordinateOpen F j) (planeCurveQuadraticFrame F j) s
  have hlocal : ∀ i, (PlaneCurveScheme F).germToFunctionField (W i) (localSections i) =
      c / t ^ 2 := by
    intro i
    apply (eq_div_iff (pow_ne_zero 2 ht)).mpr
    change (PlaneCurveScheme F).germToFunctionField (W i)
      ((PlaneCurveScheme F).presheaf.map (homOfLE inf_le_right).op
          (planeCurveQuadraticCoefficient F s i) *
        ((PlaneCurveScheme F).presheaf.map (homOfLE inf_le_left).op (q i)) ^ 2) * t ^ 2 = c
    rw [map_mul, map_pow, generic_germ_restrict, generic_germ_restrict,
      planeCurveQuadraticCoefficient_generic]
    calc
      _ = schemeGenericLinearMap (K := K) (PlaneCurveQuadraticSheaf F)
          (planeCurveCoordinateOpen F i) (planeCurveQuadraticFrame F i) s *
            ((PlaneCurveScheme F).germToFunctionField U (q i) * t) ^ 2 := by ring
      _ = _ := by rw [hq i, mul_comm, ← planeCurveQuadratic_generic_transition F i j s]
  have hcover : U ≤ iSup W := by
    simp only [W, ← inf_iSup_eq, planeCurveCoordinateOpen_cover, inf_top_eq, le_refl]
  obtain ⟨r, hr, _⟩ := existsUnique_section_with_generic_value
    (PlaneCurveScheme F) W U (fun _ ↦ homOfLE inf_le_left) hcover (c / t ^ 2)
    localSections hlocal
  exact ⟨r, (eq_div_iff (pow_ne_zero 2 ht)).mp hr.1⟩

/-- A nonzero linear form cannot vanish in the actual curve function field
when the defining equation has larger degree. -/
theorem planeCurve_linear_aeval_ne_zero
    (F : PlanePolynomial K) (e : ℕ) (hF : F.IsHomogeneous e)
    (hFdeg : 1 < F.totalDegree) (hprime : (Ideal.span {F}).IsPrime)
    (j : Fin 3) (L : PlanePolynomial K) (hL : L.IsHomogeneous 1) (hL0 : L ≠ 0) :
    letI := planeCurveScheme_isIntegral F e hF hFdeg hprime
    letI := planeCurveCoordinateOpen_nonempty F e hF hFdeg hprime j
    aeval (planeCurveGenericCoordinates F j) L ≠ 0 := by
  letI := planeCurveScheme_isIntegral F e hF hFdeg hprime
  letI := planeCurveCoordinateOpen_nonempty F e hF hFdeg hprime j
  intro hz
  have hmem := (planeCurve_homogeneous_aeval_eq_zero_iff F e hF hFdeg hprime j 1 L hL).mp hz
  have hF0 : F ≠ 0 := by
    intro hh
    simp [hh] at hFdeg
  exact hL0 (eq_zero_of_dvd_of_totalDegree_lt F L hF0
    (Ideal.mem_span_singleton.mp hmem) (hL.totalDegree_le.trans_lt hFdeg))

/-- Every nonzero linear form defines a nonempty open of the actual
integral plane curve of degree greater than one. -/
theorem planeCurveLinearOpen_nonempty
    (F : PlanePolynomial K) (e : ℕ) (hF : F.IsHomogeneous e)
    (hFdeg : 1 < F.totalDegree) (hprime : (Ideal.span {F}).IsPrime)
    (L : PlanePolynomial K) (hL : L.IsHomogeneous 1) (hL0 : L ≠ 0) :
    Nonempty (planeCurveLinearOpen F L) := by
  letI := planeCurveScheme_isIntegral F e hF hFdeg hprime
  refine ⟨⟨genericPoint (PlaneCurveScheme F), ?_⟩⟩
  change (planeCurveInclusion F).base (genericPoint (PlaneCurveScheme F)) ∈
    Proj.basicOpen (homogeneousSubmodule (Fin 3) K) L
  rw [planeCurveInclusion_genericPoint F e hF hFdeg hprime]
  change L ∉ Ideal.span {F}
  intro hmem
  have hF0 : F ≠ 0 := by
    intro hh
    simp [hh] at hFdeg
  exact hL0 (eq_zero_of_dvd_of_totalDegree_lt F L hF0
    (Ideal.mem_span_singleton.mp hmem) (hL.totalDegree_le.trans_lt hFdeg))

/-- An actual square section divided by the square of any nonzero linear
form is an actual regular function on the corresponding linear chart.
All local ratios and their compatibility are supplied by the constructed
projective scheme and structure sheaf. -/
theorem planeCurveQuadraticSection_linear_regular
    (F : PlanePolynomial K) (e : ℕ) (hF : F.IsHomogeneous e)
    (hFdeg : 1 < F.totalDegree) (hprime : (Ideal.span {F}).IsPrime)
    (j : Fin 3) (L : PlanePolynomial K) (hL : L.IsHomogeneous 1) (hL0 : L ≠ 0)
    (s : (PlaneCurveQuadraticSheaf F).val.obj (op ⊤)) :
    letI := planeCurveScheme_isIntegral F e hF hFdeg hprime
    letI := planeCurveCoordinateOpen_nonempty F e hF hFdeg hprime j
    letI := planeCurveLinearOpen_nonempty F e hF hFdeg hprime L hL hL0
    ∃ r : Γ(PlaneCurveScheme F, planeCurveLinearOpen F L),
      (PlaneCurveScheme F).germToFunctionField (planeCurveLinearOpen F L) r *
          (aeval (planeCurveGenericCoordinates F j) L) ^ 2 =
        schemeGenericLinearMap (K := K) (PlaneCurveQuadraticSheaf F)
          (planeCurveCoordinateOpen F j) (planeCurveQuadraticFrame F j) s := by
  letI := planeCurveScheme_isIntegral F e hF hFdeg hprime
  letI : ∀ i, Nonempty (planeCurveCoordinateOpen F i) :=
    planeCurveCoordinateOpen_nonempty F e hF hFdeg hprime
  letI := planeCurveLinearOpen_nonempty F e hF hFdeg hprime L hL hL0
  exact planeCurveQuadraticSection_regular_of_ratios F j (planeCurveLinearOpen F L)
    (aeval (planeCurveGenericCoordinates F j) L)
    (planeCurve_linear_aeval_ne_zero F e hF hFdeg hprime j L hL hL0)
    (planeCurveLinearRatio F L hL) (planeCurveLinearRatio_generic F L hL j) s

/-- Every actual global square section has a homogeneous numerator after
clearing a power of any prescribed nonzero linear form. This is obtained
from actual regularity on that linear chart and actual homogeneous chart
representatives, not from an assumed extension or lifting property. -/
theorem planeCurveQuadraticSection_linear_weighted_representative
    (F : PlanePolynomial K) (e : ℕ) (hF : F.IsHomogeneous e)
    (hFdeg : 1 < F.totalDegree) (hprime : (Ideal.span {F}).IsPrime)
    (j : Fin 3) (L : PlanePolynomial K) (hL : L.IsHomogeneous 1) (hL0 : L ≠ 0)
    (s : (PlaneCurveQuadraticSheaf F).val.obj (op ⊤)) :
    letI := planeCurveScheme_isIntegral F e hF hFdeg hprime
    letI := planeCurveCoordinateOpen_nonempty F e hF hFdeg hprime j
    ∃ (n : ℕ) (B : PlanePolynomial K), B.IsHomogeneous (n + 2) ∧
      aeval (planeCurveGenericCoordinates F j) B =
        schemeGenericLinearMap (K := K) (PlaneCurveQuadraticSheaf F)
          (planeCurveCoordinateOpen F j) (planeCurveQuadraticFrame F j) s *
          (aeval (planeCurveGenericCoordinates F j) L) ^ n := by
  letI := planeCurveScheme_isIntegral F e hF hFdeg hprime
  letI := planeCurveCoordinateOpen_nonempty F e hF hFdeg hprime j
  letI := planeCurveLinearOpen_nonempty F e hF hFdeg hprime L hL hL0
  obtain ⟨r, hr⟩ := planeCurveQuadraticSection_linear_regular
    F e hF hFdeg hprime j L hL hL0 s
  obtain ⟨n, P, hP, hrepr⟩ := planeCurveLinearOpen_generic_representative F L hL j r
  refine ⟨n, P * L ^ 2, hP.mul (by simpa using hL.pow 2), ?_⟩
  rw [map_mul, map_pow, ← hrepr, ← hr]
  ring

end EvenQuinticConic
