import EvenQuinticConic.PlaneThetaIneffectivity
import EvenQuinticConic.PlaneChartRepresentatives
import EvenQuinticConic.PlaneHomogeneousKernel

/-!
# The actual square sheaf and weighted homogeneous fractions

The change of generic coordinates below is derived from the constructed
transition cocycle and restriction maps of the actual structure sheaf.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace MvPolynomial
open scoped EvenQuinticConic.SchemeScalars
namespace EvenQuinticConic
variable {K : Type} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

@[simp] theorem planeCurveCoordinateFunction_self (F : PlanePolynomial K) (i : Fin 3) :
    planeCurveCoordinateFunction F i i = 1 := by
  unfold planeCurveCoordinateFunction
  rw [planeCoordinateRatio_self, map_one]

/-- The actual pulled-back transition is the restriction of the actual
coordinate ratio, on every common subopen. -/
theorem planeCurveHyperplaneTransition_val (F : PlanePolynomial K) (i j : Fin 3)
    (W : (PlaneCurveScheme F).Opens)
    (hi : W ≤ planeCurveCoordinateOpen F i) (hj : W ≤ planeCurveCoordinateOpen F j) :
    ((planeCurveHyperplaneTransition F).transition i j W hi hj : Γ(PlaneCurveScheme F, W)) =
      (PlaneCurveScheme F).presheaf.map (homOfLE hi).op
        (planeCurveCoordinateFunction F j i) := by
  have h := planeCurveCoordinateFunction_compatible F j i j W hi hj
  simpa only [planeCurveCoordinateFunction_self, map_one, mul_one] using h.symm

/-- The regular coefficient of an actual global square section in a standard
coordinate frame. -/
def planeCurveQuadraticCoefficient (F : PlanePolynomial K)
    (s : (PlaneCurveQuadraticSheaf F).val.obj (op ⊤)) (i : Fin 3) :
    Γ(PlaneCurveScheme F, planeCurveCoordinateOpen F i) :=
  s.eval i (planeCurveCoordinateOpen F i) le_top le_rfl

/-- The generic value of the regular coefficient is the actual generic
linear map used in the theta theorem. -/
theorem planeCurveQuadraticCoefficient_generic (F : PlanePolynomial K)
    [IsIntegral (PlaneCurveScheme F)] (i : Fin 3)
    [Nonempty (planeCurveCoordinateOpen F i)]
    (s : (PlaneCurveQuadraticSheaf F).val.obj (op ⊤)) :
    (PlaneCurveScheme F).germToFunctionField (planeCurveCoordinateOpen F i)
      (planeCurveQuadraticCoefficient F s i) =
    schemeGenericLinearMap (K := K) (PlaneCurveQuadraticSheaf F)
      (planeCurveCoordinateOpen F i) (planeCurveQuadraticFrame F i) s := rfl

/-- The square transition has weight two, as a theorem about actual regular
functions on any common subopen. -/
theorem planeCurveQuadraticCoefficient_transition (F : PlanePolynomial K)
    (s : (PlaneCurveQuadraticSheaf F).val.obj (op ⊤)) (i j : Fin 3)
    (W : (PlaneCurveScheme F).Opens)
    (hi : W ≤ planeCurveCoordinateOpen F i) (hj : W ≤ planeCurveCoordinateOpen F j) :
    (PlaneCurveScheme F).presheaf.map (homOfLE hi).op
        (planeCurveQuadraticCoefficient F s i) =
      ((PlaneCurveScheme F).presheaf.map (homOfLE hi).op
        (planeCurveCoordinateFunction F j i)) ^ 2 *
      (PlaneCurveScheme F).presheaf.map (homOfLE hj).op
        (planeCurveQuadraticCoefficient F s j) := by
  have h := s.transition i j W le_top hi hj
  change s.eval i W le_top hi =
    (((planeCurveHyperplaneTransition F).transition i j W hi hj : Γ(PlaneCurveScheme F,W)) *
      ((planeCurveHyperplaneTransition F).transition i j W hi hj : Γ(PlaneCurveScheme F,W))) *
      s.eval j W le_top hj at h
  rw [planeCurveHyperplaneTransition_val] at h
  simpa only [planeCurveQuadraticCoefficient, ← _root_.pow_two,
    ← s.naturality i (planeCurveCoordinateOpen F i) W le_top le_rfl hi,
    ← s.naturality j (planeCurveCoordinateOpen F j) W le_top le_rfl hj] using h

private theorem planeCurveGenericPoint_mem (F : PlanePolynomial K)
    [IsIntegral (PlaneCurveScheme F)] (U : (PlaneCurveScheme F).Opens) [Nonempty U] :
    genericPoint (PlaneCurveScheme F) ∈ U :=
  ((genericPoint_spec (PlaneCurveScheme F)).mem_open_set_iff U.isOpen).mpr (by
    obtain ⟨x⟩ := ‹Nonempty U›
    exact ⟨x.val, Set.mem_univ _, x.property⟩)

/-- The generic coefficient in frame `j` is the coefficient in frame `i`
multiplied by `(Xᵢ/Xⱼ)²`. This follows from the actual overlap restriction. -/
theorem planeCurveQuadratic_generic_transition (F : PlanePolynomial K)
    [IsIntegral (PlaneCurveScheme F)] (i j : Fin 3)
    [Nonempty (planeCurveCoordinateOpen F i)] [Nonempty (planeCurveCoordinateOpen F j)]
    (s : (PlaneCurveQuadraticSheaf F).val.obj (op ⊤)) :
    schemeGenericLinearMap (K := K) (PlaneCurveQuadraticSheaf F)
        (planeCurveCoordinateOpen F j) (planeCurveQuadraticFrame F j) s =
      (planeCurveGenericCoordinates F j i) ^ 2 *
      schemeGenericLinearMap (K := K) (PlaneCurveQuadraticSheaf F)
        (planeCurveCoordinateOpen F i) (planeCurveQuadraticFrame F i) s := by
  let W := planeCurveCoordinateOpen F j ⊓ planeCurveCoordinateOpen F i
  letI : Nonempty W := ⟨⟨genericPoint (PlaneCurveScheme F),
    planeCurveGenericPoint_mem F _, planeCurveGenericPoint_mem F _⟩⟩
  have h := congrArg ((PlaneCurveScheme F).germToFunctionField W)
    (planeCurveQuadraticCoefficient_transition F s j i W inf_le_left inf_le_right)
  simpa only [map_mul, map_pow, generic_germ_restrict,
    planeCurveCoordinateFunction_generic, planeCurveQuadraticCoefficient_generic] using h

/-- All normalized projective coordinates in different charts compare by the
actual transition ratio. -/
theorem planeCurveGenericCoordinates_transition (F : PlanePolynomial K)
    [IsIntegral (PlaneCurveScheme F)] (i j k : Fin 3)
    [Nonempty (planeCurveCoordinateOpen F i)] [Nonempty (planeCurveCoordinateOpen F j)] :
    planeCurveGenericCoordinates F j k =
      planeCurveGenericCoordinates F j i * planeCurveGenericCoordinates F i k := by
  let W := planeCurveCoordinateOpen F j ⊓ planeCurveCoordinateOpen F i
  letI : Nonempty W := ⟨⟨genericPoint (PlaneCurveScheme F),
    planeCurveGenericPoint_mem F _, planeCurveGenericPoint_mem F _⟩⟩
  have h := planeCurveCoordinateFunction_compatible F k j i W inf_le_left inf_le_right
  rw [planeCurveHyperplaneTransition_val] at h
  have hh := congrArg ((PlaneCurveScheme F).germToFunctionField W) h
  simpa only [map_mul, generic_germ_restrict, planeCurveCoordinateFunction_generic] using hh

@[simp] theorem planeCurveGenericCoordinates_self (F : PlanePolynomial K)
    [IsIntegral (PlaneCurveScheme F)] (i : Fin 3)
    [Nonempty (planeCurveCoordinateOpen F i)] : planeCurveGenericCoordinates F i i = 1 := by
  rw [← planeCurveCoordinateFunction_generic, planeCurveCoordinateFunction_self, map_one]

/-- A normalized coordinate function cannot vanish generically if its own
standard chart is nonempty. -/
theorem planeCurveGenericCoordinates_ne_zero (F : PlanePolynomial K)
    [IsIntegral (PlaneCurveScheme F)] (i j : Fin 3)
    [Nonempty (planeCurveCoordinateOpen F i)] [Nonempty (planeCurveCoordinateOpen F j)] :
    planeCurveGenericCoordinates F j i ≠ 0 := by
  have h := planeCurveGenericCoordinates_transition F i j j
  rw [planeCurveGenericCoordinates_self] at h
  intro hz
  rw [hz, zero_mul] at h
  exact one_ne_zero h

/-- Homogeneous polynomial expressions in distinct actual chart coordinates
transform with their true homogeneous degree. -/
theorem planeCurve_homogeneous_aeval_transition (F : PlanePolynomial K)
    [IsIntegral (PlaneCurveScheme F)] (i j : Fin 3)
    [Nonempty (planeCurveCoordinateOpen F i)] [Nonempty (planeCurveCoordinateOpen F j)]
    (P : PlanePolynomial K) (n : ℕ) (hP : P.IsHomogeneous n) :
    aeval (planeCurveGenericCoordinates F j) P =
      aeval (planeCurveGenericCoordinates F i) P * (planeCurveGenericCoordinates F j i) ^ n := by
  have hcoords : planeCurveGenericCoordinates F j =
      fun k => planeCurveGenericCoordinates F i k * planeCurveGenericCoordinates F j i := by
    funext k
    rw [planeCurveGenericCoordinates_transition F i j k, mul_comm]
  change eval₂ (algebraMap K (PlaneCurveScheme F).functionField)
    (planeCurveGenericCoordinates F j) P = _
  nth_rw 1 [hcoords]
  exact homogeneous_eval₂_scale (algebraMap K (PlaneCurveScheme F).functionField)
    (planeCurveGenericCoordinates F i) (planeCurveGenericCoordinates F j i) P n hP

/-- A chart expression exists in the canonical base-field algebra structure
on the actual function field. -/
theorem planeCurveQuadraticSection_generic_representative (F : PlanePolynomial K)
    [IsIntegral (PlaneCurveScheme F)] (i : Fin 3)
    [Nonempty (planeCurveCoordinateOpen F i)]
    (s : (PlaneCurveQuadraticSheaf F).val.obj (op ⊤)) :
    ∃ (n : ℕ) (P : PlanePolynomial K), P.IsHomogeneous n ∧
      aeval (planeCurveGenericCoordinates F i) P =
        schemeGenericLinearMap (K := K) (PlaneCurveQuadraticSheaf F)
          (planeCurveCoordinateOpen F i) (planeCurveQuadraticFrame F i) s := by
  obtain ⟨n, P, hP, heq⟩ := planeCurveCoordinateOpen_generic_representative F i
    (planeCurveQuadraticCoefficient F s i)
  refine ⟨n, P, hP, ?_⟩
  letI : Nonempty (planeCurveInclusion F ⁻¹ᵁ Proj.basicOpen
      (homogeneousSubmodule (Fin 3) K) (X i)) :=
    inferInstanceAs (Nonempty (planeCurveCoordinateOpen F i))
  have hc : planeCurveGenericConstants F i =
      algebraMap K (PlaneCurveScheme F).functionField :=
    planeChartToFunctionField_constants_eq_algebraMap (planeCurveInclusion F) i
  rw [hc, planeCurveQuadraticCoefficient_generic] at heq
  exact heq

/-- Every actual global square section has, in any chosen chart `i`, a
homogeneous numerator of degree `n+2`. In another frame `j`, its denominator
is the `n`th power of the actual ratio `Xᵢ/Xⱼ`. Both the representative and
its compatibility are proved from the actual sheaf. -/
theorem planeCurveQuadraticSection_weighted_representative (F : PlanePolynomial K)
    [IsIntegral (PlaneCurveScheme F)] (i j : Fin 3)
    [Nonempty (planeCurveCoordinateOpen F i)] [Nonempty (planeCurveCoordinateOpen F j)]
    (s : (PlaneCurveQuadraticSheaf F).val.obj (op ⊤)) :
    ∃ (n : ℕ) (B : PlanePolynomial K), B.IsHomogeneous (n + 2) ∧
      aeval (planeCurveGenericCoordinates F j) B =
        schemeGenericLinearMap (K := K) (PlaneCurveQuadraticSheaf F)
          (planeCurveCoordinateOpen F j) (planeCurveQuadraticFrame F j) s *
          (planeCurveGenericCoordinates F j i) ^ n := by
  obtain ⟨n, P, hP, heq⟩ := planeCurveQuadraticSection_generic_representative F i s
  refine ⟨n, P * X i ^ 2, hP.mul (by simpa using (isHomogeneous_X K i).pow 2), ?_⟩
  rw [map_mul, map_pow, aeval_X, planeCurve_homogeneous_aeval_transition F i j P n hP,
    heq, planeCurveQuadratic_generic_transition F i j s]
  ring

/-- Compatible homogeneous numerators for every actual chart of a global
square section. The cross-multiplication identities hold in the actual
homogeneous cone quotient, proved through its full geometric kernel. -/
theorem planeCurveQuadraticSection_cone_representatives
    (F : PlanePolynomial K) (e : ℕ) (hF : F.IsHomogeneous e)
    (hFdeg : 1 < F.totalDegree) (hprime : (Ideal.span {F}).IsPrime)
    (j : Fin 3) (s : (PlaneCurveQuadraticSheaf F).val.obj (op ⊤)) :
    letI := planeCurveScheme_isIntegral F e hF hFdeg hprime
    letI := planeCurveCoordinateOpen_nonempty F e hF hFdeg hprime j
    ∃ (n : Fin 3 → ℕ) (B : Fin 3 → PlanePolynomial K),
      (∀ i, (B i).IsHomogeneous (n i + 2)) ∧
      (∀ i, aeval (planeCurveGenericCoordinates F j) (B i) =
        schemeGenericLinearMap (K := K) (PlaneCurveQuadraticSheaf F)
          (planeCurveCoordinateOpen F j) (planeCurveQuadraticFrame F j) s *
          (planeCurveGenericCoordinates F j i) ^ n i) ∧
      (∀ i k, Ideal.Quotient.mk (Ideal.span {F}) (B i) *
          (Ideal.Quotient.mk (Ideal.span {F}) (X k)) ^ n k =
        Ideal.Quotient.mk (Ideal.span {F}) (B k) *
          (Ideal.Quotient.mk (Ideal.span {F}) (X i)) ^ n i) := by
  letI := planeCurveScheme_isIntegral F e hF hFdeg hprime
  letI : ∀ i, Nonempty (planeCurveCoordinateOpen F i) :=
    fun i => planeCurveCoordinateOpen_nonempty F e hF hFdeg hprime i
  choose n B hB hval using fun i =>
    planeCurveQuadraticSection_weighted_representative F i j s
  refine ⟨n, B, hB, hval, ?_⟩
  intro i k
  have hleft : (B i * X k ^ n k).IsHomogeneous (n i + 2 + n k) :=
    (hB i).mul (by simpa using (isHomogeneous_X K k).pow (n k))
  have hright : (B k * X i ^ n i).IsHomogeneous (n i + 2 + n k) := by
    convert (hB k).mul (by simpa using (isHomogeneous_X K i).pow (n i)) using 1; omega
  have hmem : B i * X k ^ n k - B k * X i ^ n i ∈ Ideal.span {F} := by
    apply (planeCurve_homogeneous_aeval_eq_zero_iff F e hF hFdeg hprime j
      (n i + 2 + n k) _ (hleft.sub hright)).mp
    simp only [map_sub, map_mul, map_pow, aeval_X, hval]
    ring
  have heq := Ideal.Quotient.eq.mpr hmem
  simpa only [map_mul, map_pow] using heq

end EvenQuinticConic
