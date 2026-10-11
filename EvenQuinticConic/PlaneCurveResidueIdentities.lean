import EvenQuinticConic.PlaneCurveKaehlerFrames
import EvenQuinticConic.PlaneResidueCrossTransition

/-!
# Residue identities in actual curve overlap rings

The coefficients, coordinate restrictions, and derivative units below are
constructed in the structure sheaf of the actual curve. The differential
identities live in the genuine Kähler module of each overlap section ring.
No sheafification comparison or global adjunction gluing is assumed here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace MvPolynomial

namespace EvenQuinticConic

variable {K : Type} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual base-field action on sections used by the curve differential presheaf. -/
def planeCurveResidueSectionAlgebra (F : PlanePolynomial K)
    (W : (PlaneCurveScheme F).Opens) : Algebra K Γ(PlaneCurveScheme F, W) :=
  ((schemeConstantsPresheafHom (planeCurveStructure F)).app (op W)).hom.toAlgebra

attribute [local instance] planeCurveResidueSectionAlgebra

/-- Actual normalized coordinate sections restricted to a smaller curve open. -/
def planeCurveResidueCoordinates (F : PlanePolynomial K) (i : Fin 3)
    (W : (PlaneCurveScheme F).Opens) (hi : W ≤ planeCurveCoordinateOpen F i) :
    Fin 3 → Γ(PlaneCurveScheme F, W) :=
  fun k => UnitTransition.res hi (planeCurveChartCoordinates F i k)

@[simp]
theorem planeCurveResidueCoordinates_self (F : PlanePolynomial K) (i : Fin 3)
    (W : (PlaneCurveScheme F).Opens) (hi : W ≤ planeCurveCoordinateOpen F i) :
    planeCurveResidueCoordinates F i W hi i = 1 := by
  simp [planeCurveResidueCoordinates]

/-- Evaluation of any polynomial in the actual restricted coordinates is
restriction of its evaluation on the actual coordinate chart. -/
theorem planeCurveResidueCoordinates_aeval
    (F : PlanePolynomial K) [IsIntegral (PlaneCurveScheme F)] (i : Fin 3)
    [Nonempty (planeCurveCoordinateOpen F i)]
    (W : (PlaneCurveScheme F).Opens) (hi : W ≤ planeCurveCoordinateOpen F i)
    (P : PlanePolynomial K) :
    aeval (planeCurveResidueCoordinates F i W hi) P =
      UnitTransition.res hi (planeCurveChartPolynomialMap F i P) := by
  have hc : algebraMap K Γ(PlaneCurveScheme F, W) =
      (UnitTransition.res hi).comp (planeCurveChartConstants F i) := by
    change ((schemeConstantsPresheafHom (planeCurveStructure F)).app (op W)).hom = _
    rw [planeCurveChartConstants_eq_differentialConstants]
    have h := (schemeConstantsPresheafHom (planeCurveStructure F)).naturality
      (homOfLE hi).op
    simpa only [Functor.const_obj_map, Category.id_comp, CommRingCat.hom_comp,
      UnitTransition.res] using congrArg CommRingCat.Hom.hom h
  change eval₂ (algebraMap K Γ(PlaneCurveScheme F, W)) _ P =
    UnitTransition.res hi (eval₂ (planeCurveChartConstants F i)
      (planeCurveChartCoordinates F i) P)
  rw [eval₂_comp_left, hc]
  rfl

/-- On a subopen of the genuine derivative principal open, the restricted
derivative is a unit, proved by the structure sheaf's principal-open theorem. -/
theorem planeCurveGradient_isUnit_on
    (F : PlanePolynomial K) (hF : F.IsHomogeneous 5) (i j : Fin 3)
    (W : (PlaneCurveScheme F).Opens)
    (hW : W ≤ (PlaneCurveScheme F).basicOpen (planeCurveGradientSection F hF i j)) :
    IsUnit (UnitTransition.res
      (hW.trans ((PlaneCurveScheme F).basicOpen_le (planeCurveGradientSection F hF i j)))
      (planeCurveGradientSection F hF i j)) := by
  have h := ((PlaneCurveScheme F).toRingedSpace.isUnit_res_basicOpen
    (planeCurveGradientSection F hF i j)).map (UnitTransition.res hW)
  change IsUnit (UnitTransition.res hW (UnitTransition.res
    ((PlaneCurveScheme F).basicOpen_le (planeCurveGradientSection F hF i j))
    (planeCurveGradientSection F hF i j))) at h
  simpa only [UnitTransition.res_res] using h

/-- The actual derivative unit on any subordinate overlap open. -/
def planeCurveGradientUnitOn
    (F : PlanePolynomial K) (hF : F.IsHomogeneous 5) (i j : Fin 3)
    (W : (PlaneCurveScheme F).Opens)
    (hW : W ≤ (PlaneCurveScheme F).basicOpen (planeCurveGradientSection F hF i j)) :
    Γ(PlaneCurveScheme F, W)ˣ :=
  (planeCurveGradient_isUnit_on F hF i j W hW).unit

@[simp]
theorem planeCurveGradientUnitOn_val
    (F : PlanePolynomial K) (hF : F.IsHomogeneous 5) (i j : Fin 3)
    (W : (PlaneCurveScheme F).Opens)
    (hW : W ≤ (PlaneCurveScheme F).basicOpen (planeCurveGradientSection F hF i j)) :
    (planeCurveGradientUnitOn F hF i j W hW : Γ(PlaneCurveScheme F, W)) =
      UnitTransition.res
        (hW.trans ((PlaneCurveScheme F).basicOpen_le (planeCurveGradientSection F hF i j)))
        (planeCurveGradientSection F hF i j) :=
  (planeCurveGradient_isUnit_on F hF i j W hW).unit_spec

/-- The original equation vanishes after restricting the actual coordinates,
proved from the chart equation rather than assumed on the overlap. -/
theorem planeCurveResidueCoordinates_equation
    (F : PlanePolynomial K) (hF : F.IsHomogeneous 5)
    (hFdeg : 1 < F.totalDegree) (hprime : (Ideal.span {F}).IsPrime)
    (i : Fin 3) (W : (PlaneCurveScheme F).Opens)
    (hi : W ≤ planeCurveCoordinateOpen F i) :
    aeval (planeCurveResidueCoordinates F i W hi) F = 0 := by
  letI := planeCurveScheme_isIntegral F 5 hF hFdeg hprime
  letI := planeCurveCoordinateOpen_nonempty F 5 hF hFdeg hprime i
  rw [planeCurveResidueCoordinates_aeval]
  have h := (planeCurveChartPolynomialMap_homogeneous_eq_zero_iff
    F 5 hF hFdeg hprime i 5 F hF).mpr (Ideal.subset_span (Set.mem_singleton F))
  rw [h, map_zero]

/-- The actual restricted derivative unit is the partial derivative evaluated
at the actual restricted normalized coordinates. -/
theorem planeCurveGradientUnitOn_eq_aeval
    (F : PlanePolynomial K) (hF : F.IsHomogeneous 5)
    [IsIntegral (PlaneCurveScheme F)] (i j : Fin 3)
    [Nonempty (planeCurveCoordinateOpen F i)]
    (W : (PlaneCurveScheme F).Opens)
    (hW : W ≤ (PlaneCurveScheme F).basicOpen (planeCurveGradientSection F hF i j))
    (hi : W ≤ planeCurveCoordinateOpen F i) :
    (planeCurveGradientUnitOn F hF i j W hW : Γ(PlaneCurveScheme F, W)) =
      aeval (planeCurveResidueCoordinates F i W hi) (pderiv j F) := by
  rw [planeCurveResidueCoordinates_aeval, planeCurveChartPolynomialMap_pderiv,
    planeCurveGradientUnitOn_val]

/-- The signed residue swap on every actual common subopen of the two
nonradial derivative principal opens of one coordinate chart. The units,
coordinates, equation, and base-field action all come from the actual curve. -/
theorem planeCurveResidue_sameChart
    (F : PlanePolynomial K) (hF : F.IsHomogeneous 5)
    (hFdeg : 1 < F.totalDegree) (hprime : (Ideal.span {F}).IsPrime)
    (i j k : Fin 3) (hji : j ≠ i) (hki : k ≠ i) (hkj : k ≠ j)
    (W : (PlaneCurveScheme F).Opens)
    (hj : W ≤ (PlaneCurveScheme F).basicOpen (planeCurveGradientSection F hF i j))
    (hk : W ≤ (PlaneCurveScheme F).basicOpen (planeCurveGradientSection F hF i k)) :
    let hi := hj.trans ((PlaneCurveScheme F).basicOpen_le (planeCurveGradientSection F hF i j))
    (↑(planeCurveGradientUnitOn F hF i j W hj)⁻¹ : Γ(PlaneCurveScheme F, W)) •
        KaehlerDifferential.D K Γ(PlaneCurveScheme F, W)
          (planeCurveResidueCoordinates F i W hi k) =
      -((↑(planeCurveGradientUnitOn F hF i k W hk)⁻¹ : Γ(PlaneCurveScheme F, W)) •
        KaehlerDifferential.D K Γ(PlaneCurveScheme F, W)
          (planeCurveResidueCoordinates F i W hi j)) := by
  letI := planeCurveScheme_isIntegral F 5 hF hFdeg hprime
  letI := planeCurveCoordinateOpen_nonempty F 5 hF hFdeg hprime i
  dsimp only
  apply planeChart_kaehler_residue_swap F _ i j k hji hki hkj
  · exact planeCurveResidueCoordinates_self F i W _
  · exact planeCurveResidueCoordinates_equation F hF hFdeg hprime i W _
  · exact planeCurveGradientUnitOn_eq_aeval F hF i j W hj _
  · exact planeCurveGradientUnitOn_eq_aeval F hF i k W hk _

/-- The actual invertible coordinate ratio on a common subopen of two
projective coordinate charts, taken from the already constructed cocycle. -/
def planeCurveResidueCoordinateUnit
    (F : PlanePolynomial K) (i l : Fin 3) (W : (PlaneCurveScheme F).Opens)
    (hi : W ≤ planeCurveCoordinateOpen F i) (hl : W ≤ planeCurveCoordinateOpen F l) :
    Γ(PlaneCurveScheme F, W)ˣ :=
  (planeCurveHyperplaneTransition F).transition i l W hi hl

/-- The cocycle unit is the actual restricted ratio `X_l / X_i`. -/
theorem planeCurveResidueCoordinateUnit_val
    (F : PlanePolynomial K) (i l : Fin 3) (W : (PlaneCurveScheme F).Opens)
    (hi : W ≤ planeCurveCoordinateOpen F i) (hl : W ≤ planeCurveCoordinateOpen F l) :
    (planeCurveResidueCoordinateUnit F i l W hi hl : Γ(PlaneCurveScheme F, W)) =
      planeCurveResidueCoordinates F i W hi l := by
  have h := planeCurveCoordinateFunction_compatible F l i l W hi hl
  change planeCurveResidueCoordinates F i W hi l =
    (planeCurveResidueCoordinateUnit F i l W hi hl : Γ(PlaneCurveScheme F, W)) *
      planeCurveResidueCoordinates F l W hl l at h
  simpa only [planeCurveResidueCoordinates_self, mul_one] using h.symm

/-- Coordinate change on the actual curve overlap follows from the already
proved projective coordinate compatibility, with no transition equation input. -/
theorem planeCurveResidueCoordinates_changeChart
    (F : PlanePolynomial K) (i l : Fin 3) (W : (PlaneCurveScheme F).Opens)
    (hi : W ≤ planeCurveCoordinateOpen F i) (hl : W ≤ planeCurveCoordinateOpen F l)
    (a : Fin 3) :
    planeCurveResidueCoordinates F l W hl a =
      planeCurveResidueCoordinates F i W hi a *
        (↑(planeCurveResidueCoordinateUnit F i l W hi hl)⁻¹ : Γ(PlaneCurveScheme F, W)) := by
  let u := planeCurveResidueCoordinateUnit F i l W hi hl
  have h := planeCurveCoordinateFunction_compatible F a i l W hi hl
  change planeCurveResidueCoordinates F i W hi a =
    (u : Γ(PlaneCurveScheme F, W)) * planeCurveResidueCoordinates F l W hl a at h
  rw [h, mul_right_comm, Units.mul_inv, one_mul]

/-- Every actual homogeneous polynomial value has its predicted scaling
under actual projective coordinate restriction maps. -/
theorem planeCurveResidueCoordinates_aeval_changeChart
    (F : PlanePolynomial K) (i l : Fin 3) (W : (PlaneCurveScheme F).Opens)
    (hi : W ≤ planeCurveCoordinateOpen F i) (hl : W ≤ planeCurveCoordinateOpen F l)
    (P : PlanePolynomial K) (d : ℕ) (hP : P.IsHomogeneous d) :
    aeval (planeCurveResidueCoordinates F l W hl) P =
      aeval (planeCurveResidueCoordinates F i W hi) P *
        (↑(planeCurveResidueCoordinateUnit F i l W hi hl)⁻¹ : Γ(PlaneCurveScheme F, W)) ^ d := by
  have hv := funext (planeCurveResidueCoordinates_changeChart F i l W hi hl)
  rw [hv, aeval_def, aeval_def, homogeneous_eval₂_scale _ _ _ _ d hP]

/-- Units obtained independently from the two actual derivative principal
opens have exactly the fourth-power coordinate transition. -/
theorem planeCurveGradientUnitOn_changeChart
    (F : PlanePolynomial K) (hF : F.IsHomogeneous 5)
    [IsIntegral (PlaneCurveScheme F)] (i l j : Fin 3)
    [Nonempty (planeCurveCoordinateOpen F i)] [Nonempty (planeCurveCoordinateOpen F l)]
    (W : (PlaneCurveScheme F).Opens)
    (hij : W ≤ (PlaneCurveScheme F).basicOpen (planeCurveGradientSection F hF i j))
    (hlj : W ≤ (PlaneCurveScheme F).basicOpen (planeCurveGradientSection F hF l j))
    (hi : W ≤ planeCurveCoordinateOpen F i) (hl : W ≤ planeCurveCoordinateOpen F l) :
    planeCurveGradientUnitOn F hF l j W hlj =
      planeCurveGradientUnitOn F hF i j W hij *
        (planeCurveResidueCoordinateUnit F i l W hi hl)⁻¹ ^ 4 := by
  apply Units.ext
  rw [Units.val_mul, Units.val_pow_eq_pow_val,
    planeCurveGradientUnitOn_eq_aeval F hF l j W hlj hl,
    planeCurveGradientUnitOn_eq_aeval F hF i j W hij hi]
  exact planeCurveResidueCoordinates_aeval_changeChart F i l W hi hl
    (pderiv j F) 4 (by simpa using hF.pderiv (i := j))

/-- The common-derivative cross-chart residue identity in the actual overlap
section ring, using the two independently constructed derivative units. -/
theorem planeCurveResidue_commonDerivative
    (F : PlanePolynomial K) (hF : F.IsHomogeneous 5)
    (hFdeg : 1 < F.totalDegree) (hprime : (Ideal.span {F}).IsPrime)
    (i l j : Fin 3) (W : (PlaneCurveScheme F).Opens)
    (hij : W ≤ (PlaneCurveScheme F).basicOpen (planeCurveGradientSection F hF i j))
    (hlj : W ≤ (PlaneCurveScheme F).basicOpen (planeCurveGradientSection F hF l j)) :
    let hi := hij.trans ((PlaneCurveScheme F).basicOpen_le (planeCurveGradientSection F hF i j))
    let hl := hlj.trans ((PlaneCurveScheme F).basicOpen_le (planeCurveGradientSection F hF l j));
    -((↑(planeCurveGradientUnitOn F hF l j W hlj)⁻¹ : Γ(PlaneCurveScheme F, W)) •
        KaehlerDifferential.D K Γ(PlaneCurveScheme F, W)
          (planeCurveResidueCoordinates F l W hl i)) =
      (planeCurveResidueCoordinates F i W hi l) ^ 2 •
        ((↑(planeCurveGradientUnitOn F hF i j W hij)⁻¹ : Γ(PlaneCurveScheme F, W)) •
          KaehlerDifferential.D K Γ(PlaneCurveScheme F, W)
            (planeCurveResidueCoordinates F i W hi l)) := by
  letI := planeCurveScheme_isIntegral F 5 hF hFdeg hprime
  letI := planeCurveCoordinateOpen_nonempty F 5 hF hFdeg hprime i
  letI := planeCurveCoordinateOpen_nonempty F 5 hF hFdeg hprime l
  dsimp only
  rw [planeCurveGradientUnitOn_changeChart F hF i l j W hij hlj,
    planeCurveResidueCoordinates_changeChart F i l]
  exact (quintic_residue_transition_common_derivative F hF _ i l j
    (planeCurveResidueCoordinates_self F i W _)
    (planeCurveResidueCoordinateUnit F i l W _ _)
    (planeCurveGradientUnitOn F hF i j W hij)
    (planeCurveResidueCoordinateUnit_val F i l W _ _)
    (planeCurveGradientUnitOn_eq_aeval F hF i j W hij _)).2

/-- A unit derivative from the second chart, multiplied by the actual fourth
power coordinate unit, is the original chart's evaluated derivative. This
also proves invertibility when no derivative-open inclusion on that chart
was supplied. -/
theorem planeCurveGradientUnitOn_scaleBack
    (F : PlanePolynomial K) (hF : F.IsHomogeneous 5)
    [IsIntegral (PlaneCurveScheme F)] (i l j : Fin 3)
    [Nonempty (planeCurveCoordinateOpen F l)]
    (W : (PlaneCurveScheme F).Opens)
    (hlj : W ≤ (PlaneCurveScheme F).basicOpen (planeCurveGradientSection F hF l j))
    (hi : W ≤ planeCurveCoordinateOpen F i) (hl : W ≤ planeCurveCoordinateOpen F l) :
    (↑(planeCurveGradientUnitOn F hF l j W hlj *
      planeCurveResidueCoordinateUnit F i l W hi hl ^ 4) : Γ(PlaneCurveScheme F, W)) =
      aeval (planeCurveResidueCoordinates F i W hi) (pderiv j F) := by
  rw [Units.val_mul, Units.val_pow_eq_pow_val,
    planeCurveGradientUnitOn_eq_aeval F hF l j W hlj hl,
    planeCurveResidueCoordinates_aeval_changeChart F i l W hi hl
      (pderiv j F) 4 (by simpa using hF.pderiv (i := j))]
  rw [mul_assoc, ← mul_pow, Units.inv_mul, one_pow, mul_one]

/-- The radial-derivative cross-chart residue identity on every actual
common subopen of the indicated derivative principal opens. Both coordinate
change and the radial derivative unit are derived from actual section maps. -/
theorem planeCurveResidue_radialDerivatives
    (F : PlanePolynomial K) (hF : F.IsHomogeneous 5)
    (hFdeg : 1 < F.totalDegree) (hprime : (Ideal.span {F}).IsPrime)
    (i l k : Fin 3) (hli : l ≠ i) (hki : k ≠ i) (hkl : k ≠ l)
    (W : (PlaneCurveScheme F).Opens)
    (hil : W ≤ (PlaneCurveScheme F).basicOpen (planeCurveGradientSection F hF i l))
    (hli' : W ≤ (PlaneCurveScheme F).basicOpen (planeCurveGradientSection F hF l i)) :
    let hi := hil.trans ((PlaneCurveScheme F).basicOpen_le (planeCurveGradientSection F hF i l))
    let hl := hli'.trans ((PlaneCurveScheme F).basicOpen_le (planeCurveGradientSection F hF l i));
    -((↑(planeCurveGradientUnitOn F hF l i W hli')⁻¹ : Γ(PlaneCurveScheme F, W)) •
        KaehlerDifferential.D K Γ(PlaneCurveScheme F, W)
          (planeCurveResidueCoordinates F l W hl k)) =
      (planeCurveResidueCoordinates F i W hi l) ^ 2 •
        ((↑(planeCurveGradientUnitOn F hF i l W hil)⁻¹ : Γ(PlaneCurveScheme F, W)) •
          KaehlerDifferential.D K Γ(PlaneCurveScheme F, W)
            (planeCurveResidueCoordinates F i W hi k)) := by
  letI := planeCurveScheme_isIntegral F 5 hF hFdeg hprime
  letI := planeCurveCoordinateOpen_nonempty F 5 hF hFdeg hprime i
  letI := planeCurveCoordinateOpen_nonempty F 5 hF hFdeg hprime l
  let hi := hil.trans ((PlaneCurveScheme F).basicOpen_le (planeCurveGradientSection F hF i l))
  let hl := hli'.trans ((PlaneCurveScheme F).basicOpen_le (planeCurveGradientSection F hF l i))
  let u := planeCurveResidueCoordinateUnit F i l W hi hl
  let p := planeCurveGradientUnitOn F hF i l W hil
  let q := planeCurveGradientUnitOn F hF l i W hli' * u ^ 4
  have hq : q * (u⁻¹) ^ 4 = planeCurveGradientUnitOn F hF l i W hli' := by
    dsimp only [q]
    rw [mul_assoc, ← mul_pow, mul_inv_cancel, one_pow, mul_one]
  have h := (quintic_residue_transition_radial_derivatives F hF
    (planeCurveResidueCoordinates F i W hi) i l k hli hki hkl
    (planeCurveResidueCoordinates_self F i W hi)
    (planeCurveResidueCoordinates_equation F hF hFdeg hprime i W hi)
    u p q (planeCurveResidueCoordinateUnit_val F i l W hi hl)
    (planeCurveGradientUnitOn_eq_aeval F hF i l W hil hi)
    (planeCurveGradientUnitOn_scaleBack F hF i l i W hli' hi hl)).2
  rw [hq] at h
  dsimp only
  rw [planeCurveResidueCoordinates_changeChart F i l W hi hl k]
  exact h

end EvenQuinticConic
