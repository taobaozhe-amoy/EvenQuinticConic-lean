import EvenQuinticConic.PlaneCurveKaehlerFrames
import EvenQuinticConic.JacobianIrreducible
import EvenQuinticConic.ProjectiveJacobianCriterion
import EvenQuinticConic.AffineOpenKaehlerComparison
import EvenQuinticConic.SchemeKaehlerRestriction
import EvenQuinticConic.SchemeOpenModuleFrames
import EvenQuinticConic.SchemeOpenDifferentialFrames

/-!
# Actual differential-sheaf frames on a smooth plane curve

The derivative principal opens and coordinate ratios below belong to the
actual curve scheme. Top sections of an open subscheme are transported by
its genuine `topIso`; they are not treated as definitionally equal to
sections on the corresponding open of the original scheme.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace MvPolynomial Module

namespace EvenQuinticConic

variable {K : Type} [Field K]

/-- The six possible choices of distinct chart and derivative coordinates. -/
abbrev PlaneDifferentialChartIndex := Σ i : Fin 3, {j : Fin 3 // j ≠ i}

/-- In three coordinates, a coordinate distinct from two specified ones exists. -/
theorem planeDifferential_exists_third (i j : Fin 3) :
    ∃ k : Fin 3, k ≠ i ∧ k ≠ j := by
  fin_cases i <;> fin_cases j <;> decide

/-- A chosen remaining coordinate; its two distinctness properties are proved. -/
def planeDifferentialThirdCoordinate (i j : Fin 3) : Fin 3 :=
  (planeDifferential_exists_third i j).choose

theorem planeDifferentialThirdCoordinate_ne (i j : Fin 3) :
    planeDifferentialThirdCoordinate i j ≠ i ∧
      planeDifferentialThirdCoordinate i j ≠ j :=
  (planeDifferential_exists_third i j).choose_spec

/-- The actual derivative principal open used for a coordinate differential frame. -/
abbrev planeCurveDifferentialOpen (F : PlanePolynomial K) (hF : F.IsHomogeneous 5)
    (i j : Fin 3) : (PlaneCurveScheme F).Opens :=
  (PlaneCurveScheme F).basicOpen (planeCurveGradientSection F hF i j)

/-- The actual differential open is affine. -/
theorem planeCurveDifferentialOpen_isAffine
    (F : PlanePolynomial K) (hF : F.IsHomogeneous 5) (i j : Fin 3) :
    IsAffineOpen (planeCurveDifferentialOpen F hF i j) :=
  planeCurveGradientBasicOpen_isAffine F hF i j

/-- The actual six derivative opens cover the curve under the original
nonzero-vector Jacobian condition. -/
theorem planeCurveDifferentialOpen_cover_of_jacobian [IsAlgClosed K]
    (F : PlanePolynomial K) (hF : F.IsHomogeneous 5)
    (hJac : ∀ v : Fin 3 → K, v ≠ 0 → eval v F = 0 →
      ∃ i : Fin 3, eval v (pderiv i F) ≠ 0) :
    (⨆ a : PlaneDifferentialChartIndex,
      planeCurveDifferentialOpen F hF a.1 a.2.1) = ⊤ :=
  planeCurveGradientBasicOpen_cover F hF
    (projective_gradient_of_rational_jacobian F hJac)

/-- The remaining coordinate ratio, restricted to the derivative open. -/
def planeCurveDifferentialCoordinate (F : PlanePolynomial K) (hF : F.IsHomogeneous 5)
    (i j k : Fin 3) : Γ(PlaneCurveScheme F, planeCurveDifferentialOpen F hF i j) :=
  (PlaneCurveScheme F).presheaf.map (homOfLE
    ((PlaneCurveScheme F).basicOpen_le (planeCurveGradientSection F hF i j))).op
      (planeCurveChartCoordinates F i k)

/-- The same coordinate as a top section of the genuine open subscheme. -/
def planeCurveDifferentialCoordinateOnOpen
    (F : PlanePolynomial K) (hF : F.IsHomogeneous 5) (i j k : Fin 3) :
    Γ((planeCurveDifferentialOpen F hF i j).toScheme, ⊤) :=
  (planeCurveDifferentialOpen F hF i j).topIso.inv
    (planeCurveDifferentialCoordinate F hF i j k)

/-- The top-section coordinate is transported by the actual restriction isomorphism. -/
theorem planeCurveDifferentialCoordinateOnOpen_topIso
    (F : PlanePolynomial K) (hF : F.IsHomogeneous 5) (i j k : Fin 3) :
    (planeCurveDifferentialOpen F hF i j).topIso.hom
      (planeCurveDifferentialCoordinateOnOpen F hF i j k) =
        planeCurveDifferentialCoordinate F hF i j k := by
  exact ConcreteCategory.congr_hom
    (planeCurveDifferentialOpen F hF i j).topIso.inv_hom_id
    (planeCurveDifferentialCoordinate F hF i j k)

/-- The computed presheaf basis has the precise coordinate needed for the sheaf frame. -/
theorem planeCurveDifferentialCoordinate_basis
    (F : PlanePolynomial K) (hF : F.IsHomogeneous 5)
    (hFdeg : 1 < F.totalDegree) (hprime : (Ideal.span {F}).IsPrime)
    (i j k : Fin 3) (hji : j ≠ i) (hki : k ≠ i) (hkj : k ≠ j) :
    planeCurveGradientKaehlerBasis F hF hFdeg hprime i j k hji hki hkj () =
      CommRingCat.KaehlerDifferential.d
        (planeCurveDifferentialCoordinate F hF i j k) :=
  planeCurveGradientKaehlerBasis_apply F hF hFdeg hprime i j k hji hki hkj

/-- The actual differential sheaf on the derivative open subscheme is
trivialized by the proved coordinate differential basis. -/
def planeCurveDifferentialOpenTrivialization
    (F : PlanePolynomial K) (hF : F.IsHomogeneous 5)
    (hFdeg : 1 < F.totalDegree) (hprime : (Ideal.span {F}).IsPrime)
    (i j k : Fin 3) (hji : j ≠ i) (hki : k ≠ i) (hkj : k ≠ j) :
    SheafOfModules.unit (planeCurveDifferentialOpen F hF i j).toScheme.ringCatSheaf ≅
      schemeKaehlerSheaf ((planeCurveDifferentialOpen F hF i j).ι ≫
        planeCurveStructure F) :=
  (affineOpenKaehlerBasisDifferentialTrivialization (planeCurveStructure F)
    (planeCurveDifferentialOpen F hF i j) (planeCurveDifferentialOpen_isAffine F hF i j)
    (planeCurveGradientKaehlerBasis F hF hFdeg hprime i j k hji hki hkj)
    (planeCurveDifferentialCoordinate F hF i j k)
    (planeCurveDifferentialCoordinate_basis F hF hFdeg hprime i j k hji hki hkj)).val

/-- The same actual frame for the restriction of the original curve's
differential sheaf, using the proved restriction comparison. -/
def planeCurveDifferentialRestrictedTrivialization
    (F : PlanePolynomial K) (hF : F.IsHomogeneous 5)
    (hFdeg : 1 < F.totalDegree) (hprime : (Ideal.span {F}).IsPrime)
    (i j k : Fin 3) (hji : j ≠ i) (hki : k ≠ i) (hkj : k ≠ j) :
    SheafOfModules.unit (planeCurveDifferentialOpen F hF i j).toScheme.ringCatSheaf ≅
      (schemeModuleRestrict (planeCurveDifferentialOpen F hF i j)).obj
        (schemeKaehlerSheaf (planeCurveStructure F)) :=
  planeCurveDifferentialOpenTrivialization F hF hFdeg hprime i j k hji hki hkj ≪≫
    (schemeKaehlerRestrictIso (planeCurveStructure F)
      (planeCurveDifferentialOpen F hF i j)).symm

/-- A coherent frame of the actual differential sheaf on every original
subopen of the derivative open. The two sites are related by a proved
transport, not by definitional identification. -/
def planeCurveDifferentialSheafFrame
    (F : PlanePolynomial K) (hF : F.IsHomogeneous 5)
    (hFdeg : 1 < F.totalDegree) (hprime : (Ideal.span {F}).IsPrime)
    (i j k : Fin 3) (hji : j ≠ i) (hki : k ≠ i) (hkj : k ≠ j) :
    ModuleSheafFrame (schemeKaehlerSheaf (planeCurveStructure F))
      (planeCurveDifferentialOpen F hF i j) :=
  schemeOpenDifferentialFrame (planeCurveStructure F)
    (planeCurveDifferentialOpen F hF i j)
    (planeCurveDifferentialOpenTrivialization F hF hFdeg hprime
      i j k hji hki hkj).symm

/-- The actual local unit isomorphism on the original `Over U` site. -/
def planeCurveDifferentialSheafLocalUnitIso
    (F : PlanePolynomial K) (hF : F.IsHomogeneous 5)
    (hFdeg : 1 < F.totalDegree) (hprime : (Ideal.span {F}).IsPrime)
    (i j k : Fin 3) (hji : j ≠ i) (hki : k ≠ i) (hkj : k ≠ j) :
    (schemeKaehlerSheaf (planeCurveStructure F)).over
      (planeCurveDifferentialOpen F hF i j) ≅
        SheafOfModules.unit ((PlaneCurveScheme F).ringCatSheaf.over
          (planeCurveDifferentialOpen F hF i j)) :=
  (planeCurveDifferentialSheafFrame F hF hFdeg hprime i j k hji hki hkj).localUnitIso


/-- The affine-open trivialization has precisely the differential of the
remaining projective coordinate as its genuine top generator. -/
theorem planeCurveDifferentialOpenTrivialization_top_one
    (F : PlanePolynomial K) (hF : F.IsHomogeneous 5)
    (hFdeg : 1 < F.totalDegree) (hprime : (Ideal.span {F}).IsPrime)
    (i j k : Fin 3) (hji : j ≠ i) (hki : k ≠ i) (hkj : k ≠ j) :
    (planeCurveDifferentialOpenTrivialization F hF hFdeg hprime
      i j k hji hki hkj).hom.val.app (op ⊤)
        (1 : Γ((planeCurveDifferentialOpen F hF i j).toScheme, ⊤)) =
      (schemeKaehlerDerivation ((planeCurveDifferentialOpen F hF i j).ι ≫
        planeCurveStructure F)).d (planeCurveDifferentialCoordinateOnOpen F hF i j k) :=
  (affineOpenKaehlerBasisDifferentialTrivialization (planeCurveStructure F)
    (planeCurveDifferentialOpen F hF i j) (planeCurveDifferentialOpen_isAffine F hF i j)
    (planeCurveGradientKaehlerBasis F hF hFdeg hprime i j k hji hki hkj)
    (planeCurveDifferentialCoordinate F hF i j k)
    (planeCurveDifferentialCoordinate_basis F hF hFdeg hprime i j k hji hki hkj)).property

/-- On every original subopen, the proved sheaf-frame generator is exactly
the actual differential of the restricted coordinate ratio. -/
theorem planeCurveDifferentialSheafFrame_generator
    (F : PlanePolynomial K) (hF : F.IsHomogeneous 5)
    (hFdeg : 1 < F.totalDegree) (hprime : (Ideal.span {F}).IsPrime)
    (i j k : Fin 3) (hji : j ≠ i) (hki : k ≠ i) (hkj : k ≠ j)
    (W : (PlaneCurveScheme F).Opens) (hW : W ≤ planeCurveDifferentialOpen F hF i j) :
    ((planeCurveDifferentialSheafFrame F hF hFdeg hprime i j k hji hki hkj).coordinate
      W hW).symm (1 : Γ(PlaneCurveScheme F, W)) =
      (schemeKaehlerDerivation (planeCurveStructure F)).d
        (UnitTransition.res hW (planeCurveDifferentialCoordinate F hF i j k)) :=
  schemeOpenDifferentialFrame_generator_subopen (planeCurveStructure F)
    (planeCurveDifferentialOpen F hF i j)
    (planeCurveDifferentialOpenTrivialization F hF hFdeg hprime i j k hji hki hkj).symm
    (planeCurveDifferentialCoordinate F hF i j k)
    (planeCurveDifferentialOpenTrivialization_top_one F hF hFdeg hprime i j k hji hki hkj)
    W hW

end EvenQuinticConic
