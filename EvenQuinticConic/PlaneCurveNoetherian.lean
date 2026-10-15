import EvenQuinticConic.PlaneChartPolynomialMap
import EvenQuinticConic.SchemeKaehlerSheaf
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Ring hypotheses on the actual plane-curve charts

The standard chart rings are quotients of a polynomial ring in three
variables over the base field. Their Noetherianity is consequently proved
for every defining polynomial, without any smoothness or degree assumption.
Invertibility of two on every open follows from the actual structural
constant sections and the corresponding hypothesis on the field.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
namespace EvenQuinticConic
variable {K : Type} [Field K]

/-- Every standard actual plane-curve chart ring is Noetherian. -/
instance planeCurveCoordinateOpen_isNoetherian (F : PlanePolynomial K) (i : Fin 3) :
    IsNoetherianRing Γ(PlaneCurveScheme F, planeCurveCoordinateOpen F i) :=
  isNoetherianRing_of_surjective (PlanePolynomial K) _
    (planeCurveChartPolynomialMap F i) (planeCurveChartPolynomialMap_surjective F i)

/-- The actual structural constants send a unit two to a unit on every open,
including the empty open. -/
theorem planeCurveSections_isUnit_two [Invertible (2 : K)]
    (F : PlanePolynomial K) (V : (PlaneCurveScheme F).Opens) :
    IsUnit (2 : Γ(PlaneCurveScheme F, V)) := by
  simpa only [map_ofNat] using
    (isUnit_of_invertible (2 : K)).map
      ((schemeConstantsPresheafHom (planeCurveStructure F)).app (op V)).hom

/-- No separate section-ring characteristic hypothesis is required. -/
instance planeCurveSectionsTwo [Invertible (2 : K)]
    (F : PlanePolynomial K) (V : (PlaneCurveScheme F).Opens) :
    Invertible (2 : Γ(PlaneCurveScheme F, V)) :=
  (planeCurveSections_isUnit_two F V).invertible

end EvenQuinticConic
