import EvenQuinticConic.JacobianLocalization

/-!
# The Jacobian presentation of an affine plane-curve chart

If an algebra has coordinate presentation with relations `F` and `X i - 1`,
choosing a second coordinate `j ≠ i` gives determinant `∂ F / ∂ X j` and
relative dimension one. Inverting that actual derivative therefore gives a
standard smooth algebra of relative dimension one.
-/

noncomputable section

namespace EvenQuinticConic

open Algebra MvPolynomial

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- The two equations defining the dehomogenized hypersurface chart. -/
def planeChartRelations (F : MvPolynomial (Fin 3) R) (i : Fin 3) :
    Fin 2 → MvPolynomial (Fin 3) R := ![F, X i - 1]

/-- The relations are exactly the hypersurface equation and the chart equation. -/
theorem planeChartRelations_range (F : MvPolynomial (Fin 3) R) (i : Fin 3) :
    Set.range (planeChartRelations F i) = {F, X i - 1} := by
  ext f
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨a, rfl⟩
    fin_cases a <;> simp [planeChartRelations]
  · rintro (rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩

/-- An actual finite presentation of a dehomogenized plane hypersurface,
with derivative columns ordered so that its determinant has positive sign. -/
def planeChartPreSubmersivePresentation
    (F : MvPolynomial (Fin 3) R) (i j : Fin 3) (hji : j ≠ i)
    (v : Fin 3 → S) (hv : Function.Surjective (aeval (R := R) v))
    (hker : RingHom.ker (aeval (R := R) v) = Ideal.span {F, X i - 1}) :
    PreSubmersivePresentation R S (Fin 3) (Fin 2) where
  toGenerators := Generators.ofSurjective v hv
  relation := planeChartRelations F i
  span_range_relation_eq_ker := by
    rw [Generators.ker_eq_ker_aeval_val]
    change Ideal.span (Set.range (planeChartRelations F i)) = RingHom.ker (aeval v)
    rw [planeChartRelations_range, hker]
  map := ![j, i]
  map_inj := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all

/-- The chosen two-by-two Jacobian is the evaluated partial derivative. -/
theorem planeChartPreSubmersivePresentation_jacobian
    (F : MvPolynomial (Fin 3) R) (i j : Fin 3) (hji : j ≠ i)
    (v : Fin 3 → S) (hv : Function.Surjective (aeval (R := R) v))
    (hker : RingHom.ker (aeval (R := R) v) = Ideal.span {F, X i - 1}) :
    (planeChartPreSubmersivePresentation F i j hji v hv hker).jacobian =
      aeval v (pderiv j F) := by
  rw [PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det, Matrix.det_fin_two]
  simp [PreSubmersivePresentation.jacobiMatrix_apply,
    planeChartPreSubmersivePresentation, planeChartRelations,
    Generators.algebraMap_apply, Generators.ofSurjective, Ne.symm hji]

/-- The hypersurface chart presentation has relative dimension one. -/
theorem planeChartPreSubmersivePresentation_dimension
    (F : MvPolynomial (Fin 3) R) (i j : Fin 3) (hji : j ≠ i)
    (v : Fin 3 → S) (hv : Function.Surjective (aeval (R := R) v))
    (hker : RingHom.ker (aeval (R := R) v) = Ideal.span {F, X i - 1}) :
    (planeChartPreSubmersivePresentation F i j hji v hv hker).dimension = 1 := by
  simp [Presentation.dimension]

/-- Inverting a non-chart partial derivative makes the actual affine chart
standard smooth of relative dimension one. -/
theorem planeChart_derivative_localization_isStandardSmooth
    (F : MvPolynomial (Fin 3) R) (i j : Fin 3) (hji : j ≠ i)
    (v : Fin 3 → S) (hv : Function.Surjective (aeval (R := R) v))
    (hker : RingHom.ker (aeval (R := R) v) = Ideal.span {F, X i - 1})
    (T : Type*) [CommRing T] [Algebra R T] [Algebra S T]
    [IsScalarTower R S T] [IsLocalization.Away (aeval v (pderiv j F)) T] :
    IsStandardSmoothOfRelativeDimension 1 R T := by
  let P := planeChartPreSubmersivePresentation F i j hji v hv hker
  have hJ : P.jacobian = aeval v (pderiv j F) :=
    planeChartPreSubmersivePresentation_jacobian F i j hji v hv hker
  haveI : IsLocalization.Away P.jacobian T := by rw [hJ]; infer_instance
  have hdim : P.dimension = 1 :=
    planeChartPreSubmersivePresentation_dimension F i j hji v hv hker
  simpa only [hdim] using presentation_jacobian_localization_isStandardSmooth P T

end EvenQuinticConic
