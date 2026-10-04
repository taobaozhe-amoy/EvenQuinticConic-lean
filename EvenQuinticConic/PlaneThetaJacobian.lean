import EvenQuinticConic.PlaneThetaSmooth
import EvenQuinticConic.PlaneJacobianSmooth
import EvenQuinticConic.JacobianIrreducible
import EvenQuinticConic.ProjectiveJacobianCriterion

/-!
# Theta vanishing from the explicit nonsingular quintic equation

The hypothesis tests the given polynomial and its partial derivatives at
nonzero vectors. It implies primality and smoothness of relative dimension
one of the actual constructed curve; neither conclusion is an input.
In particular, smoothness of a reduced locus is not used to discard repeated
factors of a defining equation.

The given actual line sheaf and its square isomorphism are still geometric
inputs. Adjunction, the original discriminant double cover, and the real
conic-bundle conclusion are not proved by this module.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace MvPolynomial
open scoped EvenQuinticConic.SchemeScalars

namespace EvenQuinticConic

variable {K : Type} [Field K] [IsAlgClosed K]

/-- The explicit nonzero-vector Jacobian condition proves smoothness of the
actual quintic structure morphism; homogeneous primality is also derived. -/
theorem planeQuintic_structure_isSmooth_of_jacobian
    (F : PlanePolynomial K) (hF : F.IsHomogeneous 5) (hFdeg : F.totalDegree = 5)
    (hJac : ∀ v : Fin 3 → K, v ≠ 0 → eval v F = 0 →
      ∃ i : Fin 3, eval v (pderiv i F) ≠ 0) :
    IsSmoothOfRelativeDimension 1 (planeCurveStructure F) :=
  planeCurveStructure_isSmoothOfRelativeDimension_of_gradient F hF (by omega)
    (plane_principal_isPrime_of_jacobian F 5 hF (by omega) hJac)
    (projective_gradient_of_rational_jacobian F hJac)

/-- Every global section of an even line sheaf with the prescribed square
vanishes on the actual curve of a nonsingular quintic equation. The equation
supplies integrality, smoothness and normality; the actual local line data
supply all refined frames and perfect pairings. -/
theorem planeQuintic_even_theta_sections_eq_zero_of_jacobian
    (F : PlanePolynomial K) (hF : F.IsHomogeneous 5) (hFdeg : F.totalDegree = 5)
    (hJac : ∀ v : Fin 3 → K, v ≠ 0 → eval v F = 0 →
      ∃ i : Fin 3, eval v (pderiv i F) ≠ 0)
    (Θ : (PlaneCurveScheme F).Modules)
    {ι : Type} (U : ι → (PlaneCurveScheme F).Opens) (hU : iSup U = ⊤)
    (triv : ∀ i, Θ.over (U i) ≅
      SheafOfModules.unit ((PlaneCurveScheme F).ringCatSheaf.over (U i)))
    (squareIso :
      ((localTrivializationTransition U triv).mul
        (localTrivializationTransition U triv)).moduleSheaf ≅ PlaneCurveQuadraticSheaf F)
    (heven : Even (Module.finrank K (Θ.val.obj (op ⊤))))
    (s : Θ.val.obj (op ⊤)) : s = 0 := by
  letI := planeQuintic_structure_isSmooth_of_jacobian F hF hFdeg hJac
  exact planeQuintic_even_theta_sections_eq_zero_of_smooth F hF hFdeg
    (plane_principal_isPrime_of_jacobian F 5 hF (by omega) hJac)
    Θ U hU triv squareIso heven s

end EvenQuinticConic
