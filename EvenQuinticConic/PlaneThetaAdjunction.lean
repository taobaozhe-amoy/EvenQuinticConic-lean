import EvenQuinticConic.PlaneCurveAdjunction
import EvenQuinticConic.PlaneThetaJacobian

/-!
# Even theta vanishing with the actual differential sheaf as its square

The geometric square target is now the genuine relative differential sheaf.
The proved plane-quintic adjunction isomorphism supplies the hyperplane-square
comparison internally. The specified line sheaf, its actual local
trivializations, its square isomorphism and parity remain explicit inputs;
the original real discriminant cover is not constructed here.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace MvPolynomial
open scoped EvenQuinticConic.SchemeScalars

namespace EvenQuinticConic
variable {K : Type} [Field K] [IsAlgClosed K]

/-- Every section of an even line sheaf whose actual square is the actual
differential sheaf vanishes on a nonsingular plane quintic. Adjunction,
primality, smoothness, normality and finite-dimensionality are proved
internally; none is supplied as an additional hypothesis. -/
theorem planeQuintic_even_theta_sections_eq_zero_of_cotangent_square
    (F : PlanePolynomial K) (hF : F.IsHomogeneous 5) (hFdeg : F.totalDegree = 5)
    (hJac : ∀ v : Fin 3 → K, v ≠ 0 → eval v F = 0 →
      ∃ i : Fin 3, eval v (pderiv i F) ≠ 0)
    (Θ : (PlaneCurveScheme F).Modules)
    {ι : Type} (U : ι → (PlaneCurveScheme F).Opens) (hU : iSup U = ⊤)
    (triv : ∀ i, Θ.over (U i) ≅
      SheafOfModules.unit ((PlaneCurveScheme F).ringCatSheaf.over (U i)))
    (squareIso :
      ((localTrivializationTransition U triv).mul
        (localTrivializationTransition U triv)).moduleSheaf ≅
          schemeKaehlerSheaf (planeCurveStructure F))
    (heven : Even (Module.finrank K (Θ.val.obj (op ⊤))))
    (s : Θ.val.obj (op ⊤)) : s = 0 :=
  planeQuintic_even_theta_sections_eq_zero_of_jacobian F hF hFdeg hJac
    Θ U hU triv (squareIso ≪≫ planeQuinticAdjunctionIsoOfJacobian F hF hFdeg hJac)
    heven s

end EvenQuinticConic
