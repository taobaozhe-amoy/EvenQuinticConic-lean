import EvenQuinticConic.PlaneThetaLineBundle
import EvenQuinticConic.SmoothSchemeNormality
import EvenQuinticConic.LineBundleTensorUniversal

/-!
# Even theta vanishing on the actual smooth prime plane quintic

Smoothness of relative dimension one of the actual structural morphism
now supplies normality internally. Actual local unit-sheaf isomorphisms
supply descent and a common affine framed refinement; an actual square
isomorphism supplies the locally perfect pairing. The descended square
has the tensor universal property proved in `LineBundleTensorUniversal`.

This theorem still assumes homogeneous primality and the specified
line-sheaf/square data. It does not construct them from a conic bundle,
prove adjunction, or establish the original real topological statement.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace MvPolynomial
open scoped EvenQuinticConic.SchemeScalars

namespace EvenQuinticConic

variable {K : Type} [Field K] [IsAlgClosed K]

/-- On the actual smooth prime plane quintic, an actual locally trivial
line sheaf with the prescribed square and even section dimension has no
nonzero global sections. Normality and all refined local data are proved. -/
theorem planeQuintic_even_theta_sections_eq_zero_of_smooth
    (F : PlanePolynomial K) (hF : F.IsHomogeneous 5)
    (hFdeg : F.totalDegree = 5) (hprime : (Ideal.span {F}).IsPrime)
    [IsSmoothOfRelativeDimension 1 (planeCurveStructure F)]
    (Θ : (PlaneCurveScheme F).Modules)
    {ι : Type} (U : ι → (PlaneCurveScheme F).Opens) (hU : iSup U = ⊤)
    (triv : ∀ i, Θ.over (U i) ≅
      SheafOfModules.unit ((PlaneCurveScheme F).ringCatSheaf.over (U i)))
    (squareIso :
      ((localTrivializationTransition U triv).mul
        (localTrivializationTransition U triv)).moduleSheaf ≅ PlaneCurveQuadraticSheaf F)
    (heven : Even (Module.finrank K (Θ.val.obj (op ⊤))))
    (s : Θ.val.obj (op ⊤)) : s = 0 := by
  letI := planeCurveScheme_isIntegral F 5 hF (by omega) hprime
  exact planeQuintic_even_theta_sections_eq_zero_of_local_trivializations
    F hF hFdeg hprime
    (smoothCurve_stalks_isIntegrallyClosed K (PlaneCurveScheme F) (planeCurveStructure F))
    Θ U hU triv squareIso heven s

end EvenQuinticConic
