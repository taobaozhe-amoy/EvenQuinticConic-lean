import EvenQuinticConic.PlaneQuadraticSurjectivity

/-!
# Theta vanishing with both plane restriction theorems proved

The actual quadratic-section map is now proved surjective and the actual
quartic restriction proved injective. Neither is an assumption of the
theorem below. The normal affine theta frames and the actual perfect theta
square pairing still remain geometric inputs. This file does not construct
theta from a conic-bundle discriminant cover or prove the original real
conic-bundle obstruction.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace MvPolynomial
open scoped EvenQuinticConic.SchemeScalars

namespace EvenQuinticConic

variable {K : Type} [Field K] [IsAlgClosed K]

/-- On the actual prime plane quintic, an even-dimensional theta section
space has no nonzero section, given the actual theta square pairing and a
normal affine framed refinement. Quadratic surjectivity, quartic injectivity,
the hyperplane section dimension, and theta finite-dimensionality are all
proved internally. -/
theorem planeQuintic_even_theta_sections_eq_zero_of_normal_frames
    (F : PlanePolynomial K) (hF : F.IsHomogeneous 5)
    (hFdeg : F.totalDegree = 5) (hprime : (Ideal.span {F}).IsPrime)
    (Θ : (PlaneCurveScheme F).Modules)
    (μ : ModuleSheafPairing Θ Θ (PlaneCurveQuadraticSheaf F))
    {ι : Type*} (V : ι → (PlaneCurveScheme F).Opens) [∀ i, Nonempty (V i)]
    (hcover : iSup V = ⊤) (hV : ∀ i, IsAffineOpen (V i))
    [∀ i, IsIntegrallyClosed Γ(PlaneCurveScheme F, V i)]
    (a : ι → Fin 3) (ha : ∀ i, V i ≤ planeCurveCoordinateOpen F (a i))
    (θframes : ∀ i, ModuleSheafFrame Θ (V i))
    (hμ : ∀ i, Function.Bijective (TensorProduct.lift (μ.app (V i))))
    (heven : Even (Module.finrank K (Θ.val.obj (op ⊤))))
    (s : Θ.val.obj (op ⊤)) : s = 0 := by
  exact planeQuintic_even_theta_sections_eq_zero F hF hFdeg hprime Θ μ
    V hcover hV a ha θframes hμ
    (planeCurve_quadraticSectionMap_surjective F 5 hF (by omega) hprime) heven s

end EvenQuinticConic
