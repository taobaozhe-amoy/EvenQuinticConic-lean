import EvenQuinticConic.PlaneHyperplaneRestriction
import EvenQuinticConic.LineBundlePairing
import EvenQuinticConic.ThetaIneffectivity

/-!
# Theta ineffectivity on the constructed actual plane curve

The curve, its hyperplane sheaf, its three coordinate sections, the square
sheaf, the hyperplane multiplication pairing, and quartic injectivity are
constructed by earlier modules. None of these are free inputs below.

The remaining geometric inputs are explicit: a nonempty normal affine
refinement of the coordinate cover on which the given theta sheaf is framed,
an actual locally tensor-perfect theta square pairing, surjectivity of the
actual quadratic-section map, and evenness of the actual section dimension.
We do not assume that an arbitrary theta sheaf is trivial on each entire
standard coordinate chart. Nor do we claim that quadratic surjectivity or
the normal framed refinement has already been deduced from smoothness.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace MvPolynomial
open scoped EvenQuinticConic.SchemeScalars

namespace EvenQuinticConic

variable {K : Type} [Field K]

/-- The actual square of the constructed hyperplane cocycle sheaf. -/
def PlaneCurveQuadraticSheaf (F : PlanePolynomial K) : (PlaneCurveScheme F).Modules :=
  ((planeCurveHyperplaneTransition F).mul (planeCurveHyperplaneTransition F)).moduleSheaf

/-- The actual natural multiplication pairing of the hyperplane sheaf with
itself. Local tensor-perfectness follows from its constructed frames. -/
def planeCurveSquarePairing (F : PlanePolynomial K) :
    ModuleSheafPairing (PlaneCurveHyperplaneSheaf F) (PlaneCurveHyperplaneSheaf F)
      (PlaneCurveQuadraticSheaf F) :=
  UnitTransition.multiplicationPairing
    (planeCurveHyperplaneTransition F) (planeCurveHyperplaneTransition F)

/-- The actual chart frame on the constructed square sheaf. -/
def planeCurveQuadraticFrame (F : PlanePolynomial K) (i : Fin 3) :
    ModuleSheafFrame (PlaneCurveQuadraticSheaf F) (planeCurveCoordinateOpen F i) :=
  ((planeCurveHyperplaneTransition F).mul (planeCurveHyperplaneTransition F)).frame i

/-- The hyperplane square pairing is tensor-perfect on every subopen of a
coordinate chart; this is proved without a hypothesis on the pairing. -/
theorem planeCurveSquarePairing_tensor_bijective (F : PlanePolynomial K)
    (i : Fin 3) (V : (PlaneCurveScheme F).Opens)
    (hVi : V ≤ planeCurveCoordinateOpen F i) :
    Function.Bijective (TensorProduct.lift ((planeCurveSquarePairing F).app V)) :=
  UnitTransition.multiplicationPairing_tensor_bijective
    (planeCurveHyperplaneTransition F) (planeCurveHyperplaneTransition F) i V hVi

/-- Every actual theta section vanishes under the remaining geometric
lifting and local normality hypotheses. All hyperplane data and quartic
injectivity are supplied by the constructed plane quintic itself. -/
theorem planeQuintic_even_theta_sections_eq_zero [IsAlgClosed K]
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
    (h2 : Function.Surjective (quadraticSectionMap (K := K)
      (planeCurveSquarePairing F) (planeCurveCoordinateSection F)))
    (heven : Even (Module.finrank K (Θ.val.obj (op ⊤))))
    (s : Θ.val.obj (op ⊤)) : s = 0 := by
  letI := planeCurveScheme_isIntegral F 5 hF (by omega) hprime
  let hframes : ∀ i, ModuleSheafFrame (PlaneCurveHyperplaneSheaf F) (V i) :=
    fun i => (planeCurveHyperplaneFrame F (a i)).restrict (ha i)
  let tframes : ∀ i, ModuleSheafFrame (PlaneCurveQuadraticSheaf F) (V i) :=
    fun i => (planeCurveQuadraticFrame F (a i)).restrict (ha i)
  have hν : ∀ i, Function.Bijective
      (TensorProduct.lift ((planeCurveSquarePairing F).app (V i))) :=
    fun i => planeCurveSquarePairing_tensor_bijective F (a i) (V i) (ha i)
  have hpoint : genericPoint (PlaneCurveScheme F) ∈ iSup V := by
    rw [hcover]
    trivial
  obtain ⟨i₀, _⟩ := TopologicalSpace.Opens.mem_iSup.mp hpoint
  have h4 : ∀ P : PlanePolynomial K, P.IsHomogeneous 4 →
      aeval (fun k => schemeGenericLinearMap (K := K) (PlaneCurveHyperplaneSheaf F)
        (V i₀) (hframes i₀) (planeCurveCoordinateSection F k)) P = 0 → P = 0 :=
    planeQuintic_hyperplane_quartic_injective_on_subopen
      F hF hFdeg hprime (a i₀) (V i₀) (ha i₀)
  exact even_theta_ineffective_of_restriction_maps
    Θ (PlaneCurveHyperplaneSheaf F) (PlaneCurveQuadraticSheaf F)
    μ (planeCurveSquarePairing F) V hcover hV θframes hframes tframes hμ hν i₀
    (planeCurveCoordinateSection F) h2 h4 heven s

end EvenQuinticConic
