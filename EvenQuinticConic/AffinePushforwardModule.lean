import EvenQuinticConic.AffinePushforwardTensor
import EvenQuinticConic.ModuleHomGluing
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.Topology.Sheaves.Functors

/-!
# Actual pushforward module sheaves for affine spectral maps

The module sheaf below is mathlib's pushforward of the source structure
sheaf along the given scheme morphism. Its sections, restrictions, and
scalar action are identified definitionally with the genuine section
rings used in the tensor comparison. No chart or freeness is an input.
-/

noncomputable section
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u
namespace EvenQuinticConic

variable {X Y : Scheme.{u}}

/-- The sheaf-of-rings morphism underlying a scheme morphism, with scalars
forgotten from commutative rings to rings. -/
def schemePushforwardRingMap (f : X ⟶ Y) : Y.ringCatSheaf ⟶
    ((Opens.map f.base).sheafPushforwardContinuous RingCat
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).obj X.ringCatSheaf :=
  ⟨Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)⟩

/-- The actual pushforward functor on scheme module sheaves. -/
def schemeModulePushforward (f : X ⟶ Y) : X.Modules ⥤ Y.Modules :=
  SheafOfModules.pushforward (schemePushforwardRingMap f)

/-- Sections of the pushed-forward structure sheaf, including the actual
scalar restriction along the scheme's structure-sheaf morphism. -/
theorem schemeModulePushforward_unit_sections (f : X ⟶ Y) (V : Y.Opens) :
    ((schemeModulePushforward f).obj (SheafOfModules.unit X.ringCatSheaf)).val.obj (op V) =
      (ModuleCat.restrictScalars (f.app V).hom).obj
        (ModuleCat.of Γ(X, f ⁻¹ᵁ V) Γ(X, f ⁻¹ᵁ V)) := rfl

/-- Restrictions in the pushed-forward unit are the actual source restrictions. -/
theorem schemeModulePushforward_unit_restrict (f : X ⟶ Y)
    (V W : Y.Opens) (hWV : W ≤ V)
    (s : ((schemeModulePushforward f).obj (SheafOfModules.unit X.ringCatSheaf)).val.obj (op V)) :
    moduleRestrict ((schemeModulePushforward f).obj (SheafOfModules.unit X.ringCatSheaf)) hWV s =
      X.presheaf.map ((Opens.map f.base).map (homOfLE hWV)).op s := rfl

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

/-- The actual `π_* O_Spec(A)` as a module sheaf on `Spec(R)`. -/
def affinePushforwardModule : (Spec (CommRingCat.of R)).Modules :=
  (schemeModulePushforward (Spec.map (CommRingCat.ofHom (algebraMap R A)))).obj
    (SheafOfModules.unit (Spec (CommRingCat.of A)).ringCatSheaf)

/-- The affine module's section type is the genuine section ring on the preimage. -/
theorem affinePushforwardModule_sections (V : Opens (PrimeSpectrum.Top R)) :
    ((affinePushforwardModule (R := R) (A := A)).val.obj (op V) : Type u) =
      ((Spec.structureSheaf A).val.obj (op (affinePushforwardOpen (A := A) V)) : Type u) := rfl

/-- Scalars act through the actual structure-sheaf pullback, followed by multiplication. -/
theorem affinePushforwardModule_smul (V : Opens (PrimeSpectrum.Top R))
    (s : (Spec.structureSheaf R).val.obj (op V))
    (x : (affinePushforwardModule (R := R) (A := A)).val.obj (op V)) :
    s • x = affinePushforwardCoefficientMap (A := A) V s *
      (show (Spec.structureSheaf A).val.obj (op (affinePushforwardOpen (A := A) V)) from x) := rfl

/-- The affine module's restriction is the actual pushforward section restriction. -/
theorem affinePushforwardModule_restrict (V W : Opens (PrimeSpectrum.Top R)) (hWV : W ≤ V)
    (x : (affinePushforwardModule (R := R) (A := A)).val.obj (op V)) :
    moduleRestrict (affinePushforwardModule (R := R) (A := A)) hWV x =
      affinePushforwardSectionRestriction (A := A) V W hWV x := rfl

/-- The canonical tensor comparison is linear for the actual pushforward module action. -/
def affinePushforwardTensorLinearMap (V : Opens (PrimeSpectrum.Top R)) :
    ((Spec.structureSheaf R).val.obj (op V) ⊗[R] A) →ₗ[(Spec.structureSheaf R).val.obj (op V)]
      (affinePushforwardModule (R := R) (A := A)).val.obj (op V) where
  toFun := affinePushforwardTensorMap (A := A) V
  map_add' := map_add _
  map_smul' s x := by
    change affinePushforwardTensorMap (A := A) V (s • x) =
      affinePushforwardCoefficientMap (A := A) V s * affinePushforwardTensorMap (A := A) V x
    rw [Algebra.smul_def, map_mul]
    congr 1
    change affinePushforwardTensorMap (A := A) V (s ⊗ₜ[R] (1 : A)) = _
    simp

/-- The linear comparison has exactly the canonical ring-map underlying function. -/
@[simp] theorem affinePushforwardTensorLinearMap_apply (V : Opens (PrimeSpectrum.Top R))
    (x : (Spec.structureSheaf R).val.obj (op V) ⊗[R] A) :
    affinePushforwardTensorLinearMap (A := A) V x = affinePushforwardTensorMap (A := A) V x := rfl

/-- The linear comparison respects actual module-sheaf restrictions. -/
theorem affinePushforwardTensorLinearMap_restrict
    (V W : Opens (PrimeSpectrum.Top R)) (hWV : W ≤ V)
    (x : (Spec.structureSheaf R).val.obj (op V) ⊗[R] A) :
    moduleRestrict (affinePushforwardModule (R := R) (A := A)) hWV
      (affinePushforwardTensorLinearMap (A := A) V x) =
    affinePushforwardTensorLinearMap (A := A) W
      (principalOpenKummerSectionRestriction V W hWV x) :=
  affinePushforwardTensorMap_restrict V W hWV x

end EvenQuinticConic
