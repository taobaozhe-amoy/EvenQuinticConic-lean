import EvenQuinticConic.FrameCocycleDescent
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-! # Sections of the actual kernel of a module-sheaf morphism -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
namespace EvenQuinticConic
variable {X : Scheme.{u}} {M N : X.Modules} (τ : M ⟶ N)

local instance sectionCommRing (V : X.Opens) : CommRing (X.ringCatSheaf.val.obj (op V)) :=
  inferInstanceAs (CommRing Γ(X, V))

/-- Evaluation of the categorical sheaf kernel is the actual sectionwise kernel. -/
def moduleSheafKernelSectionEquiv (V : X.Opens) :
    (kernel τ).val.obj (op V) ≃ₗ[X.ringCatSheaf.val.obj (op V)]
      LinearMap.ker (τ.val.app (op V)).hom :=
  ((PreservesKernel.iso (SheafOfModules.evaluation X.ringCatSheaf (op V)) τ) ≪≫
    ModuleCat.kernelIsoKer (τ.val.app (op V))).toLinearEquiv

/-- This comparison identifies the inclusion with the actual kernel inclusion. -/
theorem moduleSheafKernelSectionEquiv_val (V : X.Opens)
    (s : (kernel τ).val.obj (op V)) :
    (moduleSheafKernelSectionEquiv τ V s).val = (kernel.ι τ).val.app (op V) s := by
  have h :
      ((PreservesKernel.iso (SheafOfModules.evaluation X.ringCatSheaf (op V)) τ) ≪≫
        ModuleCat.kernelIsoKer (τ.val.app (op V))).hom ≫
          ModuleCat.ofHom (LinearMap.ker (τ.val.app (op V)).hom).subtype =
      (SheafOfModules.evaluation X.ringCatSheaf (op V)).map (kernel.ι τ) := by
    simp only [Iso.trans_hom, Category.assoc,
      ModuleCat.kernelIsoKer_hom_ker_subtype, PreservesKernel.iso_hom]
    exact kernelComparison_comp_ι τ _
  exact congrArg (fun f => f s) h

/-- The sectionwise kernel inclusions commute with actual restrictions. -/
theorem moduleSheafKernelSectionEquiv_restrict (V W : X.Opens) (hWV : W ≤ V)
    (s : (kernel τ).val.obj (op V)) :
    (moduleSheafKernelSectionEquiv τ W (moduleRestrict (kernel τ) hWV s)).val =
      moduleRestrict M hWV (moduleSheafKernelSectionEquiv τ V s).val := by
  rw [moduleSheafKernelSectionEquiv_val, moduleSheafKernelSectionEquiv_val]
  exact (PresheafOfModules.naturality_apply (kernel.ι τ).val (homOfLE hWV).op s)

end EvenQuinticConic
