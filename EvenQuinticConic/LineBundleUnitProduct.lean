import EvenQuinticConic.LineBundleTensorUniversal

/-! # Cancelling an actually trivial factor in a cocycle product -/
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
open scoped TensorProduct
universe u
namespace EvenQuinticConic
variable {X : Scheme.{u}}

def moduleSheafUnitAction (M : X.Modules) :
    ModuleSheafPairing (SheafOfModules.unit X.ringCatSheaf) M M where
  app V := LinearMap.lsmul Γ(X, V) (M.val.obj (op V))
  naturality _V _W hWV r s := M.val.map_smul (homOfLE hWV).op r s

theorem moduleSheafUnitAction_lift (M : X.Modules) (V : X.Opens) :
    TensorProduct.lift ((moduleSheafUnitAction M).app V) =
      (TensorProduct.lid Γ(X, V) (M.val.obj (op V))).toLinearMap := by
  apply TensorProduct.ext'
  intro r s
  rfl

namespace UnitTransition
variable {ι : Type u} {U : ι → X.Opens} (g h : UnitTransition X U)

def productIsoOfPairing (hcover : iSup U = ⊤) {P : X.Modules}
    (μ : ModuleSheafPairing g.moduleSheaf h.moduleSheaf P)
    (hμ : ∀ i V (_hi : V ≤ U i), Function.Bijective (TensorProduct.lift (μ.app V))) :
    (g.mul h).moduleSheaf ≅ P :=
  glueModuleIso U hcover (g.pairingLocalHom h μ) (g.pairingLocalHom_compatible h μ)
    (fun i V hi ↦ (hμ i V hi).comp (g.multiplicationTensorEquiv h i V hi).symm.bijective)

def productIsoOfTrivialLeft (hcover : iSup U = ⊤)
    (e : g.moduleSheaf ≅ SheafOfModules.unit X.ringCatSheaf) :
    (g.mul h).moduleSheaf ≅ h.moduleSheaf :=
  g.productIsoOfPairing h hcover
    ((moduleSheafUnitAction h.moduleSheaf).precomposeIso e (Iso.refl _)) (by
      intro i V hi
      apply ModuleSheafPairing.precomposeIso_tensor_bijective
      rw [moduleSheafUnitAction_lift]
      exact (TensorProduct.lid Γ(X, V) (h.moduleSheaf.val.obj (op V))).bijective)

theorem productIsoOfTrivialLeft_hom_mul (hcover : iSup U = ⊤)
    (e : g.moduleSheaf ≅ SheafOfModules.unit X.ringCatSheaf)
    (V : X.Opens) (s : g.Section V) (t : h.Section V) :
    (g.productIsoOfTrivialLeft h hcover e).hom.val.app (op V) (s.mul t) =
      (show Γ(X, V) from e.hom.val.app (op V) s) • t :=
  g.pairingDesc_app_mul h hcover
    ((moduleSheafUnitAction h.moduleSheaf).precomposeIso e (Iso.refl _)) V s t

end UnitTransition
end EvenQuinticConic
