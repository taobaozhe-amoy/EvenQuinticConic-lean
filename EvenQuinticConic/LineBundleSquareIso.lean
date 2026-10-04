import EvenQuinticConic.LineBundlePairing

/-!
# Square pairings induced by actual sheaf isomorphisms

An isomorphism from the sheaf descended from the square cocycle to another
module sheaf induces a natural square pairing. Its tensor lift is an
isomorphism on every subopen of a trivializing chart, as a consequence of
the actual sheaf isomorphism and the constructed multiplication pairing.
No assertion about the tensor product of global sections is needed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open scoped TensorProduct

universe u

namespace EvenQuinticConic

variable {X : Scheme.{u}}

/-- An actual module-sheaf isomorphism evaluates to a linear equivalence
on every open, over the actual ring of regular sections there. -/
def moduleSheafIsoSectionEquiv {M N : X.Modules} (e : M ≅ N) (V : X.Opens) :
    M.val.obj (op V) ≃ₗ[Γ(X,V)] N.val.obj (op V) :=
  ((SheafOfModules.evaluation _ (op V)).mapIso e).toLinearEquiv

@[simp]
theorem moduleSheafIsoSectionEquiv_apply {M N : X.Modules} (e : M ≅ N)
    (V : X.Opens) (s : M.val.obj (op V)) :
    moduleSheafIsoSectionEquiv e V s = e.hom.val.app (op V) s := rfl

namespace ModuleSheafPairing

variable {M N P Q : X.Modules}

/-- Postcomposition of a natural pairing with an actual module-sheaf
morphism preserves naturality. -/
def postcompose (μ : ModuleSheafPairing M N P) (f : P ⟶ Q) :
    ModuleSheafPairing M N Q where
  app V := (μ.app V).compr₂ (f.val.app (op V)).hom
  naturality V W hWV s t := by
    change Q.val.map (homOfLE hWV).op (f.val.app (op V) (μ.app V s t)) =
      f.val.app (op W) (μ.app W
        (M.val.map (homOfLE hWV).op s) (N.val.map (homOfLE hWV).op t))
    rw [← PresheafOfModules.naturality_apply, μ.naturality]

@[simp]
theorem postcompose_app (μ : ModuleSheafPairing M N P) (f : P ⟶ Q)
    (V : X.Opens) (s : M.val.obj (op V)) (t : N.val.obj (op V)) :
    (μ.postcompose f).app V s t = f.val.app (op V) (μ.app V s t) := rfl

/-- The induced tensor map is the composite of the original tensor map
and the actual section map of the sheaf morphism. -/
theorem lift_postcompose (μ : ModuleSheafPairing M N P) (f : P ⟶ Q)
    (V : X.Opens) :
    TensorProduct.lift ((μ.postcompose f).app V) =
      (f.val.app (op V)).hom.comp (TensorProduct.lift (μ.app V)) := by
  apply TensorProduct.ext'
  intro s t
  rfl

/-- Postcomposition of a natural pairing with an actual sheaf isomorphism. -/
def postcomposeIso (μ : ModuleSheafPairing M N P) (e : P ≅ Q) :
    ModuleSheafPairing M N Q := μ.postcompose e.hom

@[simp]
theorem postcomposeIso_app (μ : ModuleSheafPairing M N P) (e : P ≅ Q)
    (V : X.Opens) (s : M.val.obj (op V)) (t : N.val.obj (op V)) :
    (μ.postcomposeIso e).app V s t = e.hom.val.app (op V) (μ.app V s t) := rfl

/-- A sheaf isomorphism preserves tensor-perfectness on any open where
it already holds; the bijectivity of the section map is derived from it. -/
theorem postcomposeIso_tensor_bijective (μ : ModuleSheafPairing M N P)
    (e : P ≅ Q) (V : X.Opens)
    (hμ : Function.Bijective (TensorProduct.lift (μ.app V))) :
    Function.Bijective (TensorProduct.lift ((μ.postcomposeIso e).app V)) := by
  rw [postcomposeIso, lift_postcompose]
  exact (moduleSheafIsoSectionEquiv e V).bijective.comp hμ


variable {M' N' : X.Modules}

/-- Transport both inputs of an actual sheaf pairing through actual sheaf
morphisms. Naturality follows from the morphisms' naturality. -/
def precompose (μ : ModuleSheafPairing M N P) (f : M' ⟶ M) (g : N' ⟶ N) :
    ModuleSheafPairing M' N' P where
  app V := (μ.app V).compl₁₂ (f.val.app (op V)).hom (g.val.app (op V)).hom
  naturality V W hWV s t := by
    change P.val.map (homOfLE hWV).op
      (μ.app V (f.val.app (op V) s) (g.val.app (op V) t)) =
      μ.app W (f.val.app (op W) (M'.val.map (homOfLE hWV).op s))
        (g.val.app (op W) (N'.val.map (homOfLE hWV).op t))
    rw [μ.naturality, PresheafOfModules.naturality_apply,
      PresheafOfModules.naturality_apply]

@[simp]
theorem precompose_app (μ : ModuleSheafPairing M N P) (f : M' ⟶ M) (g : N' ⟶ N)
    (V : X.Opens) (s : M'.val.obj (op V)) (t : N'.val.obj (op V)) :
    (μ.precompose f g).app V s t =
      μ.app V (f.val.app (op V) s) (g.val.app (op V) t) := rfl

/-- Transport the input sheaves of a pairing along actual sheaf isomorphisms. -/
def precomposeIso (μ : ModuleSheafPairing M N P) (e : M' ≅ M) (f : N' ≅ N) :
    ModuleSheafPairing M' N' P := μ.precompose e.hom f.hom

@[simp]
theorem precomposeIso_app (μ : ModuleSheafPairing M N P) (e : M' ≅ M) (f : N' ≅ N)
    (V : X.Opens) (s : M'.val.obj (op V)) (t : N'.val.obj (op V)) :
    (μ.precomposeIso e f).app V s t =
      μ.app V (e.hom.val.app (op V) s) (f.hom.val.app (op V) t) := rfl

/-- Transporting input sheaves transports the local tensor map by the tensor
product of the actual evaluated linear equivalences. -/
theorem lift_precomposeIso (μ : ModuleSheafPairing M N P) (e : M' ≅ M) (f : N' ≅ N)
    (V : X.Opens) :
    TensorProduct.lift ((μ.precomposeIso e f).app V) =
      (TensorProduct.lift (μ.app V)).comp
        (TensorProduct.congr (moduleSheafIsoSectionEquiv e V)
          (moduleSheafIsoSectionEquiv f V)).toLinearMap := by
  apply TensorProduct.ext'
  intro s t
  simp only [TensorProduct.lift.tmul, precomposeIso_app, LinearMap.comp_apply,
    LinearEquiv.coe_coe, TensorProduct.congr_tmul, moduleSheafIsoSectionEquiv_apply]

/-- Tensor-perfectness is preserved under actual isomorphisms of the input
sheaves. -/
theorem precomposeIso_tensor_bijective (μ : ModuleSheafPairing M N P)
    (e : M' ≅ M) (f : N' ≅ N) (V : X.Opens)
    (hμ : Function.Bijective (TensorProduct.lift (μ.app V))) :
    Function.Bijective (TensorProduct.lift ((μ.precomposeIso e f).app V)) := by
  rw [lift_precomposeIso]
  exact hμ.comp (TensorProduct.congr (moduleSheafIsoSectionEquiv e V)
    (moduleSheafIsoSectionEquiv f V)).bijective

end ModuleSheafPairing

namespace UnitTransition

variable {ι : Type u} {U : ι → X.Opens}

/-- An actual isomorphism from the square-cocycle sheaf supplies the square
pairing of the descended line sheaf. -/
def squarePairingOfIso (g : UnitTransition X U) {P : X.Modules}
    (e : (g.mul g).moduleSheaf ≅ P) :
    ModuleSheafPairing g.moduleSheaf g.moduleSheaf P :=
  (g.multiplicationPairing g).postcomposeIso e

@[simp]
theorem squarePairingOfIso_app (g : UnitTransition X U) {P : X.Modules}
    (e : (g.mul g).moduleSheaf ≅ P) (V : X.Opens)
    (s t : g.Section V) :
    (g.squarePairingOfIso e).app V s t = e.hom.val.app (op V) (s.mul t) := rfl

/-- Tensor-perfectness follows from the actual square isomorphism on every
subopen of every cocycle chart; it is not supplied as a separate hypothesis. -/
theorem squarePairingOfIso_tensor_bijective (g : UnitTransition X U) {P : X.Modules}
    (e : (g.mul g).moduleSheaf ≅ P) (i : ι) (V : X.Opens) (hVi : V ≤ U i) :
    Function.Bijective (TensorProduct.lift ((g.squarePairingOfIso e).app V)) :=
  (g.multiplicationPairing g).postcomposeIso_tensor_bijective e V
    (g.multiplicationPairing_tensor_bijective g i V hVi)

end UnitTransition

end EvenQuinticConic
