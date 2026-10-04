import EvenQuinticConic.LineBundleSquareIso
import EvenQuinticConic.ModuleHomGluing

/-!
# The universal property of the actual product-cocycle sheaf

For two actual line sheaves descended on a common open cover, the product
cocycle represents natural bilinear pairings into any module sheaf. The
factorization is constructed from local tensor maps and the actual sheaf
axiom; tensor products of global sections are not assumed to be sheaves.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open scoped TensorProduct

universe u

namespace EvenQuinticConic.UnitTransition

variable {X : Scheme.{u}} {ι : Type u} {U : ι → X.Opens}
variable (g h : UnitTransition X U) {P : X.Modules}

/-- On a trivializing chart, every section of the product sheaf is one
literal product of sections of the two factors. -/
theorem exists_mul_on_chart (i : ι) (V : X.Opens) (hVi : V ≤ U i)
    (z : (g.mul h).Section V) :
    ∃ s : g.Section V, ∃ t : h.Section V, s.mul t = z := by
  refine ⟨(g.coordinateEquiv i V hVi).symm 1,
    (h.coordinateEquiv i V hVi).symm ((g.mul h).coordinateEquiv i V hVi z), ?_⟩
  apply ((g.mul h).coordinateEquiv i V hVi).injective
  change g.coordinateEquiv i V hVi ((g.coordinateEquiv i V hVi).symm 1) *
    h.coordinateEquiv i V hVi
      ((h.coordinateEquiv i V hVi).symm ((g.mul h).coordinateEquiv i V hVi z)) = _
  simp only [LinearEquiv.apply_symm_apply, one_mul]

/-- The linear factorization of a pairing over one chart subopen. -/
def pairingLocalLinearMap (μ : ModuleSheafPairing g.moduleSheaf h.moduleSheaf P)
    (i : ι) (V : X.Opens) (hVi : V ≤ U i) :
    (g.mul h).Section V →ₗ[Γ(X,V)] P.val.obj (op V) :=
  (TensorProduct.lift (μ.app V)).comp (g.multiplicationTensorEquiv h i V hVi).symm.toLinearMap

/-- The local factorization recovers the original pairing on every pair
of sections, independently of how chart generators are chosen. -/
theorem pairingLocalLinearMap_mul
    (μ : ModuleSheafPairing g.moduleSheaf h.moduleSheaf P)
    (i : ι) (V : X.Opens) (hVi : V ≤ U i) (s : g.Section V) (t : h.Section V) :
    g.pairingLocalLinearMap h μ i V hVi (s.mul t) = μ.app V s t := by
  rw [← g.multiplicationTensorEquiv_tmul h i V hVi s t]
  change TensorProduct.lift (μ.app V)
    ((g.multiplicationTensorEquiv h i V hVi).symm
      ((g.multiplicationTensorEquiv h i V hVi) (s ⊗ₜ[Γ(X,V)] t))) = _
  rw [LinearEquiv.symm_apply_apply, TensorProduct.lift.tmul]

/-- The local factorization commutes with actual section restrictions. -/
def pairingLocalHom (μ : ModuleSheafPairing g.moduleSheaf h.moduleSheaf P)
    (i : ι) : LocalModuleHom (g.mul h).moduleSheaf P (U i) where
  app V hVi := g.pairingLocalLinearMap h μ i V hVi
  naturality V W hVi hWi hWV z := by
    obtain ⟨s, t, rfl⟩ := g.exists_mul_on_chart h i V hVi z
    change g.pairingLocalLinearMap h μ i W hWi ((s.mul t).restrict hWV) =
      P.val.map (homOfLE hWV).op (g.pairingLocalLinearMap h μ i V hVi (s.mul t))
    rw [Section.restrict_mul, pairingLocalLinearMap_mul, pairingLocalLinearMap_mul]
    exact (μ.naturality V W hWV s t).symm

/-- Local factorizations agree on overlaps because they agree on all
products, and every local section is such a product. -/
theorem pairingLocalHom_compatible
    (μ : ModuleSheafPairing g.moduleSheaf h.moduleSheaf P)
    (i j : ι) (V : X.Opens) (hi : V ≤ U i) (hj : V ≤ U j) :
    (g.pairingLocalHom h μ i).app V hi = (g.pairingLocalHom h μ j).app V hj := by
  apply LinearMap.ext
  intro z
  obtain ⟨s, t, rfl⟩ := g.exists_mul_on_chart h i V hi z
  exact (g.pairingLocalLinearMap_mul h μ i V hi s t).trans
    (g.pairingLocalLinearMap_mul h μ j V hj s t).symm

/-- The actual global sheaf morphism factoring a natural bilinear pairing. -/
def pairingDesc (hcover : iSup U = ⊤)
    (μ : ModuleSheafPairing g.moduleSheaf h.moduleSheaf P) :
    (g.mul h).moduleSheaf ⟶ P :=
  glueModuleHom U hcover (g.pairingLocalHom h μ) (g.pairingLocalHom_compatible h μ)

/-- The descended morphism agrees with the local tensor factorization. -/
theorem pairingDesc_app_on_chart (hcover : iSup U = ⊤)
    (μ : ModuleSheafPairing g.moduleSheaf h.moduleSheaf P)
    (i : ι) (V : X.Opens) (hVi : V ≤ U i) (z : (g.mul h).Section V) :
    (g.pairingDesc h hcover μ).val.app (op V) z =
      g.pairingLocalLinearMap h μ i V hVi z :=
  glueModuleHom_app U hcover (g.pairingLocalHom h μ)
    (g.pairingLocalHom_compatible h μ) i V hVi z

/-- The factorization recovers the original pairing on every open, by
actual sheaf separation on the intersections with the chart cover. -/
theorem pairingDesc_app_mul (hcover : iSup U = ⊤)
    (μ : ModuleSheafPairing g.moduleSheaf h.moduleSheaf P)
    (V : X.Opens) (s : g.Section V) (t : h.Section V) :
    (g.pairingDesc h hcover μ).val.app (op V) (s.mul t) = μ.app V s t := by
  apply module_eq_of_cover_restrictions U hcover V
  intro i
  change P.val.map (homOfLE (show V ⊓ U i ≤ V from inf_le_left)).op
      ((g.pairingDesc h hcover μ).val.app (op V) (s.mul t)) =
    P.val.map (homOfLE (show V ⊓ U i ≤ V from inf_le_left)).op (μ.app V s t)
  rw [← PresheafOfModules.naturality_apply, μ.naturality]
  change (g.pairingDesc h hcover μ).val.app (op (V ⊓ U i))
    ((s.mul t).restrict inf_le_left) = μ.app (V ⊓ U i)
      (s.restrict inf_le_left) (t.restrict inf_le_left)
  rw [Section.restrict_mul, pairingDesc_app_on_chart g h hcover μ i _ inf_le_right,
    pairingLocalLinearMap_mul]

/-- A morphism from the product sheaf is determined by its values on
literal products; equality is first checked on charts and then glued. -/
theorem product_hom_ext (hcover : iSup U = ⊤)
    (f k : (g.mul h).moduleSheaf ⟶ P)
    (hfk : ∀ (V : X.Opens) (s : g.Section V) (t : h.Section V),
      f.val.app (op V) (s.mul t) = k.val.app (op V) (s.mul t)) : f = k := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  ext z
  apply module_eq_of_cover_restrictions U hcover V.unop
  intro i
  change P.val.map (homOfLE (show V.unop ⊓ U i ≤ V.unop from inf_le_left)).op
      (f.val.app V z) =
    P.val.map (homOfLE (show V.unop ⊓ U i ≤ V.unop from inf_le_left)).op (k.val.app V z)
  rw [← PresheafOfModules.naturality_apply, ← PresheafOfModules.naturality_apply]
  obtain ⟨s, t, hst⟩ := g.exists_mul_on_chart h i (V.unop ⊓ U i) inf_le_right
    ((g.mul h).moduleSheaf.val.map
      (homOfLE (show V.unop ⊓ U i ≤ V.unop from inf_le_left)).op z)
  rw [← hst]
  exact hfk _ s t

/-- The product-cocycle sheaf represents actual natural bilinear pairings.
This is the sheaf-level tensor universal property, proved by local tensor
factorization and gluing. -/
def productHomEquiv (hcover : iSup U = ⊤) :
    ((g.mul h).moduleSheaf ⟶ P) ≃ ModuleSheafPairing g.moduleSheaf h.moduleSheaf P where
  toFun f := (g.multiplicationPairing h).postcompose f
  invFun := g.pairingDesc h hcover
  left_inv f := by
    apply g.product_hom_ext h hcover
    intro V s t
    exact g.pairingDesc_app_mul h hcover ((g.multiplicationPairing h).postcompose f) V s t
  right_inv μ := by
    cases μ with
    | mk app naturality =>
      dsimp only [ModuleSheafPairing.postcompose]
      congr 1
      funext V
      apply LinearMap.ext
      intro s
      apply LinearMap.ext
      intro t
      exact g.pairingDesc_app_mul h hcover ⟨app, naturality⟩ V s t

@[simp]
theorem productHomEquiv_apply (hcover : iSup U = ⊤)
    (f : (g.mul h).moduleSheaf ⟶ P) :
    g.productHomEquiv h hcover f = (g.multiplicationPairing h).postcompose f := rfl

@[simp]
theorem productHomEquiv_symm_apply (hcover : iSup U = ⊤)
    (μ : ModuleSheafPairing g.moduleSheaf h.moduleSheaf P) :
    (g.productHomEquiv h hcover).symm μ = g.pairingDesc h hcover μ := rfl


/-- Transporting the tensor universal property along actual isomorphisms
of the input sheaves shows that the product also represents pairings on
the original, arbitrarily presented line sheaves. -/
def productHomEquivOfIso (hcover : iSup U = ⊤)
    {M N : X.Modules} (e : M ≅ g.moduleSheaf) (f : N ≅ h.moduleSheaf) :
    ((g.mul h).moduleSheaf ⟶ P) ≃ ModuleSheafPairing M N P :=
  (g.productHomEquiv h hcover).trans
    { toFun := fun μ ↦ μ.precomposeIso e f
      invFun := fun μ ↦ μ.precomposeIso e.symm f.symm
      left_inv := by
        intro μ
        cases μ with
        | mk app naturality =>
          dsimp only [ModuleSheafPairing.precomposeIso, ModuleSheafPairing.precompose]
          congr 1
          funext V
          apply LinearMap.ext
          intro s
          apply LinearMap.ext
          intro t
          change app V
            ((moduleSheafIsoSectionEquiv e V) ((moduleSheafIsoSectionEquiv e V).symm s))
            ((moduleSheafIsoSectionEquiv f V) ((moduleSheafIsoSectionEquiv f V).symm t)) =
            app V s t
          rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
      right_inv := by
        intro μ
        cases μ with
        | mk app naturality =>
          dsimp only [ModuleSheafPairing.precomposeIso, ModuleSheafPairing.precompose]
          congr 1
          funext V
          apply LinearMap.ext
          intro s
          apply LinearMap.ext
          intro t
          change app V
            ((moduleSheafIsoSectionEquiv e V).symm ((moduleSheafIsoSectionEquiv e V) s))
            ((moduleSheafIsoSectionEquiv f V).symm ((moduleSheafIsoSectionEquiv f V) t)) =
            app V s t
          rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply] }

@[simp]
theorem productHomEquivOfIso_apply (hcover : iSup U = ⊤)
    {M N : X.Modules} (e : M ≅ g.moduleSheaf) (f : N ≅ h.moduleSheaf)
    (k : (g.mul h).moduleSheaf ⟶ P) :
    g.productHomEquivOfIso h hcover e f k =
      ((g.multiplicationPairing h).postcompose k).precomposeIso e f := rfl

@[simp]
theorem productHomEquivOfIso_symm_apply (hcover : iSup U = ⊤)
    {M N : X.Modules} (e : M ≅ g.moduleSheaf) (f : N ≅ h.moduleSheaf)
    (μ : ModuleSheafPairing M N P) :
    (g.productHomEquivOfIso h hcover e f).symm μ =
      g.pairingDesc h hcover (μ.precomposeIso e.symm f.symm) := rfl

end EvenQuinticConic.UnitTransition
