import EvenQuinticConic.SheafTrivialization

/-!
# Gluing actual morphisms of module sheaves

Natural local linear maps agreeing on overlaps determine a genuine global
module-sheaf morphism. The construction uses the actual sheaf condition.
-/

open CategoryTheory Opposite TopologicalSpace

universe u

namespace EvenQuinticConic

variable {X : TopCat.{u}} {R : TopCat.Sheaf RingCat.{u} X}

/-- Restriction of a section of an actual module sheaf. -/
abbrev moduleRestrict (M : SheafOfModules.{u} R) {V W : Opens X} (h : W ≤ V)
    (s : M.val.obj (op V)) : M.val.obj (op W) :=
  M.val.map (homOfLE h).op s

theorem moduleRestrict_comp (M : SheafOfModules.{u} R)
    {U V W : Opens X} (hVU : V ≤ U) (hWV : W ≤ V) (s : M.val.obj (op U)) :
    moduleRestrict M hWV (moduleRestrict M hVU s) =
      moduleRestrict M (hWV.trans hVU) s := by
  change M.val.presheaf.map (homOfLE hWV).op
    (M.val.presheaf.map (homOfLE hVU).op s) = _
  rw [← ConcreteCategory.comp_apply, ← M.val.presheaf.map_comp]
  rfl

/-- Actual linear maps on all subopens of one open, with their naturality. -/
structure LocalModuleHom (M N : SheafOfModules.{u} R) (U : Opens X) where
  app : ∀ V : Opens X, V ≤ U → M.val.obj (op V) →ₗ[R.val.obj (op V)] N.val.obj (op V)
  naturality : ∀ (V W : Opens X) (hV : V ≤ U) (hW : W ≤ U) (hWV : W ≤ V)
    (s : M.val.obj (op V)),
    app W hW (moduleRestrict M hWV s) = moduleRestrict N hWV (app V hV s)

variable {M N : SheafOfModules.{u} R} {ι : Type*}
  (U : ι → Opens X) (hcover : iSup U = ⊤)
  (f : ∀ i, LocalModuleHom M N (U i))
  (hcompat : ∀ i j V (hi : V ≤ U i) (hj : V ≤ U j), (f i).app V hi = (f j).app V hj)

include hcover hcompat

/-- The images of a section under the local morphisms glue uniquely. -/
theorem existsUnique_glued_module_image (V : Opens X) (s : M.val.obj (op V)) :
    ∃! t : N.val.obj (op V), ∀ i,
      moduleRestrict N (inf_le_left : V ⊓ U i ≤ V) t =
        (f i).app (V ⊓ U i) inf_le_right
          (moduleRestrict M (inf_le_left : V ⊓ U i ≤ V) s) := by
  let G : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨N.val.presheaf, N.isSheaf⟩
  let W : ι → Opens X := fun i ↦ V ⊓ U i
  apply G.existsUnique_gluing' W V (fun _ ↦ homOfLE inf_le_left)
    (by simp only [W, ← inf_iSup_eq, hcover, inf_top_eq, le_refl])
  intro i j
  change moduleRestrict N inf_le_left ((f i).app (W i) inf_le_right
      (moduleRestrict M inf_le_left s)) =
    moduleRestrict N inf_le_right ((f j).app (W j) inf_le_right
      (moduleRestrict M inf_le_left s))
  rw [← (f i).naturality (W i) (W i ⊓ W j) inf_le_right
      (inf_le_left.trans inf_le_right) inf_le_left,
    ← (f j).naturality (W j) (W i ⊓ W j) inf_le_right
      (inf_le_right.trans inf_le_right) inf_le_right,
    moduleRestrict_comp, moduleRestrict_comp,
    hcompat i j (W i ⊓ W j) (inf_le_left.trans inf_le_right)
      (inf_le_right.trans inf_le_right)]

/-- The unique glued image, chosen from the actual sheaf existence theorem. -/
noncomputable def gluedModuleImage (V : Opens X) (s : M.val.obj (op V)) :
    N.val.obj (op V) :=
  (existsUnique_glued_module_image U hcover f hcompat V s).choose

theorem gluedModuleImage_restrict_cover (V : Opens X) (s : M.val.obj (op V)) (i : ι) :
    moduleRestrict N (inf_le_left : V ⊓ U i ≤ V)
        (gluedModuleImage U hcover f hcompat V s) =
      (f i).app (V ⊓ U i) inf_le_right (moduleRestrict M inf_le_left s) :=
  (existsUnique_glued_module_image U hcover f hcompat V s).choose_spec.1 i

/-- Restriction to any subopen in one chart recovers that local map. -/
theorem gluedModuleImage_on_subopen (i : ι) (V : Opens X) (hi : V ≤ U i)
    (s : M.val.obj (op V)) :
    gluedModuleImage U hcover f hcompat V s = (f i).app V hi s := by
  symm
  apply (existsUnique_glued_module_image U hcover f hcompat V s).choose_spec.2
  intro j
  rw [← (f i).naturality V (V ⊓ U j) hi (inf_le_left.trans hi) inf_le_left,
    hcompat i j (V ⊓ U j) (inf_le_left.trans hi) inf_le_right]

omit f hcompat in
/-- Equality of sections can be tested on the intersections with a cover. -/
theorem module_eq_of_cover_restrictions (V : Opens X) (s t : N.val.obj (op V))
    (h : ∀ i, moduleRestrict N (inf_le_left : V ⊓ U i ≤ V) s =
      moduleRestrict N (inf_le_left : V ⊓ U i ≤ V) t) : s = t := by
  let G : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨N.val.presheaf, N.isSheaf⟩
  apply G.eq_of_locally_eq' (fun i ↦ V ⊓ U i) V (fun _ ↦ homOfLE inf_le_left)
    (by simp only [← inf_iSup_eq, hcover, inf_top_eq, le_refl]) s t
  exact h

theorem gluedModuleImage_add (V : Opens X) (s t : M.val.obj (op V)) :
    gluedModuleImage U hcover f hcompat V (s + t) =
      gluedModuleImage U hcover f hcompat V s + gluedModuleImage U hcover f hcompat V t := by
  apply module_eq_of_cover_restrictions U hcover V
  intro i
  rw [gluedModuleImage_restrict_cover]
  change (f i).app (V ⊓ U i) inf_le_right
      (M.val.map (homOfLE (show V ⊓ U i ≤ V from inf_le_left)).op (s + t)) =
    N.val.map (homOfLE (show V ⊓ U i ≤ V from inf_le_left)).op (_ + _)
  rw [map_add, map_add, map_add]
  exact congrArg₂ (· + ·)
    (gluedModuleImage_restrict_cover U hcover f hcompat V s i).symm
    (gluedModuleImage_restrict_cover U hcover f hcompat V t i).symm

theorem gluedModuleImage_smul (V : Opens X) (r : R.val.obj (op V)) (s : M.val.obj (op V)) :
    gluedModuleImage U hcover f hcompat V (r • s) =
      r • gluedModuleImage U hcover f hcompat V s := by
  apply module_eq_of_cover_restrictions U hcover V
  intro i
  rw [gluedModuleImage_restrict_cover]
  change (f i).app (V ⊓ U i) inf_le_right
      (M.val.map (homOfLE (show V ⊓ U i ≤ V from inf_le_left)).op (r • s)) =
    N.val.map (homOfLE (show V ⊓ U i ≤ V from inf_le_left)).op (r • _)
  rw [M.val.map_smul, N.val.map_smul, map_smul]
  exact congrArg
    (fun x ↦ R.val.map (homOfLE (show V ⊓ U i ≤ V from inf_le_left)).op r • x)
    (gluedModuleImage_restrict_cover U hcover f hcompat V s i).symm

theorem gluedModuleImage_naturality (V W : Opens X) (hWV : W ≤ V)
    (s : M.val.obj (op V)) :
    gluedModuleImage U hcover f hcompat W (moduleRestrict M hWV s) =
      moduleRestrict N hWV (gluedModuleImage U hcover f hcompat V s) := by
  apply module_eq_of_cover_restrictions U hcover W
  intro i
  have hT : W ⊓ U i ≤ V ⊓ U i := inf_le_inf hWV le_rfl
  rw [gluedModuleImage_restrict_cover, moduleRestrict_comp, moduleRestrict_comp]
  have hnat := (f i).naturality (V ⊓ U i) (W ⊓ U i) inf_le_right inf_le_right hT
    (moduleRestrict M (inf_le_left : V ⊓ U i ≤ V) s)
  rw [moduleRestrict_comp, ← gluedModuleImage_restrict_cover U hcover f hcompat V s i,
    moduleRestrict_comp] at hnat
  exact hnat

/-- The glued image maps are actual linear maps. -/
noncomputable def gluedModuleLinearMap (V : Opens X) :
    M.val.obj (op V) →ₗ[R.val.obj (op V)] N.val.obj (op V) where
  toFun := gluedModuleImage U hcover f hcompat V
  map_add' := gluedModuleImage_add U hcover f hcompat V
  map_smul' := gluedModuleImage_smul U hcover f hcompat V

/-- The morphism of actual sheaves of modules obtained by local gluing. -/
noncomputable def glueModuleHom : M ⟶ N where
  val :=
    { app := fun V ↦ ModuleCat.ofHom (gluedModuleLinearMap U hcover f hcompat V.unop)
      naturality := by
        intro V W g
        ext s
        exact gluedModuleImage_naturality U hcover f hcompat V.unop W.unop g.unop.le s }

/-- The global morphism agrees with the local linear maps on every chart subopen. -/
theorem glueModuleHom_app (i : ι) (V : Opens X) (hi : V ≤ U i)
    (s : M.val.obj (op V)) :
    (glueModuleHom U hcover f hcompat).val.app (op V) s = (f i).app V hi s :=
  gluedModuleImage_on_subopen U hcover f hcompat i V hi s

/-- Local bijectivity yields an actual global isomorphism, after constructing
the global morphism by the sheaf axiom. -/
noncomputable def glueModuleIso
    (hf : ∀ i V (h : V ≤ U i), Function.Bijective ((f i).app V h)) : M ≅ N := by
  let g := glueModuleHom U hcover f hcompat
  apply moduleSheafIsoOfBijective g
  intro V
  apply sheaf_app_bijective_of_cover
    ((SheafOfModules.toSheaf R).obj M) ((SheafOfModules.toSheaf R).obj N)
    ((SheafOfModules.toSheaf R).map g).val U hcover
  intro i W h
  have heq : (fun s ↦ g.val.app (op W) s) = (f i).app W h := by
    funext s
    exact glueModuleHom_app U hcover f hcompat i W h s
  change Function.Bijective (fun s ↦ g.val.app (op W) s)
  rw [heq]
  exact hf i W h

theorem glueModuleIso_hom_app
    (hf : ∀ i V (h : V ≤ U i), Function.Bijective ((f i).app V h))
    (i : ι) (V : Opens X) (hi : V ≤ U i) (s : M.val.obj (op V)) :
    (glueModuleIso U hcover f hcompat hf).hom.val.app (op V) s = (f i).app V hi s :=
  glueModuleHom_app U hcover f hcompat i V hi s

end EvenQuinticConic
