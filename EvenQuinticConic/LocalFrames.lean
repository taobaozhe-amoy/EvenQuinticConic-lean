import EvenQuinticConic.SheafTrivialization

/-!
# Coherent local frames of actual module sheaves

A local frame consists of linear equivalences on all subopens, compatible
with the actual restriction maps. A unit coordinate on the covering open
therefore remains a unit on every smaller open, including empty opens.
This file does not define a particular geometric theta characteristic.
-/

open CategoryTheory Opposite TopologicalSpace

universe u

namespace EvenQuinticConic

variable {X : TopCat.{u}} {R : TopCat.Sheaf RingCat.{u} X}
  (M : SheafOfModules.{u} R)

/-- A rank-one trivialization over an open subset, expressed by natural
linear coordinates on its subopens. This is actual module and restriction
data, not a proposition asserting that a desired global isomorphism exists. -/
structure ModuleSheafFrame (U : Opens X) where
  coordinate : ∀ (V : Opens X), V ≤ U →
    M.val.obj (op V) ≃ₗ[R.val.obj (op V)] R.val.obj (op V)
  coordinate_restrict : ∀ (V W : Opens X) (hV : V ≤ U) (hW : W ≤ U)
    (hWV : W ≤ V) (s : M.val.obj (op V)),
    coordinate W hW (M.val.map (homOfLE hWV).op s) =
      R.val.map (homOfLE hWV).op (coordinate V hV s)

variable {M}

/-- Coordinates of a genuine compatible section commute with restriction. -/
theorem ModuleSheafFrame.coordinate_section_restrict {U : Opens X}
    (e : ModuleSheafFrame M U) (s : M.sections) (V : Opens X) (hV : V ≤ U) :
    e.coordinate V hV (s.eval (op V)) =
      R.val.map (homOfLE hV).op (e.coordinate U le_rfl (s.eval (op U))) := by
  have hr : M.val.map (homOfLE hV).op (s.eval (op U)) = s.eval (op V) :=
    PresheafOfModules.sections_property s (homOfLE hV).op
  rw [← hr]
  exact e.coordinate_restrict U V le_rfl hV hV (s.eval (op U))

/-- A unit coordinate on the covering open remains a unit on every subopen.
No fraction-field map on an empty open is needed. -/
theorem ModuleSheafFrame.isUnit_coordinate_on_subopen {U : Opens X}
    (e : ModuleSheafFrame M U) (s : M.sections)
    (hs : IsUnit (e.coordinate U le_rfl (s.eval (op U))))
    (V : Opens X) (hV : V ≤ U) :
    IsUnit (e.coordinate V hV (s.eval (op V))) := by
  rw [e.coordinate_section_restrict s V hV]
  exact hs.map (R.val.map (homOfLE hV).op).hom

/-- Coherent frames reduce the local unit hypotheses to the members of the
cover themselves. The conclusion is an actual isomorphism of module sheaves. -/
noncomputable def moduleSheafTrivializationOfCoverFrames
    (s : M.sections) {ι : Type*} (U : ι → Opens X) (hcover : iSup U = ⊤)
    (frame : ∀ i, ModuleSheafFrame M (U i))
    (hs : ∀ i, IsUnit ((frame i).coordinate (U i) le_rfl (s.eval (op (U i))))) :
    SheafOfModules.unit R ≅ M :=
  moduleSheafTrivializationOfLocalUnit M s U hcover
    (fun i V h ↦ (frame i).coordinate V h)
    (fun i V h ↦ (frame i).isUnit_coordinate_on_subopen s (hs i) V h)

/-- Actual compatible local generators glue to a global section which
trivializes the module sheaf. A global generator is constructed, not assumed. -/
theorem exists_global_generator_of_compatible_local_units
    {ι : Type*} (U : ι → Opens X) (hcover : iSup U = ⊤)
    (frame : ∀ i, ModuleSheafFrame M (U i))
    (t : ∀ i, M.val.obj (op (U i)))
    (ht : TopCat.Presheaf.IsCompatible M.val.presheaf U t)
    (hu : ∀ i, IsUnit ((frame i).coordinate (U i) le_rfl (t i))) :
    ∃ s : M.sections, (∀ i, s.eval (op (U i)) = t i) ∧
      ∃ e : SheafOfModules.unit R ≅ M,
        ∀ V (r : R.val.obj (op V)), e.hom.val.app (op V) r = r • s.eval (op V) := by
  let F : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨M.val.presheaf, M.isSheaf⟩
  obtain ⟨a, ha, _⟩ := F.existsUnique_gluing' U ⊤
    (fun _ ↦ homOfLE le_top) (by rw [hcover]) t ht
  let s := moduleGlobalSectionFamily M a
  have hs : ∀ i, s.eval (op (U i)) = t i := fun i ↦ ha i
  have hu' : ∀ i, IsUnit ((frame i).coordinate (U i) le_rfl (s.eval (op (U i)))) := by
    intro i
    rw [hs i]
    exact hu i
  refine ⟨s, hs, moduleSheafTrivializationOfCoverFrames s U hcover frame hu', ?_⟩
  intro V r
  rfl

end EvenQuinticConic
