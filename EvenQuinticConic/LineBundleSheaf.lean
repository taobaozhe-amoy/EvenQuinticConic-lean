import EvenQuinticConic.LineBundlePresheaf
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# The actual sheaf descended from unit transition functions

A compatible family of descended sections is glued coordinate by coordinate
using the actual structure sheaf. Its restriction and transition laws follow
by separation in that same structure sheaf.
-/

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

universe u

namespace EvenQuinticConic.UnitTransition

variable {X : Scheme.{u}} {ι : Type u} {U : ι → X.Opens}
    (g : UnitTransition X U)
    {β : Type u} (V : β → X.Opens) (sf : ∀ b, g.Section (V b))
    (hsf : ∀ b c, (sf b).restrict (show V b ⊓ V c ≤ V b from inf_le_left) =
      (sf c).restrict (show V b ⊓ V c ≤ V c from inf_le_right))

private theorem subordinate_cover (W : X.Opens) (hWV : W ≤ iSup V) :
    W ≤ ⨆ b, W ⊓ V b := by
  rw [← inf_iSup_eq]
  exact le_inf le_rfl hWV

include hsf

/-- Coordinates of a compatible family agree on overlaps, as actual
regular functions, by taking coordinates of the original section equality. -/
theorem local_coordinate_compatible (i : ι) (W : X.Opens)
    (hWi : W ≤ U i) :
    TopCat.Presheaf.IsCompatible X.presheaf (fun b => W ⊓ V b)
      (fun b => (sf b).eval i (W ⊓ V b) inf_le_right (inf_le_left.trans hWi)) := by
  intro b c
  let Z := (W ⊓ V b) ⊓ (W ⊓ V c)
  have hZbc : Z ≤ V b ⊓ V c :=
    le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)
  have hZi : Z ≤ U i := inf_le_left.trans (inf_le_left.trans hWi)
  have h := congrArg (fun s : g.Section (V b ⊓ V c) =>
    s.eval i Z hZbc hZi) (hsf b c)
  change res inf_le_left ((sf b).eval i (W ⊓ V b) inf_le_right _) =
    res inf_le_right ((sf c).eval i (W ⊓ V c) inf_le_right _)
  rw [(sf b).naturality, (sf c).naturality]
  exact h

/-- Existence of each glued coordinate comes from the actual structure
sheaf, not an extra gluing axiom imposed on the transition construction. -/
theorem exists_coordinate_gluing (i : ι) (W : X.Opens)
    (hWV : W ≤ iSup V) (hWi : W ≤ U i) :
    ∃ a : Γ(X, W), ∀ b,
      res (show W ⊓ V b ≤ W from inf_le_left) a =
        (sf b).eval i (W ⊓ V b) inf_le_right (inf_le_left.trans hWi) := by
  obtain ⟨a, ha, _⟩ := X.sheaf.existsUnique_gluing'
    (fun b => W ⊓ V b) W (fun _ => homOfLE inf_le_left)
    (subordinate_cover V W hWV)
    (fun b => (sf b).eval i (W ⊓ V b) inf_le_right (inf_le_left.trans hWi))
    (local_coordinate_compatible g V sf hsf i W hWi)
  exact ⟨a, ha⟩

/-- The regular function obtained by gluing one chart coordinate. -/
noncomputable def coordinateGluing (i : ι) (W : X.Opens)
    (hWV : W ≤ iSup V) (hWi : W ≤ U i) : Γ(X, W) :=
  (exists_coordinate_gluing g V sf hsf i W hWV hWi).choose

theorem coordinateGluing_spec (i : ι) (W : X.Opens)
    (hWV : W ≤ iSup V) (hWi : W ≤ U i) (b : β) :
    res (show W ⊓ V b ≤ W from inf_le_left)
      (coordinateGluing g V sf hsf i W hWV hWi) =
        (sf b).eval i (W ⊓ V b) inf_le_right (inf_le_left.trans hWi) :=
  (exists_coordinate_gluing g V sf hsf i W hWV hWi).choose_spec b

/-- On any subopen lying in one member of the given cover, the constructed
coordinate restricts to that member's actual coordinate. -/
theorem coordinateGluing_restrict_to_member (i : ι) (W Z : X.Opens)
    (hWV : W ≤ iSup V) (hWi : W ≤ U i) (b : β)
    (hZW : Z ≤ W) (hZb : Z ≤ V b) :
    res hZW (coordinateGluing g V sf hsf i W hWV hWi) =
      (sf b).eval i Z hZb (hZW.trans hWi) := by
  have hZ : Z ≤ W ⊓ V b := le_inf hZW hZb
  calc
    _ = res hZ (res (show W ⊓ V b ≤ W from inf_le_left)
        (coordinateGluing g V sf hsf i W hWV hWi)) := by rw [res_res]
    _ = res hZ ((sf b).eval i (W ⊓ V b) inf_le_right
        (inf_le_left.trans hWi)) := by rw [coordinateGluing_spec]
    _ = _ := (sf b).naturality i (W ⊓ V b) Z _ _ hZ

/-- The glued coordinates commute with restrictions because regular
functions in the actual structure sheaf are determined locally. -/
theorem coordinateGluing_naturality (i : ι) (W Z : X.Opens)
    (hWV : W ≤ iSup V) (hWi : W ≤ U i) (hZW : Z ≤ W) :
    res hZW (coordinateGluing g V sf hsf i W hWV hWi) =
      coordinateGluing g V sf hsf i Z (hZW.trans hWV) (hZW.trans hWi) := by
  apply X.sheaf.eq_of_locally_eq' (fun b => Z ⊓ V b) Z
    (fun _ => homOfLE inf_le_left)
    (subordinate_cover V Z (hZW.trans hWV))
  intro b
  change res inf_le_left (res hZW _) = res inf_le_left _
  rw [res_res,
    coordinateGluing_restrict_to_member g V sf hsf i W (Z ⊓ V b)
      hWV hWi b (inf_le_left.trans hZW) inf_le_right,
    coordinateGluing_spec]

/-- The transition law holds for the glued coordinates, by checking it on
each member of the cover and using the given transition naturality. -/
theorem coordinateGluing_transition (i j : ι) (W : X.Opens)
    (hWV : W ≤ iSup V) (hi : W ≤ U i) (hj : W ≤ U j) :
    coordinateGluing g V sf hsf i W hWV hi =
      (g.transition i j W hi hj : Γ(X, W)) *
        coordinateGluing g V sf hsf j W hWV hj := by
  apply X.sheaf.eq_of_locally_eq' (fun b => W ⊓ V b) W
    (fun _ => homOfLE inf_le_left) (subordinate_cover V W hWV)
  intro b
  change res inf_le_left _ = res inf_le_left (_ * _)
  rw [map_mul, coordinateGluing_spec, coordinateGluing_spec, res_transition]
  exact (sf b).transition i j (W ⊓ V b) inf_le_right _ _

/-- The actual section obtained by gluing a compatible family. -/
noncomputable def sectionGluing : g.Section (iSup V) :=
  ⟨fun i W => coordinateGluing g V sf hsf i W.val W.prop.1 W.prop.2, by
    constructor
    · intro i W Z hWV hWi hZW
      exact coordinateGluing_naturality g V sf hsf i W Z hWV hWi hZW
    · intro i j W hWV hi hj
      exact coordinateGluing_transition g V sf hsf i j W hWV hi hj⟩

/-- The constructed section genuinely restricts to each prescribed section. -/
theorem sectionGluing_spec (b : β) :
    (sectionGluing g V sf hsf).restrict (le_iSup V b) = sf b := by
  apply Section.ext
  intro i W hWb hWi
  change coordinateGluing g V sf hsf i W (hWb.trans (le_iSup V b)) hWi = _
  simpa using coordinateGluing_restrict_to_member g V sf hsf i W W
    (hWb.trans (le_iSup V b)) hWi b le_rfl hWb

/-- A section with the prescribed local restrictions equals the constructed
section, by uniqueness in the actual structure sheaf in every coordinate. -/
theorem sectionGluing_unique (s : g.Section (iSup V))
    (hs : ∀ b, s.restrict (le_iSup V b) = sf b) :
    s = sectionGluing g V sf hsf := by
  apply Section.ext
  intro i W hWV hWi
  apply X.sheaf.eq_of_locally_eq' (fun b => W ⊓ V b) W
    (fun _ => homOfLE inf_le_left) (subordinate_cover V W hWV)
  intro b
  change res inf_le_left (s.eval i W hWV hWi) =
    res inf_le_left (coordinateGluing g V sf hsf i W hWV hWi)
  rw [s.naturality, coordinateGluing_spec]
  exact congrArg (fun t : g.Section (V b) =>
    t.eval i (W ⊓ V b) inf_le_right (inf_le_left.trans hWi)) (hs b)

omit hsf

/-- The descended module presheaf satisfies the actual sheaf axiom. -/
theorem presheaf_isSheaf : TopCat.Presheaf.IsSheaf g.presheaf.presheaf := by
  apply (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing _).mpr
  intro β V sf hsf
  change ∀ b c, (sf b).restrict inf_le_left = (sf c).restrict inf_le_right at hsf
  refine ⟨sectionGluing g V sf hsf, sectionGluing_spec g V sf hsf, ?_⟩
  intro s hs
  exact sectionGluing_unique g V sf hsf s hs

/-- The actual module sheaf descended from the given unit transition
functions. Its sheaf property has been proved by coordinatewise gluing. -/
noncomputable def moduleSheaf : X.Modules where
  val := g.presheaf
  isSheaf := presheaf_isSheaf g

end EvenQuinticConic.UnitTransition
