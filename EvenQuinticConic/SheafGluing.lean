import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import EvenQuinticConic.GenericPointInjection

/-!
# Gluing on actual sheaves

The results in this file use mathlib's sheaf condition on open covers.
They do not assume a gluing operation or an existence theorem as an extra hypothesis.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace TopologicalSpace.Opens Opposite

namespace EvenQuinticConic

section ConcreteSheaves

universe x

variable {C : Type*} [Category C] {FC : C → C → Type*} {CC : C → Type*}
variable [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]
variable [HasLimitsOfSize.{x, x} C] [(forget C).ReflectsIsomorphisms]
variable [PreservesLimitsOfSize.{x, x} (forget C)]
variable {X : TopCat.{x}} (F G : TopCat.Sheaf C X) (f : F.1 ⟶ G.1)
variable {ι : Type*} (U : ι → Opens X) (hcover : iSup U = ⊤)

include hcover

/-- Bijectivity on every open contained in one member of an open cover implies
bijectivity on every open. Compatibility of local preimages follows from the
local injectivity; existence and uniqueness then use the actual sheaf axioms. -/
theorem sheaf_app_bijective_of_cover
    (hloc : ∀ i V, V ≤ U i → Function.Bijective (f.app (op V)))
    (V : Opens X) : Function.Bijective (f.app (op V)) := by
  let W : ι → Opens X := fun i => V ⊓ U i
  let j : ∀ i, W i ⟶ V := fun i => homOfLE inf_le_left
  have hW : V ≤ iSup W := by
    simp only [W, ← inf_iSup_eq, hcover, inf_top_eq, le_refl]
  have naturality_apply {A B : Opens X} (i : A ⟶ B)
      (s : ToType (F.1.obj (op B))) :
      f.app (op A) (F.1.map i.op s) = G.1.map i.op (f.app (op B) s) := by
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, f.naturality]
  constructor
  · intro s t hst
    apply F.eq_of_locally_eq' W V j hW s t
    intro i
    apply (hloc i (W i) inf_le_right).1
    rw [naturality_apply, naturality_apply, hst]
  · intro s
    choose sf hsf using fun i => (hloc i (W i) inf_le_right).2 (G.1.map (j i).op s)
    have hcompat : TopCat.Presheaf.IsCompatible F.1 W sf := by
      intro i k
      apply (hloc i (W i ⊓ W k) (inf_le_left.trans inf_le_right)).1
      rw [naturality_apply, naturality_apply, hsf, hsf]
      rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
        ← G.1.map_comp, ← G.1.map_comp]
      rfl
    obtain ⟨t, ht, _⟩ := F.existsUnique_gluing' W V j hW sf hcompat
    refine ⟨t, ?_⟩
    apply G.eq_of_locally_eq' W V j hW
    intro i
    rw [← naturality_apply, ht, hsf]

end ConcreteSheaves

section IntegralSchemes

open AlgebraicGeometry

variable (X : Scheme) [IsIntegral X]

/-- Local representatives of the same element of the actual function field
of an integral scheme glue uniquely. Equality on intersections is proved
using the injectivity of the actual generic stalk maps. -/
theorem existsUnique_section_of_generic_representatives
    {ι : Type*} (U : ι → X.Opens) [∀ i, Nonempty (U i)]
    (V : X.Opens) (j : ∀ i, U i ⟶ V) (hcover : V ≤ iSup U)
    (r : X.functionField) (s : ∀ i, Γ(X, U i))
    (hs : ∀ i, X.germToFunctionField (U i) (s i) = r) :
    ∃! t : Γ(X, V), ∀ i, X.presheaf.map (j i).op t = s i := by
  apply X.sheaf.existsUnique_gluing' U V j hcover s
  intro i k
  have hη : ∀ l, genericPoint X ∈ U l := fun l =>
    ((genericPoint_spec X).mem_open_set_iff (U l).isOpen).mpr (by
      simpa using (inferInstance : Nonempty (U l)))
  letI : Nonempty (U i ⊓ U k : X.Opens) := ⟨⟨genericPoint X, hη i, hη k⟩⟩
  apply regular_restrict_eq_of_generic_eq X
  exact (hs i).trans (hs k).symm

/-- The unique glued regular function has the specified generic value. -/
theorem existsUnique_section_with_generic_value
    {ι : Type*} (U : ι → X.Opens) [∀ i, Nonempty (U i)]
    (V : X.Opens) [Nonempty V] (j : ∀ i, U i ⟶ V) (hcover : V ≤ iSup U)
    (r : X.functionField) (s : ∀ i, Γ(X, U i))
    (hs : ∀ i, X.germToFunctionField (U i) (s i) = r) :
    ∃! t : Γ(X, V), X.germToFunctionField V t = r ∧
      ∀ i, X.presheaf.map (j i).op t = s i := by
  obtain ⟨t, ht, _⟩ := existsUnique_section_of_generic_representatives X U V j hcover r s hs
  have hη : genericPoint X ∈ V :=
    ((genericPoint_spec X).mem_open_set_iff V.isOpen).mpr (by
      simpa using (inferInstance : Nonempty V))
  obtain ⟨i, _⟩ := Opens.mem_iSup.mp (hcover hη)
  have htr : X.germToFunctionField V t = r := by
    rw [← generic_germ_restrict X (j i) t, ht, hs]
  refine ⟨t, ⟨htr, ht⟩, ?_⟩
  intro t' ht'
  apply X.germToFunctionField_injective V
  exact ht'.1.trans htr.symm

omit [IsIntegral X] in
/-- A section whose restrictions to an open cover are units is a unit.
The proof uses invertibility in every actual stalk and the sheaf criterion
for invertibility, including at points where some chosen numerator vanishes. -/
theorem isUnit_of_unit_restrictions
    {ι : Type*} (U : ι → X.Opens) (V : X.Opens)
    (j : ∀ i, U i ⟶ V) (hcover : V ≤ iSup U) (t : Γ(X, V))
    (ht : ∀ i, IsUnit (X.presheaf.map (j i).op t)) : IsUnit t := by
  apply RingedSpace.isUnit_of_isUnit_germ X.toRingedSpace V t
  intro x hx
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hcover hx)
  have hiu := (X.presheaf.germ (U i) x hi).hom.isUnit_map (ht i)
  rwa [X.presheaf.germ_res_apply] at hiu

/-- Unit representatives of one rational function on a cover glue to a
unique unit of the ring of sections. All rings and maps here are the actual
structure sheaf and generic stalk of the integral scheme. -/
theorem existsUnique_unit_of_generic_representatives
    {ι : Type*} (U : ι → X.Opens) [∀ i, Nonempty (U i)]
    (V : X.Opens) [Nonempty V] (j : ∀ i, U i ⟶ V) (hcover : V ≤ iSup U)
    (r : X.functionField) (s : ∀ i, Γ(X, U i)ˣ)
    (hs : ∀ i, X.germToFunctionField (U i) (s i : Γ(X, U i)) = r) :
    ∃! t : Γ(X, V)ˣ, X.germToFunctionField V (t : Γ(X, V)) = r ∧
      ∀ i, Units.map (X.presheaf.map (j i).op).hom t = s i := by
  obtain ⟨t, ⟨htr, ht⟩, _⟩ := existsUnique_section_with_generic_value X U V j hcover r
    (fun i => (s i : Γ(X, U i))) hs
  have hunit : IsUnit t := isUnit_of_unit_restrictions X U V j hcover t (by
    intro i
    rw [ht i]
    exact (s i).isUnit)
  obtain ⟨v, rfl⟩ := hunit
  refine ⟨v, ⟨htr, ?_⟩, ?_⟩
  · intro i
    apply Units.ext
    exact ht i
  · intro v' hv'
    apply Units.ext
    apply X.germToFunctionField_injective V
    exact hv'.1.trans htr.symm

/-- A rational function whose positive power is a unit on each member of a
normal affine cover extends to one global unit. The local extension theorem
and the actual sheaf gluing theorem are composed here. -/
theorem existsUnique_unit_of_local_generic_power
    {ι : Type*} (U : ι → X.Opens) [∀ i, Nonempty (U i)]
    (hU : ∀ i, IsAffineOpen (U i)) [∀ i, IsIntegrallyClosed Γ(X, U i)]
    (V : X.Opens) [Nonempty V] (j : ∀ i, U i ⟶ V) (hcover : V ≤ iSup U)
    (r : X.functionField) (s : ∀ i, Γ(X, U i)ˣ) {n : ℕ} (hn : 0 < n)
    (hs : ∀ i, r ^ n = X.germToFunctionField (U i) (s i : Γ(X, U i))) :
    ∃! t : Γ(X, V)ˣ, X.germToFunctionField V (t : Γ(X, V)) = r := by
  choose v hv using fun i =>
    (existsUnique_regular_unit_of_generic_pow_eq X (U i) (hU i) r (s i) hn (hs i)).exists
  obtain ⟨t, ht, _⟩ := existsUnique_unit_of_generic_representatives X U V j hcover r v
    (fun i => (hv i).1)
  refine ⟨t, ht.1, ?_⟩
  intro t' ht'
  apply Units.ext
  apply X.germToFunctionField_injective V
  exact ht'.trans ht.1.symm

end IntegralSchemes

end EvenQuinticConic
