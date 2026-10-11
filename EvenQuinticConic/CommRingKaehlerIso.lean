import Mathlib.Algebra.Category.ModuleCat.Differentials.Basic
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-!
# Actual differential maps induced by ring isomorphisms

The categorical Kähler map in a square whose bottom map is a ring
isomorphism and whose top map is an identity is itself an isomorphism,
with the prescribed restriction of scalars.
-/

noncomputable section

open CategoryTheory

namespace EvenQuinticConic

universe u

variable {A B B' : CommRingCat.{u}} {f : A ⟶ B} {f' : A ⟶ B'}

private theorem commRingKaehlerMap_leftInverse
    (e : B ≅ B') (h : (𝟙 A) ≫ f' = f ≫ e.hom)
    (h' : (𝟙 A) ≫ f = f' ≫ e.inv) :
    Function.LeftInverse (CommRingCat.KaehlerDifferential.map h')
      (CommRingCat.KaehlerDifferential.map h) := by
  let α := CommRingCat.KaehlerDifferential.map h
  let β := CommRingCat.KaehlerDifferential.map h'
  let c : CommRingCat.KaehlerDifferential f ⟶ CommRingCat.KaehlerDifferential f :=
    ModuleCat.ofHom
      { toFun := fun x => β (α x)
        map_add' := by intro x y; simp only [map_add]
        map_smul' := by
          intro r x
          change β (α (r • x)) = r • β (α x)
          rw [map_smul]
          change β (e.hom r • α x) = _
          rw [map_smul]
          change e.inv (e.hom r) • β (α x) = _
          have hr : e.inv (e.hom r) = r := ConcreteCategory.congr_hom e.hom_inv_id r
          rw [hr] }
  have hc : c = 𝟙 _ := by
    apply CommRingCat.KaehlerDifferential.ext
    intro b
    change CommRingCat.KaehlerDifferential.map h'
      (CommRingCat.KaehlerDifferential.map h (CommRingCat.KaehlerDifferential.d b)) =
        CommRingCat.KaehlerDifferential.d b
    rw [CommRingCat.KaehlerDifferential.map_d, CommRingCat.KaehlerDifferential.map_d]
    have hb : e.inv (e.hom b) = b := ConcreteCategory.congr_hom e.hom_inv_id b
    rw [hb]
  intro x
  exact ConcreteCategory.congr_hom hc x

/-- The actual differential map of a base-preserving ring isomorphism is an
isomorphism after restricting scalars along that same ring isomorphism. -/
theorem commRingKaehlerMap_isIso
    (e : B ≅ B') (h : (𝟙 A) ≫ f' = f ≫ e.hom) :
    IsIso (CommRingCat.KaehlerDifferential.map h) := by
  have h' : (𝟙 A) ≫ f = f' ≫ e.inv := by
    simpa only [Category.id_comp, Category.assoc, e.hom_inv_id, Category.comp_id]
      using (congrArg (fun g => g ≫ e.inv) h).symm
  have hl := commRingKaehlerMap_leftInverse e h h'
  have hr := commRingKaehlerMap_leftInverse e.symm h' h
  exact (ConcreteCategory.isIso_iff_bijective _).mpr ⟨hl.injective, hr.surjective⟩

/-- Canonical module isomorphism induced by the actual differential map. -/
def commRingKaehlerIso
    (e : B ≅ B') (h : (𝟙 A) ≫ f' = f ≫ e.hom) :
    CommRingCat.KaehlerDifferential f ≅
      (ModuleCat.restrictScalars e.hom.hom).obj (CommRingCat.KaehlerDifferential f') := by
  letI := commRingKaehlerMap_isIso e h
  exact asIso (CommRingCat.KaehlerDifferential.map h)

/-- The canonical isomorphism sends the differential of a function to the
 differential of its image under the given ring isomorphism. -/
@[simp]
theorem commRingKaehlerIso_hom_d
    (e : B ≅ B') (h : (𝟙 A) ≫ f' = f ≫ e.hom) (b : B) :
    (commRingKaehlerIso e h).hom (CommRingCat.KaehlerDifferential.d (f := f) b) =
      CommRingCat.KaehlerDifferential.d (f := f') (e.hom b) :=
  CommRingCat.KaehlerDifferential.map_d h b

/-- The inverse isomorphism sends a differential to the differential of the
inverse image of its function. -/
@[simp]
theorem commRingKaehlerIso_inv_d
    (e : B ≅ B') (h : (𝟙 A) ≫ f' = f ≫ e.hom) (b : B') :
    (commRingKaehlerIso e h).inv (CommRingCat.KaehlerDifferential.d (f := f') b) =
      CommRingCat.KaehlerDifferential.d (f := f) (e.inv b) := by
  have hb : e.hom (e.inv b) = b := ConcreteCategory.congr_hom e.inv_hom_id b
  have hd := commRingKaehlerIso_hom_d e h (e.inv b)
  rw [hb] at hd
  rw [← hd]
  exact ConcreteCategory.congr_hom (commRingKaehlerIso e h).hom_inv_id _

end EvenQuinticConic
