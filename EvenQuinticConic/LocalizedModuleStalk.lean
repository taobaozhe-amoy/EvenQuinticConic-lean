import Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# Localized module stalks from actual principal-open localizations

An actual module presheaf on `Spec A` has an `A`-module presheaf obtained
from the structure sheaf's constant sections. If compatible maps from a fixed
module are localizations on principal opens, their maps to stalks are the
corresponding prime localizations. No sheaf condition or identification of
sections on arbitrary opens is assumed.
-/

noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

namespace EvenQuinticConic

universe u

variable {A : Type u} [CommRing A]

/-- The actual structure-sheaf module presheaf with scalars restricted to `A`. -/
def affineModulePresheaf
    (P : PresheafOfModules.{u} ((Spec.structureSheaf A).val ⋙ forget₂ CommRingCat RingCat)) :
    TopCat.Presheaf (ModuleCat.{u} A) (PrimeSpectrum.Top A) :=
  (PresheafOfModules.forgetToPresheafModuleCat (op ⊤)
    (Limits.initialOpOfTerminal Limits.isTerminalTop)).obj P ⋙
    ModuleCat.restrictScalars (StructureSheaf.globalSectionsIso A).hom.hom

variable (P : PresheafOfModules.{u}
  ((Spec.structureSheaf A).val ⋙ forget₂ CommRingCat RingCat))

@[simp]
theorem affineModulePresheaf_map_apply {U V : Opens (PrimeSpectrum.Top A)}
    (i : V ⟶ U) (m : (affineModulePresheaf P).obj (op U)) :
    (affineModulePresheaf P).map i.op m = P.map i.op m := rfl

/-- Restricting scalars uses the original structure sheaf's constant sections. -/
theorem affineModulePresheaf_smul (U : Opens (PrimeSpectrum.Top A)) (a : A)
    (m : (affineModulePresheaf P).obj (op U)) :
    a • m = @SMul.smul
      (((Spec.structureSheaf A).val ⋙ forget₂ CommRingCat RingCat).obj (op U))
      (P.obj (op U)) inferInstance (StructureSheaf.toOpen A U a) m := rfl

/-- A function invertible on an open set acts invertibly on actual module sections. -/
theorem affineModulePresheaf_smul_bijective (a : A)
    (U : Opens (PrimeSpectrum.Top A)) (hU : U ≤ PrimeSpectrum.basicOpen a) :
    Function.Bijective (fun m : (affineModulePresheaf P).obj (op U) ↦ a • m) := by
  have hu : IsUnit (StructureSheaf.toOpen A U a) := by
    have h := (StructureSheaf.isUnit_to_basicOpen_self A a).map
      ((Spec.structureSheaf A).val.map (homOfLE hU).op).hom
    simpa only [← CommRingCat.comp_apply, StructureSheaf.toOpen_res] using h
  simpa only [affineModulePresheaf_smul] using
    (hu.smul_bijective (β := P.obj (op U)))

/-- Nonvanishing functions act invertibly on a module presheaf stalk. -/
theorem affineModulePresheaf_stalk_isUnit (p : PrimeSpectrum.Top A)
    (a : p.asIdeal.primeCompl) :
    IsUnit (algebraMap A (Module.End A ((affineModulePresheaf P).stalk p)) a) := by
  let F := affineModulePresheaf P
  rw [Module.End.isUnit_iff]
  constructor
  · apply LinearMap.ker_eq_bot.mp
    apply eq_bot_iff.mpr
    intro z hz
    change (a : A) • z = 0 at hz
    obtain ⟨U, hpU, m, rfl⟩ := F.germ_exist p z
    have heq : F.germ U p hpU ((a : A) • m) = F.germ U p hpU 0 := by
      simpa only [map_smul, map_zero] using hz
    obtain ⟨V, hpV, iVU, _, hm⟩ := F.germ_eq p hpU hpU _ _ heq
    let W := V ⊓ PrimeSpectrum.basicOpen (a : A)
    have hpW : p ∈ W := ⟨hpV, a.2⟩
    have hmW : (a : A) • F.map (homOfLE (show W ≤ U from inf_le_left.trans iVU.le)).op m = 0 := by
      have h := congrArg (F.map (homOfLE (show W ≤ V from inf_le_left)).op) hm
      simpa only [map_smul, map_zero, ← ConcreteCategory.comp_apply, ← F.map_comp] using h
    have hzero : F.map (homOfLE (show W ≤ U from inf_le_left.trans iVU.le)).op m = 0 :=
      (affineModulePresheaf_smul_bijective P a W inf_le_right).injective
        (hmW.trans (smul_zero _).symm)
    change F.germ U p hpU m = 0
    rw [← F.germ_res_apply (homOfLE (show W ≤ U from inf_le_left.trans iVU.le)) p hpW m,
      hzero, map_zero]
  · intro z
    obtain ⟨U, hpU, m, rfl⟩ := F.germ_exist p z
    let W := U ⊓ PrimeSpectrum.basicOpen (a : A)
    have hpW : p ∈ W := ⟨hpU, a.2⟩
    obtain ⟨n, hn⟩ := (affineModulePresheaf_smul_bijective P a W inf_le_right).surjective
      (F.map (homOfLE (show W ≤ U from inf_le_left)).op m)
    refine ⟨F.germ W p hpW n, ?_⟩
    change (a : A) • F.germ W p hpW n = F.germ U p hpU m
    rw [← map_smul]
    exact (congrArg (F.germ W p hpW) hn).trans
      (F.germ_res_apply (homOfLE (show W ≤ U from inf_le_left)) p hpW m)

variable (M : ModuleCat.{u} A)
  (τ : (Functor.const ((Opens (PrimeSpectrum.Top A))ᵒᵖ)).obj M ⟶ affineModulePresheaf P)

/-- The map from a fixed module to the actual module presheaf stalk. -/
def affineModuleToStalk (p : PrimeSpectrum.Top A) :
    M ⟶ (affineModulePresheaf P).stalk p :=
  τ.app (op ⊤) ≫ (affineModulePresheaf P).germ ⊤ p (by trivial)

/-- The compatible maps to all opens induce the same germ. -/
theorem affineModuleToStalk_eq_germ (p : PrimeSpectrum.Top A)
    (U : Opens (PrimeSpectrum.Top A)) (hpU : p ∈ U) (m : M) :
    affineModuleToStalk P M τ p m =
      (affineModulePresheaf P).germ U p hpU (τ.app (op U) m) := by
  have h := τ.naturality (homOfLE (show U ≤ ⊤ from le_top)).op
  have hm : (affineModulePresheaf P).map (homOfLE (show U ≤ ⊤ from le_top)).op
      (τ.app (op ⊤) m) = τ.app (op U) m := by
    simpa using (ConcreteCategory.congr_hom h m).symm
  rw [← hm, TopCat.Presheaf.germ_res_apply]
  rfl

/-- Localizations on principal opens determine the genuine prime-localized stalk. -/
theorem affineModuleToStalk_isLocalizedModule
    (hlocal : ∀ a : A, IsLocalizedModule (Submonoid.powers a)
      (τ.app (op (PrimeSpectrum.basicOpen a))).hom)
    (p : PrimeSpectrum.Top A) :
    IsLocalizedModule p.asIdeal.primeCompl (affineModuleToStalk P M τ p).hom where
  map_units := affineModulePresheaf_stalk_isUnit P p
  surj z := by
    obtain ⟨U, hpU, ⟨a, rfl⟩, m, rfl⟩ :=
      TopCat.Presheaf.germ_exist_of_isBasis PrimeSpectrum.isBasis_basic_opens
        (affineModulePresheaf P) p z
    letI := hlocal a
    obtain ⟨⟨n, s⟩, hs⟩ := IsLocalizedModule.surj (Submonoid.powers a)
      (τ.app (op (PrimeSpectrum.basicOpen a))).hom m
    have hsp : (s : A) ∈ p.asIdeal.primeCompl :=
      (Submonoid.powers_le.mpr hpU) s.2
    refine ⟨⟨n, ⟨s, hsp⟩⟩, ?_⟩
    change (s : A) • (affineModulePresheaf P).germ _ p hpU m =
      affineModuleToStalk P M τ p n
    rw [affineModuleToStalk_eq_germ P M τ p _ hpU, ← map_smul]
    exact congrArg ((affineModulePresheaf P).germ _ p hpU) hs
  exists_of_eq {x y} hxy := by
    obtain ⟨U, hpU, ⟨a, rfl⟩, hU₁, hU₂, h⟩ :=
      TopCat.Presheaf.germ_eq_of_isBasis PrimeSpectrum.isBasis_basic_opens
        (affineModulePresheaf P) p (show p ∈ (⊤ : Opens _) from trivial)
        (show p ∈ (⊤ : Opens _) from trivial) hxy
    have hn (m : M) : (affineModulePresheaf P).map (homOfLE hU₁).op
        (τ.app (op ⊤) m) = τ.app (op (PrimeSpectrum.basicOpen a)) m := by
      simpa using (ConcreteCategory.congr_hom (τ.naturality (homOfLE hU₁).op) m).symm
    have h' : τ.app (op (PrimeSpectrum.basicOpen a)) x =
        τ.app (op (PrimeSpectrum.basicOpen a)) y := by
      change (affineModulePresheaf P).map (homOfLE hU₁).op (τ.app (op ⊤) x) =
        (affineModulePresheaf P).map (homOfLE hU₁).op (τ.app (op ⊤) y) at h
      rw [hn, hn] at h
      exact h
    letI := hlocal a
    obtain ⟨s, hs⟩ := IsLocalizedModule.exists_of_eq
      (S := Submonoid.powers a) (f := (τ.app (op (PrimeSpectrum.basicOpen a))).hom) h'
    exact ⟨⟨s, (Submonoid.powers_le.mpr hpU) s.2⟩, hs⟩

end EvenQuinticConic
