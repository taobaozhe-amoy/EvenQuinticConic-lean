import EvenQuinticConic.AffineKaehlerDerivation
import EvenQuinticConic.LocalizedModuleStalk
import EvenQuinticConic.AffineKaehlerPresheafLocalization
import Mathlib.Topology.Sheaves.LocallySurjective

/-!
# The canonical affine differential-sheaf comparison

The comparison is checked on genuine stalk maps. Principal-open ring
localizations supply the source stalk, and the locally fractional module
sheaf supplies the target stalk. Local bijectivity then descends through
the actual sheafification map.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

namespace EvenQuinticConic

attribute [local instance] Types.instFunLike Types.instConcreteCategory

universe u

variable {A : Type u} [CommRing A]

/-- The morphism of `A`-module presheaves induced by an actual structure-sheaf
module morphism. -/
def affineModulePresheafMap
    {P Q : PresheafOfModules.{u}
      ((Spec.structureSheaf A).val ⋙ forget₂ CommRingCat RingCat)} (f : P ⟶ Q) :
    affineModulePresheaf P ⟶ affineModulePresheaf Q :=
  Functor.whiskerRight
    ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤)
      (Limits.initialOpOfTerminal Limits.isTerminalTop)).map f)
    (ModuleCat.restrictScalars (StructureSheaf.globalSectionsIso A).hom.hom)

@[simp]
theorem affineModulePresheafMap_app_apply
    {P Q : PresheafOfModules.{u}
      ((Spec.structureSheaf A).val ⋙ forget₂ CommRingCat RingCat)} (f : P ⟶ Q)
    (U : (Opens (PrimeSpectrum.Top A))ᵒᵖ) (m : P.obj U) :
    (affineModulePresheafMap f).app U m = f.app U m := rfl

/-- Scalar restriction does not change local injectivity of actual sections. -/
theorem affineModulePresheafMap_isLocallyInjective_iff
    {P Q : PresheafOfModules.{u}
      ((Spec.structureSheaf A).val ⋙ forget₂ CommRingCat RingCat)} (f : P ⟶ Q) :
    CategoryTheory.Presheaf.IsLocallyInjective
      (Opens.grothendieckTopology (PrimeSpectrum.Top A)) (affineModulePresheafMap f) ↔
    PresheafOfModules.IsLocallyInjective
      (Opens.grothendieckTopology (PrimeSpectrum.Top A)) f := by
  constructor <;> intro h <;> constructor
  all_goals intro U x y heq; exact h.equalizerSieve_mem (X := U) x y heq

/-- Scalar restriction does not change local surjectivity of actual sections. -/
theorem affineModulePresheafMap_isLocallySurjective_iff
    {P Q : PresheafOfModules.{u}
      ((Spec.structureSheaf A).val ⋙ forget₂ CommRingCat RingCat)} (f : P ⟶ Q) :
    CategoryTheory.Presheaf.IsLocallySurjective
      (Opens.grothendieckTopology (PrimeSpectrum.Top A)) (affineModulePresheafMap f) ↔
    PresheafOfModules.IsLocallySurjective
      (Opens.grothendieckTopology (PrimeSpectrum.Top A)) f := by
  constructor <;> intro h <;> constructor
  all_goals intro U x; exact h.imageSieve_mem (U := U) x

/-- Injectivity on genuine stalks implies local injectivity of a module-presheaf map. -/
theorem modulePresheaf_isLocallyInjective_of_stalk_injective
    {X : TopCat.{u}} {F G : X.Presheaf (ModuleCat.{u} A)} (f : F ⟶ G)
    (hf : ∀ x : X, Function.Injective
      ((TopCat.Presheaf.stalkFunctor (ModuleCat A) x).map f)) :
    CategoryTheory.Presheaf.IsLocallyInjective (Opens.grothendieckTopology X) f where
  equalizerSieve_mem {U} s t h := by
    intro x hx
    have hg : F.germ U.unop x hx s = F.germ U.unop x hx t := by
      apply hf x
      rw [TopCat.Presheaf.stalkFunctor_map_germ_apply,
        TopCat.Presheaf.stalkFunctor_map_germ_apply, h]
    obtain ⟨V, hxV, i, j, hV⟩ := F.germ_eq x hx hx s t hg
    refine ⟨V, i, ?_, hxV⟩
    change F.map i.op s = F.map i.op t
    simpa only [Subsingleton.elim j i] using hV

/-- A module-presheaf map with bijective stalk maps is locally bijective. -/
theorem affineModulePresheafMap_locallyBijective_of_stalk_bijective
    {P Q : PresheafOfModules.{u}
      ((Spec.structureSheaf A).val ⋙ forget₂ CommRingCat RingCat)} (f : P ⟶ Q)
    (hf : ∀ p : PrimeSpectrum.Top A, Function.Bijective
      ((TopCat.Presheaf.stalkFunctor (ModuleCat A) p).map (affineModulePresheafMap f))) :
    PresheafOfModules.IsLocallyInjective
        (Opens.grothendieckTopology (PrimeSpectrum.Top A)) f ∧
      PresheafOfModules.IsLocallySurjective
        (Opens.grothendieckTopology (PrimeSpectrum.Top A)) f := by
  constructor
  · apply (affineModulePresheafMap_isLocallyInjective_iff f).mp
    exact modulePresheaf_isLocallyInjective_of_stalk_injective _ (fun p ↦ (hf p).injective)
  · apply (affineModulePresheafMap_isLocallySurjective_iff f).mp
    exact (TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks _).mpr
      (fun p ↦ (hf p).surjective)

/-- A comparison of genuine module sheaves is an isomorphism when its
composite with a locally bijective presentation is bijective on stalks. -/
theorem affineSheafHom_isIso_of_presentation_stalk_bijective
    {P : PresheafOfModules.{u}
      ((Spec.structureSheaf A).val ⋙ forget₂ CommRingCat RingCat)}
    {Q T : (Spec (CommRingCat.of A)).Modules} (u : P ⟶ Q.val) (f : Q ⟶ T)
    [PresheafOfModules.IsLocallyInjective
      (Opens.grothendieckTopology (PrimeSpectrum.Top A)) u]
    [PresheafOfModules.IsLocallySurjective
      (Opens.grothendieckTopology (PrimeSpectrum.Top A)) u]
    (hf : ∀ p : PrimeSpectrum.Top A, Function.Bijective
      ((TopCat.Presheaf.stalkFunctor (ModuleCat A) p).map
        (affineModulePresheafMap (u ≫ f.val)))) : IsIso f := by
  let J := Opens.grothendieckTopology (PrimeSpectrum.Top A)
  let R := (Spec.structureSheaf A).val ⋙ forget₂ CommRingCat RingCat
  let u' := (PresheafOfModules.toPresheaf R).map u
  let f' := (PresheafOfModules.toPresheaf R).map f.val
  obtain ⟨hi, hs⟩ := affineModulePresheafMap_locallyBijective_of_stalk_bijective
    (u ≫ f.val) hf
  haveI : CategoryTheory.Presheaf.IsLocallyInjective J (u' ≫ f') := by
    simpa only [PresheafOfModules.IsLocallyInjective, Functor.map_comp] using hi
  haveI : CategoryTheory.Presheaf.IsLocallySurjective J (u' ≫ f') := by
    simpa only [PresheafOfModules.IsLocallySurjective, Functor.map_comp] using hs
  haveI : CategoryTheory.Presheaf.IsLocallyInjective J f' :=
    (CategoryTheory.Presheaf.comp_isLocallyInjective_iff J u' f').mp inferInstance
  haveI : CategoryTheory.Presheaf.IsLocallySurjective J f' :=
    (CategoryTheory.Presheaf.comp_isLocallySurjective_iff J u' f').mp inferInstance
  haveI : IsIso ((SheafOfModules.toSheaf _).map f) := by
    apply (CategoryTheory.Sheaf.isLocallyBijective_iff_isIso
      ((SheafOfModules.toSheaf _).map f)).mp
    constructor
    · change CategoryTheory.Presheaf.IsLocallyInjective J f'
      infer_instance
    · change CategoryTheory.Presheaf.IsLocallySurjective J f'
      infer_instance
  exact isIso_of_reflects_iso f (SheafOfModules.toSheaf _)

/-- A map to the actual associated module sheaf induces bijections on stalks
when its source is the same principal-open localization and the global
generators are sent to their genuine locally fractional sections. -/
theorem affineModulePresheafMap_tilde_stalk_bijective
    {P : PresheafOfModules.{u}
      ((Spec.structureSheaf A).val ⋙ forget₂ CommRingCat RingCat)}
    (M N : ModuleCat.{u} A)
    (τ : (Functor.const ((Opens (PrimeSpectrum.Top A))ᵒᵖ)).obj M ⟶
      affineModulePresheaf P)
    (hlocal : ∀ a : A, IsLocalizedModule (Submonoid.powers a)
      (τ.app (op (PrimeSpectrum.basicOpen a))).hom)
    (e : M ≅ N) (φ : P ⟶ N.tilde.val)
    (hφ : ∀ m : M, φ.app (op ⊤) (τ.app (op ⊤) m) =
      ModuleCat.Tilde.toOpen N ⊤ (e.hom m)) (p : PrimeSpectrum.Top A) :
    Function.Bijective ((TopCat.Presheaf.stalkFunctor (ModuleCat A) p).map
      (affineModulePresheafMap φ)) := by
  let f := affineModuleToStalk P M τ p
  let g := e.hom ≫ ModuleCat.Tilde.toStalk N p
  let α := (TopCat.Presheaf.stalkFunctor (ModuleCat A) p).map
    (affineModulePresheafMap φ)
  letI : IsLocalizedModule p.asIdeal.primeCompl f.hom :=
    affineModuleToStalk_isLocalizedModule P M τ hlocal p
  letI : IsLocalizedModule p.asIdeal.primeCompl g.hom :=
    IsLocalizedModule.of_linearEquiv_right p.asIdeal.primeCompl
      (ModuleCat.Tilde.toStalk N p).hom e.toLinearEquiv
  have hcomp : f ≫ α = g := by
    ext m
    change α ((affineModulePresheaf P).germ ⊤ p (by trivial) (τ.app (op ⊤) m)) = _
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
    change N.tildeInModuleCat.germ ⊤ p (by trivial)
      (φ.app (op ⊤) (τ.app (op ⊤) m)) = _
    rw [hφ]
    rfl
  let E := IsLocalizedModule.linearEquiv p.asIdeal.primeCompl f.hom g.hom
  have hα : α.hom = E.toLinearMap := by
    apply IsLocalizedModule.ext p.asIdeal.primeCompl f.hom
      (IsLocalizedModule.map_units g.hom)
    ext m
    change α (f m) = E (f m)
    rw [IsLocalizedModule.linearEquiv_apply]
    exact ConcreteCategory.congr_hom hcomp m
  change Function.Bijective α.hom
  rw [hα]
  exact E.bijective

variable {K : Type u} [CommRing K] [Algebra K A]

/-- The actual canonical affine comparison is an isomorphism: the
sheafification of differentials of regular functions is the associated
sheaf of the ring's Kähler differential module. -/
theorem affineKaehlerComparison_isIso :
    IsIso (affineKaehlerComparison (K := K) (A := A)) := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap K A))
  let η := schemeKaehlerSheafificationMap f
  let c := affineKaehlerComparison (K := K) (A := A)
  have hηi : PresheafOfModules.IsLocallyInjective (Opens.grothendieckTopology (PrimeSpectrum.Top A)) η := by
    change CategoryTheory.Presheaf.IsLocallyInjective (Opens.grothendieckTopology (PrimeSpectrum.Top A))
      (CategoryTheory.toSheafify (Opens.grothendieckTopology (PrimeSpectrum.Top A)) (schemeKaehlerPresheaf f).presheaf)
    exact ((Opens.grothendieckTopology (PrimeSpectrum.Top A)).W_toSheafify
      (schemeKaehlerPresheaf f).presheaf).isLocallyInjective
  have hηs : PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology (PrimeSpectrum.Top A)) η := by
    change CategoryTheory.Presheaf.IsLocallySurjective (Opens.grothendieckTopology (PrimeSpectrum.Top A))
      (CategoryTheory.toSheafify (Opens.grothendieckTopology (PrimeSpectrum.Top A)) (schemeKaehlerPresheaf f).presheaf)
    exact ((Opens.grothendieckTopology (PrimeSpectrum.Top A)).W_toSheafify
      (schemeKaehlerPresheaf f).presheaf).isLocallySurjective
  apply @affineSheafHom_isIso_of_presentation_stalk_bijective A _ _ _ _ η c hηi hηs
  intro p
  apply affineModulePresheafMap_tilde_stalk_bijective
    (affineRingKaehlerModule K A) (ModuleCat.of A Ω[A⁄K])
    (affineKaehlerToPresheaf K A) (affineKaehlerToPresheaf_isLocalizedModule K A)
    (affineRingKaehlerModule_iso K A) (η ≫ c.val) ?_ p
  have h : (affineKaehlerToPresheaf K A).app (op ⊤) ≫
      (affineModulePresheafMap (η ≫ c.val)).app (op ⊤) =
        (affineRingKaehlerModule_iso K A).hom ≫
          ModuleCat.Tilde.toOpen (ModuleCat.of A Ω[A⁄K]) ⊤ := by
    apply CommRingCat.KaehlerDifferential.ext
      (f := CommRingCat.ofHom (algebraMap K A))
    intro a
    simp only [ModuleCat.comp_apply]
    erw [affineKaehlerToPresheaf_d K A (op ⊤) a,
      affineRingKaehlerModule_iso_hom_d K A a]
    change (affineKaehlerComparison (K := K) (A := A)).val.app (op ⊤)
      ((schemeKaehlerDerivation f).d (StructureSheaf.toOpen A ⊤ a)) = _
    rw [affineKaehlerComparison_apply, affineKaehlerDifferential_toOpen]
    rfl
  intro m
  exact ConcreteCategory.congr_hom h m

/-- The canonical isomorphism with the actual locally fractional module sheaf. -/
def affineKaehlerSheafIso :
    schemeKaehlerSheaf (Spec.map (CommRingCat.ofHom (algebraMap K A))) ≅
      ModuleCat.tilde (ModuleCat.of A Ω[A⁄K]) := by
  letI := affineKaehlerComparison_isIso (K := K) (A := A)
  exact asIso (affineKaehlerComparison (K := K) (A := A))

/-- The isomorphism preserves the differential of every actual regular section. -/
theorem affineKaehlerSheafIso_hom_derivation (U : Opens (PrimeSpectrum A))
    (s : (Spec.structureSheaf A).val.obj (op U)) :
    (affineKaehlerSheafIso (K := K) (A := A)).hom.val.app (op U)
      ((schemeKaehlerDerivation
        (Spec.map (CommRingCat.ofHom (algebraMap K A)))).d s) =
      affineKaehlerDifferential (K := K) U s :=
  affineKaehlerComparison_apply U s

end EvenQuinticConic
