import EvenQuinticConic.SchemeKaehlerSheaf
import EvenQuinticConic.LocalizedModuleStalk
import Mathlib.RingTheory.Etale.Kaehler

/-!
# Actual affine differential presheaf stalks

The base-ring differential module maps to the actual differential presheaf
on `Spec A`. On principal opens this is the genuine localization map for
Kähler differentials, hence the presheaf stalk is its prime localization.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace EvenQuinticConic

/-- Ring differentials commute with a localization, expressed using the
actual categorical map of differential modules. -/
theorem commRingKaehlerMap_isLocalizedModule
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T)
    (f' : R ⟶ T) (hf : (𝟙 R) ≫ f' = f ≫ g) (W : Submonoid S)
    (hlocal : @IsLocalization S _ W T _ g.hom.toAlgebra) :
    IsLocalizedModule W (CommRingCat.KaehlerDifferential.map hf).hom := by
  have hf' : f' = f ≫ g := by simpa only [Category.id_comp] using hf
  subst f'
  letI := f.hom.toAlgebra
  letI := g.hom.toAlgebra
  letI := (f ≫ g).hom.toAlgebra
  letI : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq' rfl
  letI := hlocal
  change IsLocalizedModule W (KaehlerDifferential.map R R S T)
  infer_instance

variable (K A : Type u) [CommRing K] [CommRing A] [Algebra K A]

/-- The actual relative differential presheaf on the affine scheme. -/
abbrev affineKaehlerPresheaf :=
  schemeKaehlerPresheaf (Spec.map (CommRingCat.ofHom (algebraMap K A)))

/-- The ring differential module, with its algebra structure specified by
the original base-ring map. -/
abbrev affineRingKaehlerModule : ModuleCat.{u} A :=
  CommRingCat.KaehlerDifferential (CommRingCat.ofHom (algebraMap K A))

/-- The map of categorical differential modules induced by actual constants
on an affine open. -/
def affineKaehlerToOpenMap (U : (Opens (PrimeSpectrum.Top A))ᵒᵖ) :
    affineRingKaehlerModule K A ⟶
      (ModuleCat.restrictScalars (StructureSheaf.toOpen A U.unop).hom).obj
        ((affineKaehlerPresheaf K A).obj U) :=
  CommRingCat.KaehlerDifferential.map
    (show (𝟙 (CommRingCat.of K)) ≫
        (schemeConstantsPresheafHom
          (Spec.map (CommRingCat.ofHom (algebraMap K A)))).app U =
      CommRingCat.ofHom (algebraMap K A) ≫ StructureSheaf.toOpen A U.unop by
        simpa only [Category.id_comp] using
          schemeConstantsPresheafHom_specMap (algebraMap K A) U.unop)

theorem affineKaehlerToOpenMap_d (U : (Opens (PrimeSpectrum.Top A))ᵒᵖ) (a : A) :
    affineKaehlerToOpenMap K A U
        (CommRingCat.KaehlerDifferential.d (f := CommRingCat.ofHom (algebraMap K A)) a) =
      CommRingCat.KaehlerDifferential.d (f :=
        (schemeConstantsPresheafHom
          (Spec.map (CommRingCat.ofHom (algebraMap K A)))).app U)
        (StructureSheaf.toOpen A U.unop a) :=
  CommRingCat.KaehlerDifferential.map_d
    (f := CommRingCat.ofHom (algebraMap K A))
    (f' := (schemeConstantsPresheafHom
      (Spec.map (CommRingCat.ofHom (algebraMap K A)))).app U)
    (g := 𝟙 (CommRingCat.of K)) (g' := StructureSheaf.toOpen A U.unop)
    (by simpa only [Category.id_comp] using
      schemeConstantsPresheafHom_specMap (algebraMap K A) U.unop) a

/-- Ring differentials induce a compatible family in all actual open-section
differential modules. -/
def affineKaehlerToPresheaf :
    (Functor.const ((Opens (PrimeSpectrum.Top A))ᵒᵖ)).obj
        (affineRingKaehlerModule K A) ⟶
      affineModulePresheaf (affineKaehlerPresheaf K A) where
  app U := ModuleCat.ofHom
    (Y := (affineModulePresheaf (affineKaehlerPresheaf K A)).obj U)
    { toFun := affineKaehlerToOpenMap K A U
      map_add' := map_add _
      map_smul' := fun a m => by
        exact (affineKaehlerToOpenMap K A U).hom.map_smul a m }
  naturality {U V} i := by
    apply CommRingCat.KaehlerDifferential.ext
    intro a
    change affineKaehlerToOpenMap K A V
        (CommRingCat.KaehlerDifferential.d
          (f := CommRingCat.ofHom (algebraMap K A)) a) =
      (affineKaehlerPresheaf K A).map i
        (affineKaehlerToOpenMap K A U
          (CommRingCat.KaehlerDifferential.d
            (f := CommRingCat.ofHom (algebraMap K A)) a))
    rw [affineKaehlerToOpenMap_d, affineKaehlerToOpenMap_d]
    change CommRingCat.KaehlerDifferential.d (StructureSheaf.toOpen A V.unop a) =
      (affineKaehlerPresheaf K A).map i
        (CommRingCat.KaehlerDifferential.d (StructureSheaf.toOpen A U.unop a))
    exact (PresheafOfModules.DifferentialsConstruction.relativeDifferentials'_map_d
      (schemeConstantsPresheafHom (Spec.map (CommRingCat.ofHom (algebraMap K A))))
      i (StructureSheaf.toOpen A U.unop a)).symm

/-- The compatible family sends `d a` to the differential of the actual
constant regular function `a`. -/
theorem affineKaehlerToPresheaf_d (U : (Opens (PrimeSpectrum.Top A))ᵒᵖ) (a : A) :
    (affineKaehlerToPresheaf K A).app U
        (CommRingCat.KaehlerDifferential.d (f := CommRingCat.ofHom (algebraMap K A)) a) =
      CommRingCat.KaehlerDifferential.d (f :=
        (schemeConstantsPresheafHom
          (Spec.map (CommRingCat.ofHom (algebraMap K A)))).app U)
        (StructureSheaf.toOpen A U.unop a) :=
  affineKaehlerToOpenMap_d K A U a

/-- The actual differential-presheaf map on a principal open is a module localization. -/
theorem affineKaehlerToPresheaf_isLocalizedModule (a : A) :
    IsLocalizedModule (Submonoid.powers a)
      ((affineKaehlerToPresheaf K A).app (op (PrimeSpectrum.basicOpen a))).hom := by
  change IsLocalizedModule (Submonoid.powers a)
    (affineKaehlerToOpenMap K A (op (PrimeSpectrum.basicOpen a))).hom
  exact commRingKaehlerMap_isLocalizedModule
    (CommRingCat.ofHom (algebraMap K A))
    (StructureSheaf.toOpen A (PrimeSpectrum.basicOpen a))
    ((schemeConstantsPresheafHom
      (Spec.map (CommRingCat.ofHom (algebraMap K A)))).app
      (op (PrimeSpectrum.basicOpen a)))
    (by simpa only [Category.id_comp] using
      schemeConstantsPresheafHom_specMap (algebraMap K A) (PrimeSpectrum.basicOpen a))
    (Submonoid.powers a) (StructureSheaf.IsLocalization.to_basicOpen A a)

/-- The genuine stalk of the relative differential presheaf is the corresponding
prime localization of the ring differential module. -/
theorem affineKaehlerPresheaf_stalk_isLocalizedModule (p : PrimeSpectrum.Top A) :
    IsLocalizedModule p.asIdeal.primeCompl
      (affineModuleToStalk (affineKaehlerPresheaf K A)
        (affineRingKaehlerModule K A) (affineKaehlerToPresheaf K A) p).hom :=
  affineModuleToStalk_isLocalizedModule _ _ _
    (affineKaehlerToPresheaf_isLocalizedModule K A) p

/-- Equality of algebra structures identifies their genuine differential modules. -/
def kaehlerModuleIsoOfAlgebraEq (α β : Algebra K A) (h : α = β) :
    (letI := α; ModuleCat.of A Ω[A⁄K]) ≅ (letI := β; ModuleCat.of A Ω[A⁄K]) := by
  subst β
  exact Iso.refl _

omit [Algebra K A] in
/-- Transporting the algebra structure preserves the universal differential. -/
theorem kaehlerModuleIsoOfAlgebraEq_hom_D (α β : Algebra K A) (h : α = β) (a : A) :
    (kaehlerModuleIsoOfAlgebraEq K A α β h).hom (letI := α; KaehlerDifferential.D K A a) =
      (letI := β; KaehlerDifferential.D K A a) := by
  subst β
  rfl

/-- The categorical differential module agrees with the usual Kähler module
for the original algebra structure. -/
def affineRingKaehlerModule_iso : affineRingKaehlerModule K A ≅ ModuleCat.of A Ω[A⁄K] :=
  kaehlerModuleIsoOfAlgebraEq K A (algebraMap K A).toAlgebra inferInstance toAlgebra_algebraMap

/-- The comparison with the ordinary Kähler module preserves the actual universal differential. -/
theorem affineRingKaehlerModule_iso_hom_d (a : A) :
    (affineRingKaehlerModule_iso K A).hom
        (CommRingCat.KaehlerDifferential.d (f := CommRingCat.ofHom (algebraMap K A)) a) =
      KaehlerDifferential.D K A a := by
  exact kaehlerModuleIsoOfAlgebraEq_hom_D K A
    (algebraMap K A).toAlgebra inferInstance toAlgebra_algebraMap a

/-- The inverse comparison also preserves the universal differential. -/
theorem affineRingKaehlerModule_iso_inv_D (a : A) :
    (affineRingKaehlerModule_iso K A).inv (KaehlerDifferential.D K A a) =
      CommRingCat.KaehlerDifferential.d (f := CommRingCat.ofHom (algebraMap K A)) a := by
  have h := congrArg (fun m => (affineRingKaehlerModule_iso K A).inv m)
    (affineRingKaehlerModule_iso_hom_d K A a)
  exact h.symm.trans (ConcreteCategory.congr_hom
    (affineRingKaehlerModule_iso K A).hom_inv_id _)

end EvenQuinticConic
