import EvenQuinticConic.SchemeKaehlerSheaf
import EvenQuinticConic.SchemeKaehlerIsoTransport
import EvenQuinticConic.AffineKaehlerFrames
import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Differential frames on actual affine opens

The affine presentation is over the base ring supplied by the original
scheme morphism. Its structural morphism is identified using the actual
`isoSpec` and `topIso`, before any differential module is transported.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Module

universe u

namespace EvenQuinticConic

variable {K : Type u} [CommRing K] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of K)) (U : X.Opens) (hU : IsAffineOpen U)

/-- Equal actual structure morphisms have the same differential sheaf. -/
def schemeKaehlerSheafCongr {f g : X ⟶ Spec (CommRingCat.of K)} (h : f = g) :
    schemeKaehlerSheaf f ≅ schemeKaehlerSheaf g :=
  eqToIso (congrArg schemeKaehlerSheaf h)

/-- Transport along an equality of structure morphisms preserves the actual differential. -/
theorem schemeKaehlerSheafCongr_hom_derivation
    {f g : X ⟶ Spec (CommRingCat.of K)} (h : f = g)
    (V : X.Opensᵒᵖ) (s : X.presheaf.obj V) :
    (schemeKaehlerSheafCongr h).hom.val.app V ((schemeKaehlerDerivation f).d s) =
      (schemeKaehlerDerivation g).d s := by
  cases h
  rfl

/-- Transport a genuine differential trivialization along equality of structure maps. -/
def schemeKaehlerTrivializationCongr {f g : X ⟶ Spec (CommRingCat.of K)} (h : f = g)
    (e : SheafOfModules.unit X.ringCatSheaf ≅ schemeKaehlerSheaf f) :
    SheafOfModules.unit X.ringCatSheaf ≅ schemeKaehlerSheaf g :=
  e ≪≫ schemeKaehlerSheafCongr h

/-- Transport preserves a differential generator, including equality of its regular function. -/
theorem schemeKaehlerTrivializationCongr_generator
    {f g : X ⟶ Spec (CommRingCat.of K)} (h : f = g)
    (e : SheafOfModules.unit X.ringCatSheaf ≅ schemeKaehlerSheaf f)
    (V : X.Opens) (s t : Γ(X, V))
    (he : e.hom.val.app (op V) (1 : Γ(X, V)) = (schemeKaehlerDerivation f).d s)
    (hst : s = t) :
    (schemeKaehlerTrivializationCongr h e).hom.val.app (op V)
      (1 : Γ(X, V)) = (schemeKaehlerDerivation g).d t := by
  cases h
  cases hst
  simpa only [schemeKaehlerTrivializationCongr, schemeKaehlerSheafCongr,
    Iso.trans_refl] using he

/-- A differential trivialization and its generator formula travel together
through equal structure maps and equal regular functions. -/
def schemeKaehlerTrivializationCongrData
    {f g : X ⟶ Spec (CommRingCat.of K)} (h : f = g)
    (e : SheafOfModules.unit X.ringCatSheaf ≅ schemeKaehlerSheaf f)
    (V : X.Opens) (s t : Γ(X, V))
    (he : e.hom.val.app (op V) (1 : Γ(X, V)) = (schemeKaehlerDerivation f).d s)
    (hst : s = t) :
    { e' : SheafOfModules.unit X.ringCatSheaf ≅ schemeKaehlerSheaf g //
      e'.hom.val.app (op V) (1 : Γ(X, V)) = (schemeKaehlerDerivation g).d t } :=
  ⟨schemeKaehlerTrivializationCongr h e,
    schemeKaehlerTrivializationCongr_generator h e V s t he hst⟩

/-- The affine chart of an open subscheme carries exactly the base-ring
structure induced by the original scheme morphism. -/
theorem affineOpen_structure_eq :
    U.ι ≫ f = hU.isoSpec.hom ≫
      Spec.map ((schemeConstantsPresheafHom f).app (op U)) := by
  apply ext_of_isAffine
  rw [Scheme.comp_appTop, Scheme.comp_appTop, hU.isoSpec_hom_appTop,
    Scheme.ΓSpecIso_naturality_assoc]
  dsimp only [schemeConstantsPresheafHom, Functor.const_obj_obj]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [Scheme.Opens.ι_appTop, Scheme.Opens.topIso_inv, ← Functor.map_comp]
  rfl

/-- A coordinate-ring element pulled back through the genuine affine chart
is its actual top section on the open subscheme. -/
theorem affineOpen_isoSpec_toOpen (s : Γ(X, U)) :
    (hU.isoSpec.hom.appIso ⊤).hom
      (StructureSheaf.toOpen Γ(X, U) (hU.isoSpec.hom ''ᵁ ⊤) s) =
        U.topIso.inv s := by
  have h : hU.isoSpec.hom.appTop ≫ (hU.isoSpec.hom.appIso ⊤).inv =
      (Spec Γ(X, U)).presheaf.map
        (homOfLE (show hU.isoSpec.hom ''ᵁ ⊤ ≤ ⊤ from le_top)).op := by
    simpa [Scheme.Hom.appLE] using
      Scheme.Hom.appLE_appIso_inv hU.isoSpec.hom
        (show (⊤ : U.toScheme.Opens) ≤ hU.isoSpec.hom ⁻¹ᵁ ⊤ from le_top)
  have hp : StructureSheaf.toOpen Γ(X, U) (hU.isoSpec.hom ''ᵁ ⊤) ≫
      (hU.isoSpec.hom.appIso ⊤).hom = U.topIso.inv := by
    rw [Scheme.toOpen_eq, ← h]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hU.isoSpec_hom_appTop, Iso.inv_hom_id_assoc]
  exact ConcreteCategory.congr_hom hp s

/-- Transport an affine differential basis along an actual open immersion. -/
def affineKaehlerBasisOpenImageTrivialization
    {A : Type u} [CommRing A] [Algebra K A] {Y : Scheme.{u}}
    (i : Y ⟶ Spec (CommRingCat.of A)) [IsOpenImmersion i]
    (b : Basis Unit A Ω[A⁄K]) :
    SheafOfModules.unit Y.ringCatSheaf ≅
      schemeKaehlerSheaf (i ≫ Spec.map (CommRingCat.ofHom (algebraMap K A))) :=
  schemeModuleOpenImageUnitIso i ≪≫
    (schemeModuleOpenImage i).mapIso (affineKaehlerBasisTrivialization b) ≪≫
    (schemeKaehlerOpenImageIso i
      (Spec.map (CommRingCat.ofHom (algebraMap K A)))).symm

/-- Open-immersion transport preserves the specified actual differential generator. -/
theorem affineKaehlerBasisOpenImageTrivialization_one
    {A : Type u} [CommRing A] [Algebra K A] {Y : Scheme.{u}}
    (i : Y ⟶ Spec (CommRingCat.of A)) [IsOpenImmersion i]
    (b : Basis Unit A Ω[A⁄K]) (a : A) (hb : b () = KaehlerDifferential.D K A a)
    (V : Y.Opens) :
    (affineKaehlerBasisOpenImageTrivialization i b).hom.val.app (op V) (1 : Γ(Y, V)) =
      (schemeKaehlerDerivation (i ≫ Spec.map (CommRingCat.ofHom (algebraMap K A)))).d
        ((i.appIso V).hom (StructureSheaf.toOpen A (i ''ᵁ V) a)) := by
  change (schemeKaehlerOpenImageIso i
    (Spec.map (CommRingCat.ofHom (algebraMap K A)))).inv.val.app (op V)
      ((affineKaehlerBasisTrivialization (K := K) (A := A) b).hom.val.app
        (op (i ''ᵁ V)) ((i.appIso V).inv 1)) = _
  rw [map_one, affineKaehlerBasisTrivialization_hom_apply_of_basis_D
    (K := K) (A := A) b a hb (i ''ᵁ V) 1, one_smul]
  exact schemeKaehlerOpenImageIso_inv_derivation i
    (Spec.map (CommRingCat.ofHom (algebraMap K A))) V
    (StructureSheaf.toOpen A (i ''ᵁ V) a)

/-- An actual differential-module basis on an affine open gives a
trivialization of the actual differential sheaf on its open subscheme. -/
def affineOpenKaehlerBasisTrivialization
    (b : Basis Unit Γ(X, U) ((schemeKaehlerPresheaf f).obj (op U))) :
    SheafOfModules.unit U.toScheme.ringCatSheaf ≅
      schemeKaehlerSheaf (U.ι ≫ f) := by
  letI : Algebra K Γ(X, U) := ((schemeConstantsPresheafHom f).app (op U)).hom.toAlgebra
  have hbase : U.ι ≫ f = hU.isoSpec.hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap K Γ(X, U))) :=
    affineOpen_structure_eq f U hU
  exact schemeKaehlerTrivializationCongr (K := K) (X := U.toScheme) hbase.symm
    (affineKaehlerBasisOpenImageTrivialization (K := K) (A := Γ(X, U))
      (Y := U.toScheme) hU.isoSpec.hom b)

set_option maxHeartbeats 300000 in
/-- A proved actual differential trivialization, bundled with its precise generator formula. -/
def affineOpenKaehlerBasisDifferentialTrivialization
    (b : Basis Unit Γ(X, U) ((schemeKaehlerPresheaf f).obj (op U)))
    (s : Γ(X, U)) (hb : b () = CommRingCat.KaehlerDifferential.d s) :
    { e : SheafOfModules.unit U.toScheme.ringCatSheaf ≅
        schemeKaehlerSheaf (U.ι ≫ f) //
      e.hom.val.app (op ⊤) (1 : Γ(U.toScheme, ⊤)) =
        (schemeKaehlerDerivation (U.ι ≫ f)).d (U.topIso.inv s) } := by
  letI : Algebra K Γ(X, U) := ((schemeConstantsPresheafHom f).app (op U)).hom.toAlgebra
  have hbase : U.ι ≫ f = hU.isoSpec.hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap K Γ(X, U))) :=
    affineOpen_structure_eq f U hU
  change b () = KaehlerDifferential.D K Γ(X, U) s at hb
  let e := affineKaehlerBasisOpenImageTrivialization (K := K) (A := Γ(X, U))
    (Y := U.toScheme) hU.isoSpec.hom b
  have hgen := affineKaehlerBasisOpenImageTrivialization_one
    (K := K) (A := Γ(X, U)) (Y := U.toScheme) hU.isoSpec.hom b s hb ⊤
  have hcoord := affineOpen_isoSpec_toOpen U hU s
  exact schemeKaehlerTrivializationCongrData (K := K) (X := U.toScheme)
    (f := hU.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap K Γ(X, U))))
    (g := U.ι ≫ f) hbase.symm e
    ⊤ ((hU.isoSpec.hom.appIso ⊤).hom
      (StructureSheaf.toOpen Γ(X, U) (hU.isoSpec.hom ''ᵁ ⊤) s)) (U.topIso.inv s)
    hgen hcoord

end EvenQuinticConic
