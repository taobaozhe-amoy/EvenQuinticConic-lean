import EvenQuinticConic.TildeModuleFrames

/-!
# Genuine affine differential-sheaf trivializations

A one-element basis of the actual Kähler module over an affine ring produces
an isomorphism with the actual differential sheaf on its spectrum. The
comparison is the proved canonical affine comparison, and its generator
formula identifies a basis vector `D a` with the genuine differential of
the regular function induced by `a` on every open.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Module KaehlerDifferential

namespace EvenQuinticConic

universe u

variable {K A : Type u} [CommRing K] [CommRing A] [Algebra K A]

/-- The genuine differential-sheaf section associated to an affine Kähler vector. -/
def affineKaehlerSection (U : Opens (PrimeSpectrum.Top A)) (m : Ω[A⁄K]) :
    (schemeKaehlerSheaf (Spec.map (CommRingCat.ofHom (algebraMap K A)))).val.obj (op U) :=
  (affineKaehlerSheafIso (K := K) (A := A)).inv.val.app (op U)
    (tildeAffineSection (ModuleCat.of A Ω[A⁄K]) U m)

/-- A vector which is an actual universal differential becomes the genuine
sheaf differential of the associated regular function, on every open. -/
theorem affineKaehlerSection_D (U : Opens (PrimeSpectrum.Top A)) (a : A) :
    affineKaehlerSection (K := K) U (D K A a) =
      (schemeKaehlerDerivation (Spec.map (CommRingCat.ofHom (algebraMap K A)))).d
        (StructureSheaf.toOpen A U a) := by
  let E := ((SheafOfModules.evaluation
    (Spec (CommRingCat.of A)).ringCatSheaf (op U)).mapIso
      (affineKaehlerSheafIso (K := K) (A := A))).toLinearEquiv
  apply E.injective
  change E (E.symm (tildeAffineSection (ModuleCat.of A Ω[A⁄K]) U (D K A a))) = _
  rw [LinearEquiv.apply_symm_apply]
  exact ((affineKaehlerSheafIso_hom_derivation (K := K) U
    (StructureSheaf.toOpen A U a)).trans
      (affineKaehlerDifferential_toOpen (K := K) U a)).symm

/-- An actual rank-one Kähler basis trivializes the actual affine
relative differential sheaf. -/
def affineKaehlerBasisTrivialization (b : Basis Unit A Ω[A⁄K]) :
    SheafOfModules.unit (Spec (CommRingCat.of A)).ringCatSheaf ≅
      schemeKaehlerSheaf (Spec.map (CommRingCat.ofHom (algebraMap K A))) :=
  tildeBasisUnitIso (ModuleCat.of A Ω[A⁄K]) b ≪≫
    (affineKaehlerSheafIso (K := K) (A := A)).symm

/-- The actual differential-sheaf trivialization acts by multiplication by
its specified section on every open, not only the affine basic opens. -/
theorem affineKaehlerBasisTrivialization_hom_apply (b : Basis Unit A Ω[A⁄K])
    (U : Opens (PrimeSpectrum.Top A)) (r : (Spec.structureSheaf A).val.obj (op U)) :
    (affineKaehlerBasisTrivialization b).hom.val.app (op U) r =
      r • affineKaehlerSection (K := K) U (b ()) := by
  change (affineKaehlerSheafIso (K := K) (A := A)).inv.val.app (op U)
    ((tildeBasisUnitIso (ModuleCat.of A Ω[A⁄K]) b).hom.val.app (op U) r) = _
  rw [tildeBasisUnitIso_hom_apply (ModuleCat.of A Ω[A⁄K]) b U r]
  exact ((affineKaehlerSheafIso (K := K) (A := A)).inv.val.app (op U)).hom.map_smul r _

/-- If the affine basis generator is `D a`, the sheaf trivialization sends
each regular coefficient to that coefficient times the actual differential
of `a`. No section-ring identification on the open is assumed. -/
theorem affineKaehlerBasisTrivialization_hom_apply_of_basis_D
    (b : Basis Unit A Ω[A⁄K]) (a : A) (hb : b () = D K A a)
    (U : Opens (PrimeSpectrum.Top A)) (r : (Spec.structureSheaf A).val.obj (op U)) :
    (affineKaehlerBasisTrivialization b).hom.val.app (op U) r =
      r • (schemeKaehlerDerivation (Spec.map (CommRingCat.ofHom (algebraMap K A)))).d
        (StructureSheaf.toOpen A U a) := by
  rw [affineKaehlerBasisTrivialization_hom_apply b U r, hb, affineKaehlerSection_D]

/-- The actual affine differential-sheaf coordinate on an arbitrary open. -/
def affineKaehlerBasisCoordinate (b : Basis Unit A Ω[A⁄K])
    (U : Opens (PrimeSpectrum.Top A)) :
    (schemeKaehlerSheaf (Spec.map (CommRingCat.ofHom (algebraMap K A)))).val.obj (op U) ≃ₗ[
      (Spec (CommRingCat.of A)).ringCatSheaf.val.obj (op U)]
      (Spec (CommRingCat.of A)).ringCatSheaf.val.obj (op U) :=
  ((SheafOfModules.evaluation (Spec (CommRingCat.of A)).ringCatSheaf (op U)).mapIso
    (affineKaehlerBasisTrivialization b)).toLinearEquiv.symm

/-- The actual coordinate recovers the coefficient of the specified generator. -/
theorem affineKaehlerBasisCoordinate_smul_section (b : Basis Unit A Ω[A⁄K])
    (U : Opens (PrimeSpectrum.Top A)) (r : (Spec.structureSheaf A).val.obj (op U)) :
    affineKaehlerBasisCoordinate b U (r • affineKaehlerSection (K := K) U (b ())) = r := by
  let E := ((SheafOfModules.evaluation
    (Spec (CommRingCat.of A)).ringCatSheaf (op U)).mapIso
      (affineKaehlerBasisTrivialization b)).toLinearEquiv
  change E.symm (r • affineKaehlerSection (K := K) U (b ())) = r
  calc
    _ = E.symm (E r) := congrArg E.symm
      (affineKaehlerBasisTrivialization_hom_apply b U r).symm
    _ = r := E.symm_apply_apply r

/-- The coordinates commute with actual restrictions of the differential
sheaf and of the structure sheaf. -/
theorem affineKaehlerBasisCoordinate_restrict (b : Basis Unit A Ω[A⁄K])
    {U V : Opens (PrimeSpectrum.Top A)} (i : V ⟶ U)
    (s : (schemeKaehlerSheaf
      (Spec.map (CommRingCat.ofHom (algebraMap K A)))).val.obj (op U)) :
    affineKaehlerBasisCoordinate b V
        ((schemeKaehlerSheaf (Spec.map (CommRingCat.ofHom (algebraMap K A)))).val.map i.op s) =
      (Spec.structureSheaf A).val.map i.op (affineKaehlerBasisCoordinate b U s) :=
  PresheafOfModules.naturality_apply (affineKaehlerBasisTrivialization b).inv.val i.op s

end EvenQuinticConic
