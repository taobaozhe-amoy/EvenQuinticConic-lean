import EvenQuinticConic.AffineKaehlerComparison
import EvenQuinticConic.SheafTrivialization
import Mathlib.Algebra.Module.LocalizedModule.IsLocalization

/-!
# Genuine module-sheaf frames from rank-one affine module frames

A linear equivalence `A ≃ₗ[A] M` induces an actual isomorphism from the
structure module sheaf on `Spec A` to `M.tilde`. The map is multiplication
by the locally fractional section supplied by the vector corresponding to
`1`. Its invertibility is proved on actual stalk maps using principal-open
localizations, without an assumption about sections on arbitrary opens.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Module

namespace EvenQuinticConic

universe u

variable {A : Type u} [CommRing A]

/-- Actual constant regular functions, as a compatible family in the
structure module presheaf with scalars restricted to the affine ring. -/
def affineStructureModuleToPresheaf :
    (Functor.const ((Opens (PrimeSpectrum.Top A))ᵒᵖ)).obj (ModuleCat.of A A) ⟶
      affineModulePresheaf
        (SheafOfModules.unit (Spec (CommRingCat.of A)).ringCatSheaf).val where
  app U := ModuleCat.ofHom
    (Y := (affineModulePresheaf
      (SheafOfModules.unit (Spec (CommRingCat.of A)).ringCatSheaf).val).obj U)
    { toFun := StructureSheaf.toOpen A U.unop
      map_add' := map_add _
      map_smul' := fun a b => by
        change StructureSheaf.toOpen A U.unop (a * b) =
          StructureSheaf.toOpen A U.unop a * StructureSheaf.toOpen A U.unop b
        exact map_mul _ a b }
  naturality {U V} i := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    change StructureSheaf.toOpen A V.unop a =
      (Spec.structureSheaf A).val.map i (StructureSheaf.toOpen A U.unop a)
    exact (ConcreteCategory.congr_hom (StructureSheaf.toOpen_res A U.unop V.unop i.unop) a).symm

/-- On every principal open, the structure module map is the genuine
localization of the affine ring viewed as a module over itself. -/
theorem affineStructureModuleToPresheaf_isLocalizedModule (a : A) :
    IsLocalizedModule (Submonoid.powers a)
      ((affineStructureModuleToPresheaf (A := A)).app
        (op (PrimeSpectrum.basicOpen a))).hom := by
  change IsLocalizedModule (Submonoid.powers a)
    (Algebra.linearMap A ((Spec.structureSheaf A).val.obj (op (PrimeSpectrum.basicOpen a))))
  infer_instance

variable (M : ModuleCat.{u} A)

/-- An affine module element as a section of the actual associated module sheaf. -/
def tildeAffineSection (U : Opens (PrimeSpectrum.Top A)) (m : M) :
    M.tilde.val.obj (op U) := ModuleCat.Tilde.toOpen M U m

/-- The actual sheaf morphism specified by a rank-one affine module frame. -/
def tildeUnitHom (e : A ≃ₗ[A] M) :
    SheafOfModules.unit (Spec (CommRingCat.of A)).ringCatSheaf ⟶ M.tilde :=
  sectionToModuleHom (moduleGlobalSectionFamily M.tilde
    (ModuleCat.Tilde.toOpen M ⊤ (e 1)))

/-- On every open, the map is multiplication by the actual locally
fractional section corresponding to the chosen affine vector. -/
theorem tildeUnitHom_apply (e : A ≃ₗ[A] M)
    (U : Opens (PrimeSpectrum.Top A)) (r : (Spec.structureSheaf A).val.obj (op U)) :
    (tildeUnitHom M e).val.app (op U) r =
      r • tildeAffineSection M U (e 1) := by
  change r • (M.tilde.val.map (homOfLE le_top : U ⟶ ⊤).op
    (tildeAffineSection M ⊤ (e 1))) = _
  congr 1


/-- An affine rank-one module frame gives an isomorphism of actual sheaves.
The proof uses the genuine localization description of both stalks. -/
theorem tildeUnitHom_isIso (e : A ≃ₗ[A] M) : IsIso (tildeUnitHom M e) := by
  apply affineSheafHom_isIso_of_presentation_stalk_bijective
    (𝟙 (SheafOfModules.unit (Spec (CommRingCat.of A)).ringCatSheaf).val)
  intro p
  simp only [Category.id_comp]
  apply affineModulePresheafMap_tilde_stalk_bijective
    (ModuleCat.of A A) M affineStructureModuleToPresheaf
    affineStructureModuleToPresheaf_isLocalizedModule e.toModuleIso
  intro a
  calc
    _ = (StructureSheaf.toOpen A ⊤ a) • tildeAffineSection M ⊤ (e 1) :=
      tildeUnitHom_apply M e ⊤ (StructureSheaf.toOpen A ⊤ a)
    _ = _ := by
      change a • ModuleCat.Tilde.toOpen M ⊤ (e 1) = ModuleCat.Tilde.toOpen M ⊤ (e a)
      rw [← map_smul]
      congr 1
      simpa using (e.map_smul a (1 : A)).symm

/-- Actual structure-module trivialization of the associated module sheaf. -/
def tildeUnitIso (e : A ≃ₗ[A] M) :
    SheafOfModules.unit (Spec (CommRingCat.of A)).ringCatSheaf ≅ M.tilde := by
  letI := tildeUnitHom_isIso M e
  exact asIso (tildeUnitHom M e)

/-- The sheaf isomorphism preserves the explicit coefficient formula. -/
theorem tildeUnitIso_hom_apply (e : A ≃ₗ[A] M)
    (U : Opens (PrimeSpectrum.Top A)) (r : (Spec.structureSheaf A).val.obj (op U)) :
    (tildeUnitIso M e).hom.val.app (op U) r =
      r • tildeAffineSection M U (e 1) := tildeUnitHom_apply M e U r

/-- A one-element basis supplies the coefficient-to-module linear equivalence. -/
def basisUnitLinearEquiv (b : Basis Unit A M) : A ≃ₗ[A] M :=
  (LinearEquiv.funUnique Unit A A).symm.trans b.equivFun.symm

/-- Coefficients act on the actual basis vector. -/
theorem basisUnitLinearEquiv_apply (b : Basis Unit A M) (a : A) :
    basisUnitLinearEquiv M b a = a • b () := by
  simp [basisUnitLinearEquiv]

/-- A one-element affine basis gives an actual associated-sheaf trivialization. -/
def tildeBasisUnitIso (b : Basis Unit A M) :
    SheafOfModules.unit (Spec (CommRingCat.of A)).ringCatSheaf ≅ M.tilde :=
  tildeUnitIso M (basisUnitLinearEquiv M b)

/-- The basis-induced isomorphism acts by multiplication on every open,
including opens which are not affine. -/
theorem tildeBasisUnitIso_hom_apply (b : Basis Unit A M)
    (U : Opens (PrimeSpectrum.Top A)) (r : (Spec.structureSheaf A).val.obj (op U)) :
    (tildeBasisUnitIso M b).hom.val.app (op U) r =
      r • tildeAffineSection M U (b ()) := by
  have h := tildeUnitIso_hom_apply M (basisUnitLinearEquiv M b) U r
  simpa only [tildeBasisUnitIso, basisUnitLinearEquiv_apply, one_smul] using h

/-- The coefficient coordinate of the actual associated module sheaf on
an arbitrary open, obtained by evaluating the genuine sheaf isomorphism. -/
def tildeBasisCoordinate (b : Basis Unit A M) (U : Opens (PrimeSpectrum.Top A)) :
    M.tilde.val.obj (op U) ≃ₗ[(Spec (CommRingCat.of A)).ringCatSheaf.val.obj (op U)]
      (Spec (CommRingCat.of A)).ringCatSheaf.val.obj (op U) :=
  ((SheafOfModules.evaluation (Spec (CommRingCat.of A)).ringCatSheaf (op U)).mapIso
    (tildeBasisUnitIso M b)).toLinearEquiv.symm

/-- The coordinate recovers the coefficient of the specified affine basis section. -/
theorem tildeBasisCoordinate_smul_section (b : Basis Unit A M)
    (U : Opens (PrimeSpectrum.Top A)) (r : (Spec.structureSheaf A).val.obj (op U)) :
    tildeBasisCoordinate M b U (r • tildeAffineSection M U (b ())) = r := by
  let E := ((SheafOfModules.evaluation
    (Spec (CommRingCat.of A)).ringCatSheaf (op U)).mapIso
      (tildeBasisUnitIso M b)).toLinearEquiv
  change E.symm (r • tildeAffineSection M U (b ())) = r
  calc
    _ = E.symm (E r) := congrArg E.symm (tildeBasisUnitIso_hom_apply M b U r).symm
    _ = r := E.symm_apply_apply r

/-- These coordinates commute with restriction on every inclusion of opens. -/
theorem tildeBasisCoordinate_restrict (b : Basis Unit A M)
    {U V : Opens (PrimeSpectrum.Top A)} (i : V ⟶ U) (s : M.tilde.val.obj (op U)) :
    tildeBasisCoordinate M b V (M.tilde.val.map i.op s) =
      (Spec.structureSheaf A).val.map i.op (tildeBasisCoordinate M b U s) :=
  PresheafOfModules.naturality_apply (tildeBasisUnitIso M b).inv.val i.op s

end EvenQuinticConic
