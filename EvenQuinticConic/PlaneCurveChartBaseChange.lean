import EvenQuinticConic.PlaneCurveAffineEquation
import EvenQuinticConic.PlaneEquationBaseChange
import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Actual base change of standard plane-curve charts

The coefficient-extended equation algebra represents the categorical base
change of each actual standard open. Both projection identities use the
original chart coordinates and the original coefficient-field structure.
-/

noncomputable section
namespace EvenQuinticConic

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

variable {K L : Type} [Field K] [Field L] [Algebra K L]

/-- The spectrum of the extended literal equation algebra is the genuine
base change of the spectrum of the original literal equation algebra. -/
def planeEquationBaseChangeSpecIso (F : PlanePolynomial K) (i : Fin 3) :
    pullback
      (Spec.map (CommRingCat.ofHom (algebraMap K (PlaneEquationAlgebra F i))))
      (Spec.map (CommRingCat.ofHom (algebraMap K L))) ≅
    Spec (CommRingCat.of
      (PlaneEquationAlgebra (MvPolynomial.map (algebraMap K L) F) i)) :=
  pullbackSymmetry _ _ ≪≫
    pullbackSpecIso K L (PlaneEquationAlgebra F i) ≪≫
    Scheme.Spec.mapIso
      (planeEquationBaseChangeEquiv (S := L) F i).toRingEquiv.symm.toCommRingCatIso.op

/-- The first projection is the literal coefficient map on equation classes. -/
@[reassoc (attr := simp)]
theorem planeEquationBaseChangeSpecIso_inv_fst (F : PlanePolynomial K) (i : Fin 3) :
    (planeEquationBaseChangeSpecIso (L := L) F i).inv ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (planeEquationCoefficientMap (S := L) F i).toRingHom) := by
  change Spec.map (CommRingCat.ofHom (planeEquationBaseChangeEquiv (S := L) F i).toRingHom) ≫
    (pullbackSpecIso K L (PlaneEquationAlgebra F i)).inv ≫
      (pullbackSymmetry _ _).inv ≫ pullback.fst _ _ = _
  rw [pullbackSymmetry_inv_comp_fst, pullbackSpecIso_inv_snd, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact congrArg AlgHom.toRingHom (planeEquationBaseChangeEquiv_includeRight (S := L) F i)

/-- The second projection is the extended coefficient-field structure. -/
@[reassoc (attr := simp)]
theorem planeEquationBaseChangeSpecIso_inv_snd (F : PlanePolynomial K) (i : Fin 3) :
    (planeEquationBaseChangeSpecIso (L := L) F i).inv ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom
        (algebraMap L (PlaneEquationAlgebra (MvPolynomial.map (algebraMap K L) F) i))) := by
  change Spec.map (CommRingCat.ofHom (planeEquationBaseChangeEquiv (S := L) F i).toRingHom) ≫
    (pullbackSpecIso K L (PlaneEquationAlgebra F i)).inv ≫
      (pullbackSymmetry _ _).inv ≫ pullback.snd _ _ = _
  rw [pullbackSymmetry_inv_comp_snd, pullbackSpecIso_inv_fst, ← Spec.map_comp]
  congr 1
  ext l
  exact (planeEquationBaseChangeEquiv (S := L) F i).commutes l

@[reassoc (attr := simp)]
theorem planeEquationBaseChangeSpecIso_hom_fst (F : PlanePolynomial K) (i : Fin 3) :
    (planeEquationBaseChangeSpecIso (L := L) F i).hom ≫
      Spec.map (CommRingCat.ofHom (planeEquationCoefficientMap (S := L) F i).toRingHom) =
    pullback.fst _ _ := by
  rw [← planeEquationBaseChangeSpecIso_inv_fst (L := L) F i, Iso.hom_inv_id_assoc]

@[reassoc (attr := simp)]
theorem planeEquationBaseChangeSpecIso_hom_snd (F : PlanePolynomial K) (i : Fin 3) :
    (planeEquationBaseChangeSpecIso (L := L) F i).hom ≫
      Spec.map (CommRingCat.ofHom
        (algebraMap L (PlaneEquationAlgebra (MvPolynomial.map (algebraMap K L) F) i))) =
    pullback.snd _ _ := by
  rw [← planeEquationBaseChangeSpecIso_inv_snd (L := L) F i, Iso.hom_inv_id_assoc]

/-- Base change of the actual chart-to-equation presentation, over the
unchanged original coefficient field. -/
def planeCurveChartBaseChangePresentationIso
    (F : PlanePolynomial K) (d : ℕ) (hF : F.IsHomogeneous d)
    (hFdeg : 1 < F.totalDegree) (hprime : (Ideal.span {F}).IsPrime) (i : Fin 3) :
    pullback ((planeCurveCoordinateOpen F i).ι ≫ planeCurveStructure F)
      (Spec.map (CommRingCat.ofHom (algebraMap K L))) ≅
    pullback
      (Spec.map (CommRingCat.ofHom (algebraMap K (PlaneEquationAlgebra F i))))
      (Spec.map (CommRingCat.ofHom (algebraMap K L))) :=
  asIso (pullback.map _ _ _ _
    (planeCurveAffineEquationIsoSpec F d hF hFdeg hprime i).hom (𝟙 _) (𝟙 _)
    (by simpa only [Category.comp_id] using
      (planeCurveAffineEquationIsoSpec_hom_comp_structure F d hF hFdeg hprime i).symm)
    (by simp))

/-- The genuine categorical base change of the actual standard open is
precisely the spectrum of its coefficient-extended affine equation. -/
def planeCurveChartBaseChangeIsoSpec
    (F : PlanePolynomial K) (d : ℕ) (hF : F.IsHomogeneous d)
    (hFdeg : 1 < F.totalDegree) (hprime : (Ideal.span {F}).IsPrime) (i : Fin 3) :
    pullback ((planeCurveCoordinateOpen F i).ι ≫ planeCurveStructure F)
      (Spec.map (CommRingCat.ofHom (algebraMap K L))) ≅
    Spec (CommRingCat.of
      (PlaneCurveAffineEquationAlgebra (MvPolynomial.map (algebraMap K L) F) i)) :=
  planeCurveChartBaseChangePresentationIso (L := L) F d hF hFdeg hprime i ≪≫
    planeEquationBaseChangeSpecIso (L := L) F i

/-- The chart base-change comparison retains the actual original chart map. -/
@[reassoc (attr := simp)]
theorem planeCurveChartBaseChangeIsoSpec_hom_fst
    (F : PlanePolynomial K) (d : ℕ) (hF : F.IsHomogeneous d)
    (hFdeg : 1 < F.totalDegree) (hprime : (Ideal.span {F}).IsPrime) (i : Fin 3) :
    (planeCurveChartBaseChangeIsoSpec (L := L) F d hF hFdeg hprime i).hom ≫
      Spec.map (CommRingCat.ofHom (planeEquationCoefficientMap (S := L) F i).toRingHom) ≫
        (planeCurveAffineEquationIsoSpec F d hF hFdeg hprime i).inv =
    pullback.fst _ _ := by
  unfold planeCurveChartBaseChangeIsoSpec
  rw [Iso.trans_hom, Category.assoc,
    planeEquationBaseChangeSpecIso_hom_fst_assoc]
  simp [planeCurveChartBaseChangePresentationIso]

/-- The chart base-change comparison is over the actual extended field. -/
@[reassoc (attr := simp)]
theorem planeCurveChartBaseChangeIsoSpec_hom_snd
    (F : PlanePolynomial K) (d : ℕ) (hF : F.IsHomogeneous d)
    (hFdeg : 1 < F.totalDegree) (hprime : (Ideal.span {F}).IsPrime) (i : Fin 3) :
    (planeCurveChartBaseChangeIsoSpec (L := L) F d hF hFdeg hprime i).hom ≫
      Spec.map (CommRingCat.ofHom
        (algebraMap L (PlaneCurveAffineEquationAlgebra
          (MvPolynomial.map (algebraMap K L) F) i))) =
    pullback.snd _ _ := by
  unfold planeCurveChartBaseChangeIsoSpec
  rw [Iso.trans_hom, Category.assoc, planeEquationBaseChangeSpecIso_hom_snd]
  simp [planeCurveChartBaseChangePresentationIso]

/-- The inverse comparison also preserves the actual original chart projection. -/
@[reassoc (attr := simp)]
theorem planeCurveChartBaseChangeIsoSpec_inv_fst
    (F : PlanePolynomial K) (d : ℕ) (hF : F.IsHomogeneous d)
    (hFdeg : 1 < F.totalDegree) (hprime : (Ideal.span {F}).IsPrime) (i : Fin 3) :
    (planeCurveChartBaseChangeIsoSpec (L := L) F d hF hFdeg hprime i).inv ≫
      pullback.fst _ _ =
    Spec.map (CommRingCat.ofHom (planeEquationCoefficientMap (S := L) F i).toRingHom) ≫
      (planeCurveAffineEquationIsoSpec F d hF hFdeg hprime i).inv := by
  rw [← planeCurveChartBaseChangeIsoSpec_hom_fst (L := L) F d hF hFdeg hprime i,
    Iso.inv_hom_id_assoc]

/-- The inverse comparison retains the extended coefficient-field structure. -/
@[reassoc (attr := simp)]
theorem planeCurveChartBaseChangeIsoSpec_inv_snd
    (F : PlanePolynomial K) (d : ℕ) (hF : F.IsHomogeneous d)
    (hFdeg : 1 < F.totalDegree) (hprime : (Ideal.span {F}).IsPrime) (i : Fin 3) :
    (planeCurveChartBaseChangeIsoSpec (L := L) F d hF hFdeg hprime i).inv ≫
      pullback.snd _ _ =
    Spec.map (CommRingCat.ofHom
      (algebraMap L (PlaneCurveAffineEquationAlgebra
        (MvPolynomial.map (algebraMap K L) F) i))) := by
  rw [← planeCurveChartBaseChangeIsoSpec_hom_snd (L := L) F d hF hFdeg hprime i,
    Iso.inv_hom_id_assoc]

/-- The extended equation spectrum, with the proved coordinate and scalar
maps, forms the actual chart base-change square. -/
theorem planeCurveChartBaseChange_isPullback
    (F : PlanePolynomial K) (d : ℕ) (hF : F.IsHomogeneous d)
    (hFdeg : 1 < F.totalDegree) (hprime : (Ideal.span {F}).IsPrime) (i : Fin 3) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (planeEquationCoefficientMap (S := L) F i).toRingHom) ≫
        (planeCurveAffineEquationIsoSpec F d hF hFdeg hprime i).inv)
      (Spec.map (CommRingCat.ofHom
        (algebraMap L (PlaneCurveAffineEquationAlgebra
          (MvPolynomial.map (algebraMap K L) F) i))))
      ((planeCurveCoordinateOpen F i).ι ≫ planeCurveStructure F)
      (Spec.map (CommRingCat.ofHom (algebraMap K L))) := by
  exact (IsPullback.of_hasPullback _ _).of_iso
    (planeCurveChartBaseChangeIsoSpec (L := L) F d hF hFdeg hprime i)
    (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simpa only [Iso.refl_hom, Category.comp_id, Category.assoc] using
      (planeCurveChartBaseChangeIsoSpec_hom_fst (L := L) F d hF hFdeg hprime i).symm)
    (by simp) (by simp) (by simp)

/-- A domain literal equation algebra implies integrality of the actual
chart base change, via the constructed scheme isomorphism. -/
theorem planeCurveChartBaseChange_isIntegral
    (F : PlanePolynomial K) (d : ℕ) (hF : F.IsHomogeneous d)
    (hFdeg : 1 < F.totalDegree) (hprime : (Ideal.span {F}).IsPrime) (i : Fin 3)
    [IsDomain (PlaneCurveAffineEquationAlgebra (MvPolynomial.map (algebraMap K L) F) i)] :
    IsIntegral (pullback ((planeCurveCoordinateOpen F i).ι ≫ planeCurveStructure F)
      (Spec.map (CommRingCat.ofHom (algebraMap K L)))) := by
  let e := planeCurveChartBaseChangeIsoSpec (L := L) F d hF hFdeg hprime i
  letI : Nonempty (pullback ((planeCurveCoordinateOpen F i).ι ≫ planeCurveStructure F)
      (Spec.map (CommRingCat.ofHom (algebraMap K L))) : Scheme) :=
    ⟨e.inv.base (Classical.choice
      (inferInstance : Nonempty (Spec (CommRingCat.of
        (PlaneCurveAffineEquationAlgebra (MvPolynomial.map (algebraMap K L) F) i)))))⟩
  exact isIntegral_of_isOpenImmersion e.hom

end EvenQuinticConic
