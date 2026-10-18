import EvenQuinticConic.PlaneChartPolynomialMap
import EvenQuinticConic.IncidenceDehomogenization

/-!
# Literal affine equation presentations of actual plane-curve charts

For a homogeneous prime equation of degree greater than one, each actual
standard affine chart has exactly the dehomogenized equation as its kernel.
The resulting algebra and scheme isomorphisms use actual coordinate-ratio
sections and preserve the original coefficient-field structure morphism.
-/

noncomputable section

namespace EvenQuinticConic

open AlgebraicGeometry CategoryTheory MvPolynomial Incidence

variable {K : Type} [Field K]

/-- The literal two-variable equation algebra of the chosen projective chart. -/
abbrev PlaneCurveAffineEquationAlgebra (F : PlanePolynomial K) (i : Fin 3) :=
  MvPolynomial (Fin 2) K ⧸ Ideal.span {dehomogenizeAt i F}

/-- Evaluation at the two actual nonpivot coordinate-ratio sections. -/
def planeCurveAffinePolynomialMap (F : PlanePolynomial K) (i : Fin 3) :
    MvPolynomial (Fin 2) K →+* Γ(PlaneCurveScheme F, planeCurveCoordinateOpen F i) :=
  (planeCurveChartPolynomialMap F i).comp (rename i.succAbove).toRingHom

@[simp]
theorem planeCurveAffinePolynomialMap_X (F : PlanePolynomial K) (i : Fin 3)
    (j : Fin 2) :
    planeCurveAffinePolynomialMap F i (X j) =
      planeCurveChartCoordinates F i (i.succAbove j) := by
  simp [planeCurveAffinePolynomialMap]

/-- Setting the pivot variable to one retains exactly the original map on
all three homogeneous-coordinate polynomials. -/
theorem planeCurveAffinePolynomialMap_dehomogenize (F : PlanePolynomial K)
    (i : Fin 3) (P : PlanePolynomial K) :
    planeCurveAffinePolynomialMap F i (dehomogenizeAt i P) =
      planeCurveChartPolynomialMap F i P := by
  have hm : (planeCurveAffinePolynomialMap F i).comp (dehomogenizeAt i).toRingHom =
      planeCurveChartPolynomialMap F i := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [planeCurveAffinePolynomialMap, planeCurveChartPolynomialMap]
    · intro j
      obtain rfl | ⟨j, rfl⟩ := Fin.eq_self_or_eq_succAbove i j
      · simp
      · simp
  exact RingHom.congr_fun hm P

/-- The two retained coordinate ratios generate every regular section on
the actual affine chart. -/
theorem planeCurveAffinePolynomialMap_surjective (F : PlanePolynomial K) (i : Fin 3) :
    Function.Surjective (planeCurveAffinePolynomialMap F i) := by
  intro r
  obtain ⟨P, rfl⟩ := planeCurveChartPolynomialMap_surjective F i r
  exact ⟨dehomogenizeAt i P, planeCurveAffinePolynomialMap_dehomogenize F i P⟩

/-- The actual affine chart's full kernel is the literal dehomogenized
principal ideal, without radicalizing or changing coordinates. -/
theorem planeCurveAffinePolynomialMap_ker
    (F : PlanePolynomial K) (d : ℕ) (hF : F.IsHomogeneous d)
    (hFdeg : 1 < F.totalDegree) (hprime : (Ideal.span {F}).IsPrime) (i : Fin 3) :
    RingHom.ker (planeCurveAffinePolynomialMap F i) =
      Ideal.span {dehomogenizeAt i F} := by
  apply le_antisymm
  · intro P hP
    have hz : rename i.succAbove P ∈ RingHom.ker (planeCurveChartPolynomialMap F i) := hP
    rw [planeCurveChartPolynomialMap_ker F d hF hFdeg hprime i] at hz
    have hmap := Ideal.mem_map_of_mem (dehomogenizeAt i).toRingHom hz
    simpa only [Ideal.map_span, Set.image_insert_eq, Set.image_singleton,
      AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, map_sub, map_one,
      dehomogenizeAt_X_pivot, sub_self, Set.pair_comm (dehomogenizeAt i F) 0,
      Ideal.span_insert_zero,
      dehomogenizeAt_rename_succAbove] using hmap
  · rw [Ideal.span_le]
    intro P hP
    rcases Set.mem_singleton_iff.mp hP with rfl
    change planeCurveAffinePolynomialMap F i (dehomogenizeAt i F) = 0
    rw [planeCurveAffinePolynomialMap_dehomogenize]
    exact (planeCurveChartPolynomialMap_homogeneous_eq_zero_iff
      F d hF hFdeg hprime i d F hF).mpr (Ideal.subset_span (Set.mem_singleton F))

/-- The explicit equation quotient is the ring of actual regular sections,
as an algebra over the constants induced by the original curve structure. -/
def planeCurveAffineEquationAlgEquiv
    (F : PlanePolynomial K) (d : ℕ) (hF : F.IsHomogeneous d)
    (hFdeg : 1 < F.totalDegree) (hprime : (Ideal.span {F}).IsPrime) (i : Fin 3) :
    letI := planeCurveChartAlgebra F i
    PlaneCurveAffineEquationAlgebra F i ≃ₐ[K]
      Γ(PlaneCurveScheme F, planeCurveCoordinateOpen F i) := by
  letI := planeCurveChartAlgebra F i
  let φ : MvPolynomial (Fin 2) K →ₐ[K]
      Γ(PlaneCurveScheme F, planeCurveCoordinateOpen F i) :=
    { toRingHom := planeCurveAffinePolynomialMap F i
      commutes' := by
        intro c
        simp [planeCurveAffinePolynomialMap, planeCurveChartPolynomialMap,
          RingHom.algebraMap_toAlgebra] }
  exact (Ideal.quotientEquivAlgOfEq K
    (planeCurveAffinePolynomialMap_ker F d hF hFdeg hprime i).symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective
        (f := φ) (planeCurveAffinePolynomialMap_surjective F i))

@[simp]
theorem planeCurveAffineEquationAlgEquiv_mk
    (F : PlanePolynomial K) (d : ℕ) (hF : F.IsHomogeneous d)
    (hFdeg : 1 < F.totalDegree) (hprime : (Ideal.span {F}).IsPrime) (i : Fin 3)
    (P : MvPolynomial (Fin 2) K) :
    planeCurveAffineEquationAlgEquiv F d hF hFdeg hprime i (Ideal.Quotient.mk _ P) =
      planeCurveAffinePolynomialMap F i P := by
  simp only [planeCurveAffineEquationAlgEquiv, AlgEquiv.trans_apply,
    Ideal.quotientEquivAlgOfEq_mk]
  rfl

/-- Each retained variable is the specified actual projective coordinate
ratio, with the original ordering of the nonpivot coordinates. -/
@[simp]
theorem planeCurveAffineEquationAlgEquiv_mk_X
    (F : PlanePolynomial K) (d : ℕ) (hF : F.IsHomogeneous d)
    (hFdeg : 1 < F.totalDegree) (hprime : (Ideal.span {F}).IsPrime) (i : Fin 3)
    (j : Fin 2) :
    planeCurveAffineEquationAlgEquiv F d hF hFdeg hprime i
        (Ideal.Quotient.mk _ (X j)) =
      planeCurveChartCoordinates F i (i.succAbove j) := by
  rw [planeCurveAffineEquationAlgEquiv_mk, planeCurveAffinePolynomialMap_X]

/-- The actual standard open is the spectrum of its literal equation algebra. -/
def planeCurveAffineEquationIsoSpec
    (F : PlanePolynomial K) (d : ℕ) (hF : F.IsHomogeneous d)
    (hFdeg : 1 < F.totalDegree) (hprime : (Ideal.span {F}).IsPrime) (i : Fin 3) :
    (planeCurveCoordinateOpen F i).toScheme ≅
      Spec (CommRingCat.of (PlaneCurveAffineEquationAlgebra F i)) := by
  letI := planeCurveChartAlgebra F i
  exact (planeCurveCoordinateOpen_isAffine F i).isoSpec ≪≫
    Scheme.Spec.mapIso
      (planeCurveAffineEquationAlgEquiv F d hF hFdeg hprime i).toRingEquiv.toCommRingCatIso.op

/-- The affine equation algebra is a domain because it is the actual ring
of sections on a nonempty open of the integral curve. -/
theorem planeCurveAffineEquationAlgebra_isDomain
    (F : PlanePolynomial K) (d : ℕ) (hF : F.IsHomogeneous d)
    (hFdeg : 1 < F.totalDegree) (hprime : (Ideal.span {F}).IsPrime) (i : Fin 3) :
    IsDomain (PlaneCurveAffineEquationAlgebra F i) := by
  letI := planeCurveScheme_isIntegral F d hF hFdeg hprime
  letI := planeCurveCoordinateOpen_nonempty F d hF hFdeg hprime i
  letI := planeCurveChartAlgebra F i
  exact Function.Injective.isDomain
    (planeCurveAffineEquationAlgEquiv F d hF hFdeg hprime i).toRingHom
    (planeCurveAffineEquationAlgEquiv F d hF hFdeg hprime i).injective

/-- The affine presentation retains the original coefficient-field
structure morphism, not merely the abstract scheme isomorphism class. -/
@[reassoc]
theorem planeCurveAffineEquationIsoSpec_hom_comp_structure
    (F : PlanePolynomial K) (d : ℕ) (hF : F.IsHomogeneous d)
    (hFdeg : 1 < F.totalDegree) (hprime : (Ideal.span {F}).IsPrime) (i : Fin 3) :
    (planeCurveAffineEquationIsoSpec F d hF hFdeg hprime i).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap K (PlaneCurveAffineEquationAlgebra F i))) =
      (planeCurveCoordinateOpen F i).ι ≫ planeCurveStructure F := by
  letI := planeCurveScheme_isIntegral F d hF hFdeg hprime
  letI := planeCurveCoordinateOpen_nonempty F d hF hFdeg hprime i
  letI := planeCurveChartAlgebra F i
  let e := planeCurveAffineEquationAlgEquiv F d hF hFdeg hprime i
  let hU := planeCurveCoordinateOpen_isAffine F i
  have hc : CommRingCat.ofHom (algebraMap K (PlaneCurveAffineEquationAlgebra F i)) ≫
      CommRingCat.ofHom e.toRingHom =
      CommRingCat.ofHom (planeCurveChartConstants F i) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro c
    exact e.commutes c
  change (hU.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom e.toRingHom)) ≫ _ = _
  rw [Category.assoc, ← Spec.map_comp, hc]
  have hn := IsAffineOpen.Spec_map_appLE_fromSpec (planeCurveStructure F)
    (isAffineOpen_top (Spec (CommRingCat.of K))) hU (show
      planeCurveCoordinateOpen F i ≤ planeCurveStructure F ⁻¹ᵁ ⊤ from le_top)
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp] at hn
  have hc' : (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
      (planeCurveStructure F).appLE ⊤ (planeCurveCoordinateOpen F i) le_top =
      CommRingCat.ofHom (planeCurveChartConstants F i) := by
    apply CommRingCat.hom_ext
    exact (planeCurveChartConstants_eq_structure F i).symm
  rw [hc'] at hn
  rw [hn, ← Category.assoc, IsAffineOpen.isoSpec_hom,
    IsAffineOpen.toSpecΓ_fromSpec]

/-- The inverse affine equation presentation is also explicitly a
morphism over the original coefficient field. -/
@[reassoc]
theorem planeCurveAffineEquationIsoSpec_inv_comp_structure
    (F : PlanePolynomial K) (d : ℕ) (hF : F.IsHomogeneous d)
    (hFdeg : 1 < F.totalDegree) (hprime : (Ideal.span {F}).IsPrime) (i : Fin 3) :
    (planeCurveAffineEquationIsoSpec F d hF hFdeg hprime i).inv ≫
        (planeCurveCoordinateOpen F i).ι ≫ planeCurveStructure F =
      Spec.map (CommRingCat.ofHom (algebraMap K (PlaneCurveAffineEquationAlgebra F i))) := by
  rw [← planeCurveAffineEquationIsoSpec_hom_comp_structure F d hF hFdeg hprime i,
    Iso.inv_hom_id_assoc]

end EvenQuinticConic
