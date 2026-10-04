import EvenQuinticConic.PlaneQuintic
import EvenQuinticConic.ProjectiveCoordinateSections
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Over
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-!
# An actual reduced plane-curve scheme

Starting with the actual scheme `Proj K[X₀,X₁,X₂]` and its closed subset
`V(F)`, we construct the reduced induced scheme using mathlib's ideal-sheaf
data and its affine gluing construction. Its coordinate rings on ambient
affine charts are actual quotients by vanishing ideals.

This is a genuine scheme, not just the previously defined projective zero
locus. An isomorphism with the alternate construction `Proj (K[X₀,X₁,X₂]/(F))`
is not proved here; quotient grading and that comparison remain separate.
-/

noncomputable section

namespace EvenQuinticConic

open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial

variable {K : Type*} [Field K]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual projective plane scheme with its standard polynomial grading. -/
def ProjectivePlaneScheme (K : Type*) [Field K] : Scheme :=
  AlgebraicGeometry.Proj (homogeneousSubmodule (Fin 3) K)

/-- The homogeneous equation's closed locus in the actual projective plane. -/
def planeCurveClosedSet (F : PlanePolynomial K) : Closeds (ProjectivePlaneScheme K) :=
  ⟨planeHypersurfaceLocus F, ProjectiveSpectrum.isClosed_zeroLocus _ _⟩

/-- The genuine ideal-sheaf data of the reduced closed plane locus. -/
def planeCurveIdealSheaf (F : PlanePolynomial K) :
    (ProjectivePlaneScheme K).IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal (planeCurveClosedSet F)

/-- The actual scheme obtained by gluing the affine quotient rings of the
vanishing ideal, with underlying space the plane curve. -/
def PlaneCurveScheme (F : PlanePolynomial K) : Scheme :=
  (planeCurveIdealSheaf F).subscheme

/-- Its actual closed immersion into the projective plane. -/
def planeCurveInclusion (F : PlanePolynomial K) :
    PlaneCurveScheme F ⟶ ProjectivePlaneScheme K :=
  (planeCurveIdealSheaf F).subschemeι

instance planeCurveInclusion_isClosedImmersion (F : PlanePolynomial K) :
    IsClosedImmersion (planeCurveInclusion F) := by
  dsimp [planeCurveInclusion]
  infer_instance

/-- The range of the actual closed immersion is exactly the prescribed
projective equation's zero locus. -/
theorem range_planeCurveInclusion (F : PlanePolynomial K) :
    Set.range (planeCurveInclusion F).base = planeHypersurfaceLocus F := by
  change Set.range (fun x : (planeCurveIdealSheaf F).support => x.val) = _
  rw [Subtype.range_coe_subtype]
  rfl

/-- Reducedness of the induced scheme is proved from the radical affine
vanishing ideals, using actual affine covering maps and stalk maps. -/
theorem reduced_induced_scheme_isReduced (X : Scheme) (Z : Closeds X) :
    IsReduced (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := by
  let I := Scheme.IdealSheafData.vanishingIdeal Z
  have hlocal (U : X.affineOpens) : _root_.IsReduced (Γ(X, U) ⧸ I.ideal U) := by
    apply (Ideal.isRadical_iff_quotient_reduced _).mp
    exact PrimeSpectrum.isRadical_vanishingIdeal _
  apply (config := { allowSynthFailures := true }) isReduced_of_isReduced_stalk
  intro x
  let U := I.subschemeCover.idx x
  let f := I.subschemeCover.f U
  obtain ⟨y, hy⟩ := I.subschemeCover.covers x
  haveI : _root_.IsReduced (I.subschemeCover.X U) := hlocal U
  haveI : IsReduced (Spec (I.subschemeCover.X U)) := inferInstance
  have hinj : Function.Injective (f.stalkMap y) :=
    (asIso (f.stalkMap y)).commRingCatIsoToRingEquiv.injective
  have hred : _root_.IsReduced (I.subscheme.presheaf.stalk (f.base y)) :=
    isReduced_of_injective (f.stalkMap y).hom hinj
  exact hy ▸ hred

instance planeCurveScheme_isReduced (F : PlanePolynomial K) :
    IsReduced (PlaneCurveScheme F) :=
  reduced_induced_scheme_isReduced _ _

/-- Primality of the homogeneous equation makes the actual curve scheme's
underlying topological space irreducible. -/
theorem planeCurveScheme_irreducibleSpace (F : PlanePolynomial K) (e : ℕ)
    (hF : F.IsHomogeneous e) (hFdeg : 1 < F.totalDegree)
    (hprime : (Ideal.span {F}).IsPrime) :
    IrreducibleSpace (PlaneCurveScheme F) := by
  exact Subtype.irreducibleSpace (planeHypersurfaceLocus_isIrreducible F e hF hFdeg hprime)

/-- The actual reduced induced curve is integral, not merely declared to have
a domain as a coefficient model. -/
theorem planeCurveScheme_isIntegral (F : PlanePolynomial K) (e : ℕ)
    (hF : F.IsHomogeneous e) (hFdeg : 1 < F.totalDegree)
    (hprime : (Ideal.span {F}).IsPrime) :
    IsIntegral (PlaneCurveScheme F) := by
  letI := planeCurveScheme_irreducibleSpace F e hF hFdeg hprime
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-- Its generic point maps to the actual homogeneous prime `(F)` in the
ambient projective plane. This comparison uses the closed immersion and
the proved equality of its image with the closure of `(F)`. -/
theorem planeCurveInclusion_genericPoint (F : PlanePolynomial K) (e : ℕ)
    (hF : F.IsHomogeneous e) (hFdeg : 1 < F.totalDegree)
    (hprime : (Ideal.span {F}).IsPrime) :
    letI := planeCurveScheme_isIntegral F e hF hFdeg hprime
    (planeCurveInclusion F).base (genericPoint (PlaneCurveScheme F)) =
      planeHypersurfaceGenericPoint F e hF hFdeg hprime := by
  letI := planeCurveScheme_isIntegral F e hF hFdeg hprime
  have himage := (genericPoint_spec (PlaneCurveScheme F)).image
    (planeCurveInclusion F).base.hom.continuous
  have hclosed : IsClosed (planeHypersurfaceLocus F) :=
    (planeCurveClosedSet F).isClosed
  rw [Set.image_univ, range_planeCurveInclusion, hclosed.closure_eq] at himage
  exact himage.eq (closure_planeHypersurfaceGenericPoint F e hF hFdeg hprime)

/-- The actual projective plane is a scheme over `K` through its degree-zero
subring and the given coefficient algebra. -/
def projectivePlaneStructure (K : Type*) [Field K] :
    ProjectivePlaneScheme K ⟶ Spec (CommRingCat.of K) :=
  AlgebraicGeometry.Proj.toSpecZero (homogeneousSubmodule (Fin 3) K) ≫
    Spec.map (CommRingCat.ofHom (algebraMap K (homogeneousSubmodule (Fin 3) K 0)))

/-- The actual curve's structure morphism over the coefficient field. -/
def planeCurveStructure (F : PlanePolynomial K) :
    PlaneCurveScheme F ⟶ Spec (CommRingCat.of K) :=
  planeCurveInclusion F ≫ projectivePlaneStructure K

instance projectivePlaneScheme_over (K : Type*) [Field K] :
    (ProjectivePlaneScheme K).Over (Spec (CommRingCat.of K)) :=
  ⟨projectivePlaneStructure K⟩

instance planeCurveScheme_over (F : PlanePolynomial K) :
    (PlaneCurveScheme F).Over (Spec (CommRingCat.of K)) :=
  ⟨planeCurveStructure F⟩

instance planeCurveInclusion_isOver (F : PlanePolynomial K) :
    (planeCurveInclusion F).IsOver (Spec (CommRingCat.of K)) :=
  ⟨rfl⟩

/-- A standard coordinate chart on the actual curve scheme. -/
def planeCurveCoordinateOpen (F : PlanePolynomial K) (i : Fin 3) :
    (PlaneCurveScheme F).Opens :=
  planeCurveInclusion F ⁻¹ᵁ
    AlgebraicGeometry.Proj.basicOpen (homogeneousSubmodule (Fin 3) K) (X i)

/-- The three standard actual affine coordinate charts cover the entire curve. -/
theorem planeCurveCoordinateOpen_cover (F : PlanePolynomial K) :
    (⨆ i : Fin 3, planeCurveCoordinateOpen F i) = ⊤ :=
  (planeCurveInclusion F).preimage_iSup_eq_top (planeCoordinateOpen_cover K)

/-- Every coordinate chart of the curve is affine as the inverse image of
an affine projective chart under the actual closed immersion. -/
theorem planeCurveCoordinateOpen_isAffine (F : PlanePolynomial K) (i : Fin 3) :
    IsAffineOpen (planeCurveCoordinateOpen F i) := by
  apply IsAffineOpen.preimage
  exact AlgebraicGeometry.Proj.isAffineOpen_basicOpen
    (homogeneousSubmodule (Fin 3) K) (X i) (isHomogeneous_X K i) (by decide)

/-- All three coordinate charts contain the actual generic point. -/
theorem genericPoint_mem_planeCurveCoordinateOpen (F : PlanePolynomial K) (e : ℕ)
    (hF : F.IsHomogeneous e) (hFdeg : 1 < F.totalDegree)
    (hprime : (Ideal.span {F}).IsPrime) (i : Fin 3) :
    letI := planeCurveScheme_isIntegral F e hF hFdeg hprime
    genericPoint (PlaneCurveScheme F) ∈ planeCurveCoordinateOpen F i := by
  letI := planeCurveScheme_isIntegral F e hF hFdeg hprime
  change (planeCurveInclusion F).base (genericPoint (PlaneCurveScheme F)) ∈
    AlgebraicGeometry.Proj.basicOpen (homogeneousSubmodule (Fin 3) K) (X i)
  rw [planeCurveInclusion_genericPoint F e hF hFdeg hprime]
  exact plane_coordinate_not_mem_principal F hFdeg i

/-- Nonemptiness of every standard affine curve chart is proved, rather than
supplied as an extra hypothesis to its generic restriction map. -/
theorem planeCurveCoordinateOpen_nonempty (F : PlanePolynomial K) (e : ℕ)
    (hF : F.IsHomogeneous e) (hFdeg : 1 < F.totalDegree)
    (hprime : (Ideal.span {F}).IsPrime) (i : Fin 3) :
    Nonempty (planeCurveCoordinateOpen F i) := by
  letI := planeCurveScheme_isIntegral F e hF hFdeg hprime
  exact ⟨⟨genericPoint (PlaneCurveScheme F),
    genericPoint_mem_planeCurveCoordinateOpen F e hF hFdeg hprime i⟩⟩

/-- On every actual ambient affine open, the curve has the actual quotient
coordinate ring by its reduced vanishing ideal. This is a statement about
structure sheaves, not a dimension or global twisting-sheaf calculation. -/
def planeCurveAffineSectionsIso (F : PlanePolynomial K)
    (U : (ProjectivePlaneScheme K).affineOpens) :
    Γ(PlaneCurveScheme F, planeCurveInclusion F ⁻¹ᵁ U) ≅
      CommRingCat.of (Γ(ProjectivePlaneScheme K, U) ⧸ (planeCurveIdealSheaf F).ideal U) :=
  (planeCurveIdealSheaf F).subschemeObjIso U

/-- Restriction from an ambient affine chart to its curve chart is a
surjective ring map. No global-section surjectivity is inferred. -/
theorem planeCurveInclusion_affine_app_surjective (F : PlanePolynomial K)
    (U : (ProjectivePlaneScheme K).affineOpens) :
    Function.Surjective ((planeCurveInclusion F).app U) :=
  (planeCurveIdealSheaf F).subschemeι_app_surjective U

/-- The affine-chart restriction kernel is the actual vanishing ideal of
the curve in that affine chart. -/
theorem planeCurveInclusion_affine_app_ker (F : PlanePolynomial K)
    (U : (ProjectivePlaneScheme K).affineOpens) :
    RingHom.ker ((planeCurveInclusion F).app U).hom =
      (planeCurveIdealSheaf F).ideal U :=
  (planeCurveIdealSheaf F).ker_subschemeι_app U

end EvenQuinticConic
