import EvenQuinticConic.GlobalIncidenceOpenChart
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

/-!
# The actual parameter projection on the global incidence minor open

The first Segre factor is read from the pivot column. This constructs the
scheme morphism to the parameter plane from that literal coordinate map,
including its structural map over the ground field. No projection or
geometric dominance assertion is supplied as input.
-/

noncomputable section

namespace EvenQuinticConic.Incidence

open MvPolynomial AlgebraicGeometry CategoryTheory

variable {K : Type*} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual parameter plane. -/
abbrev IncidenceParameterPlane (K : Type*) [Field K] :=
  Proj (homogeneousSubmodule (Fin 3) K)

/-- Reading a first-factor coordinate from the pivot column of the actual
localized Segre incidence quotient. -/
def incidenceParameterCoordinate
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4) (i : Fin 3) :
    SegreIncidenceMinorLocalization M k p :=
  algebraMap (SegreIncidenceChartAlgebra M k p) _ (Ideal.Quotient.mk _ (X (i, p)))

@[simp] theorem incidenceParameterCoordinate_pivot
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4) :
    incidenceParameterCoordinate M k p k = 1 := by
  have h : (Ideal.Quotient.mk _ (X (k, p)) : SegreIncidenceChartAlgebra M k p) = 1 := by
    apply (segreIncidenceChartAlgEquiv M k p).injective
    rw [segreIncidenceChartAlgEquiv_coordinate, segreChartT_pivot,
      segreChartY_pivot, one_mul, map_one, map_one]
  unfold incidenceParameterCoordinate
  rw [h, map_one]

/-- The literal polynomial substitution for the parameter coordinates. -/
def incidenceParameterPolynomialMap
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4) :
    MvPolynomial (Fin 3) K →ₐ[K] SegreIncidenceMinorLocalization M k p :=
  aeval (incidenceParameterCoordinate M k p)

set_option synthInstance.maxHeartbeats 100000 in
/-- Normalization of the Segre pivot makes the parameter pivot equal to one. -/
theorem incidenceParameterIdeal_le_ker
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4) :
    projectiveCoordinateIdeal (K := K) k ≤
      RingHom.ker (incidenceParameterPolynomialMap M k p).toRingHom := by
  rw [projectiveCoordinateIdeal, Ideal.span_le]
  intro F hF
  rcases Set.mem_singleton_iff.mp hF with rfl
  change aeval (incidenceParameterCoordinate M k p) (X k - 1) = 0
  rw [map_sub, aeval_X, map_one, incidenceParameterCoordinate_pivot, sub_self]

/-- The exact affine parameter-chart pullback, with no unspecified map. -/
def incidenceParameterChartMap
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4) :
    ProjectiveCoordinateQuotient (K := K) k →ₐ[K] SegreIncidenceMinorLocalization M k p :=
  Ideal.Quotient.liftₐ _ (incidenceParameterPolynomialMap M k p)
    (fun _ h => RingHom.mem_ker.mp (incidenceParameterIdeal_le_ker M k p h))

@[simp] theorem incidenceParameterChartMap_mk
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4)
    (F : MvPolynomial (Fin 3) K) :
    incidenceParameterChartMap M k p (Ideal.Quotient.mk _ F) =
      aeval (incidenceParameterCoordinate M k p) F := rfl

@[simp] theorem incidenceParameterChartMap_coordinate
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4) (i : Fin 3) :
    incidenceParameterChartMap M k p (Ideal.Quotient.mk _ (X i)) =
      incidenceParameterCoordinate M k p i := by
  simp

/-- The local incidence algebra carries its actual morphism to the
parameter plane, obtained by the first-factor coordinate pullback. -/
def incidenceMinorParameterProjection
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4) :
    Spec (CommRingCat.of (SegreIncidenceMinorLocalization M k p)) ⟶
      IncidenceParameterPlane K :=
  Spec.map (CommRingCat.ofHom (incidenceParameterChartMap M k p).toRingHom) ≫
    projectiveCoordinateQuotientChartMap (K := K) k

/-- The actual parameter projection respects the original coefficient field. -/
@[reassoc (attr := simp)] theorem incidenceMinorParameterProjection_comp_structure
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4) :
    incidenceMinorParameterProjection M k p ≫
        projectiveCoordinateStructure (K := K) (ι := Fin 3) =
      Spec.map (CommRingCat.ofHom (algebraMap K (SegreIncidenceMinorLocalization M k p))) := by
  rw [incidenceMinorParameterProjection, Category.assoc,
    projectiveCoordinateQuotientChartMap_comp_structure, ← Spec.map_comp]
  congr 1
  ext c
  exact (incidenceParameterChartMap M k p).commutes c

/-- On the genuine open of the global incidence scheme, transport of the
literal coordinate pullback constructs the actual first-factor projection. -/
def globalIncidenceMinorParameterProjection
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4)
    (h : (cross (segreChartRow (netLinearRow M) k p)
      (segreChartRow (netQuadraticRow M) k p)).z ≠ 0) :
    (globalIncidenceMinorOpen M p (k.succAbove 0) (k.succAbove 1) k).toScheme ⟶
      IncidenceParameterPlane K :=
  (globalIncidenceMinorOpenIso M p k h).hom ≫ incidenceMinorParameterProjection M k p

/-- The morphism on the actual global open is over `K` with its inherited
structural map; this is more than an abstract map of underlying spaces. -/
@[reassoc (attr := simp)] theorem globalIncidenceMinorParameterProjection_comp_structure
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4)
    (h : (cross (segreChartRow (netLinearRow M) k p)
      (segreChartRow (netQuadraticRow M) k p)).z ≠ 0) :
    globalIncidenceMinorParameterProjection M k p h ≫
        projectiveCoordinateStructure (K := K) (ι := Fin 3) =
      (globalIncidenceMinorOpen M p (k.succAbove 0) (k.succAbove 1) k).ι ≫
        globalIncidenceStructure M := by
  rw [globalIncidenceMinorParameterProjection, Category.assoc,
    incidenceMinorParameterProjection_comp_structure,
    ← globalIncidenceMinorOpenIso_inv_comp_structure M p k h,
    ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- Under the already proved Segre-to-incidence algebra identification,
the nonpivot parameter coordinates are literally the two unknowns of the
two linear incidence equations. -/
@[simp] theorem incidenceParameterCoordinate_under_incidenceEquiv
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4) (i : Fin 2) :
    segreIncidenceMinorLocalizationAlgEquiv M k p
        (incidenceParameterCoordinate M k p (k.succAbove i)) =
      Ideal.Quotient.mk _ (X i) := by
  rw [incidenceParameterCoordinate,
    segreIncidenceMinorLocalizationAlgEquiv_algebraMap,
    segreIncidenceChartAlgEquiv_pivotColumn,
    affineIncidenceCoefficientMap_mk]
  simp only [MvPolynomial.map_X]
  rfl

/-- Elimination of the two incidence equations identifies the actual
minor-chart algebra with the localization in the three spatial variables. -/
def incidenceMinorEliminationAlgEquiv
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4) :
    SegreIncidenceMinorLocalization M k p ≃ₐ[K]
      Localization.Away (cross (segreChartRow (netLinearRow M) k p)
        (segreChartRow (netQuadraticRow M) k p)).z :=
  (segreIncidenceMinorLocalizationAlgEquiv M k p).trans
    ((localizedIncidenceAlgEquiv _ _).restrictScalars K)

/-- The exact parameter pullback after eliminating the incidence unknowns.
The following formula computes its coordinates as Cramer ratios. -/
def incidenceParameterCramerMap
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4) :
    ProjectiveCoordinateQuotient (K := K) k →ₐ[K]
      Localization.Away (cross (segreChartRow (netLinearRow M) k p)
        (segreChartRow (netQuadraticRow M) k p)).z :=
  (incidenceMinorEliminationAlgEquiv M k p).toAlgHom.comp
    (incidenceParameterChartMap M k p)

/-- Each nonpivot parameter pulls back to the corresponding cross-product
component divided by the selected minor, in the actual localization ring. -/
@[simp] theorem incidenceParameterCramerMap_coordinate
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4) (i : Fin 2) :
    incidenceParameterCramerMap M k p (Ideal.Quotient.mk _ (X (k.succAbove i))) =
      ![(cross (localizedRow (segreChartRow (netLinearRow M) k p)
          (segreChartRow (netQuadraticRow M) k p) (segreChartRow (netLinearRow M) k p))
        (localizedRow (segreChartRow (netLinearRow M) k p)
          (segreChartRow (netQuadraticRow M) k p) (segreChartRow (netQuadraticRow M) k p))).x,
        (cross (localizedRow (segreChartRow (netLinearRow M) k p)
          (segreChartRow (netQuadraticRow M) k p) (segreChartRow (netLinearRow M) k p))
        (localizedRow (segreChartRow (netLinearRow M) k p)
          (segreChartRow (netQuadraticRow M) k p) (segreChartRow (netQuadraticRow M) k p))).y] i *
        IsLocalization.Away.invSelf (S := Localization.Away
          (cross (segreChartRow (netLinearRow M) k p)
            (segreChartRow (netQuadraticRow M) k p)).z)
          (cross (segreChartRow (netLinearRow M) k p)
            (segreChartRow (netQuadraticRow M) k p)).z := by
  change localizedIncidenceAlgEquiv _ _
    (segreIncidenceMinorLocalizationAlgEquiv M k p
      (incidenceParameterChartMap M k p (Ideal.Quotient.mk _ (X (k.succAbove i))))) = _
  rw [incidenceParameterChartMap_coordinate,
    incidenceParameterCoordinate_under_incidenceEquiv]
  unfold localizedIncidenceAlgEquiv
  rw [affineIncidenceAlgEquiv_mk, aeval_X]
  fin_cases i <;> rfl

/-- Since elimination is an isomorphism, injectivity of the actual chart
pullback is exactly injectivity of the explicitly computed Cramer map. -/
theorem incidenceParameterChartMap_injective_iff_cramer
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4) :
    Function.Injective (incidenceParameterChartMap M k p) ↔
      Function.Injective (incidenceParameterCramerMap M k p) := by
  exact ((incidenceMinorEliminationAlgEquiv M k p).injective.of_comp_iff
    (incidenceParameterChartMap M k p)).symm

/-- The zero homogeneous prime supplies an actual generic point of the
parameter plane. -/
def incidenceParameterZeroPrime :
    ProjectiveSpectrum (homogeneousSubmodule (Fin 3) K) where
  asHomogeneousIdeal := ⊥
  isPrime := by simpa only [HomogeneousIdeal.toIdeal_bot] using
    (Ideal.bot_prime : (⊥ : Ideal (MvPolynomial (Fin 3) K)).IsPrime)
  not_irrelevant_le := by
    intro hle
    have hx : (X (0 : Fin 3) : MvPolynomial (Fin 3) K) ∈
        HomogeneousIdeal.irrelevant (homogeneousSubmodule (Fin 3) K) := by
      rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply]
      exact DirectSum.decompose_of_mem_ne (homogeneousSubmodule (Fin 3) K)
        (isHomogeneous_X K 0) (by decide : (1 : ℕ) ≠ 0)
    have hz : (X (0 : Fin 3) : MvPolynomial (Fin 3) K) ∈
        (⊥ : Ideal (MvPolynomial (Fin 3) K)) := hle hx
    exact X_ne_zero (0 : Fin 3) (Ideal.mem_bot.mp hz)

/-- Density of the actual homogeneous zero prime, proved directly. -/
theorem closure_incidenceParameterZeroPrime :
    closure ({incidenceParameterZeroPrime (K := K)} : Set (IncidenceParameterPlane K)) =
      Set.univ := by
  rw [← ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure,
    ProjectiveSpectrum.vanishingIdeal_singleton]
  exact ProjectiveSpectrum.zeroLocus_bot _

/-- The actual parameter plane is irreducible. -/
theorem incidenceParameterPlane_irreducibleSpace :
    IrreducibleSpace (IncidenceParameterPlane K) := by
  apply (irreducibleSpace_def _).mpr
  change IsIrreducible (Set.univ : Set (IncidenceParameterPlane K))
  rw [← closure_incidenceParameterZeroPrime]
  exact isIrreducible_singleton.closure

/-- Each actual standard parameter chart is dominant in the plane. -/
theorem incidenceParameterChart_isDominant (k : Fin 3) :
    IsDominant (projectiveCoordinateQuotientChartMap (K := K) k) := by
  letI := incidenceParameterPlane_irreducibleSpace (K := K)
  apply (isDominant_iff _).mpr
  change Dense (Set.range (projectiveCoordinateQuotientChartMap (K := K) k).base)
  have hr : (projectiveCoordinateQuotientChartMap (K := K) k).opensRange =
      Proj.basicOpen (homogeneousSubmodule (Fin 3) K) (X k) := by
    unfold projectiveCoordinateQuotientChartMap
    rw [Scheme.Hom.opensRange_comp_of_isIso, Proj.opensRange_awayι]
  change Dense ((projectiveCoordinateQuotientChartMap (K := K) k).opensRange :
    Set (IncidenceParameterPlane K))
  rw [hr]
  apply (Proj.basicOpen (homogeneousSubmodule (Fin 3) K) (X k)).isOpen.dense
  refine ⟨incidenceParameterZeroPrime, ?_⟩
  exact X_ne_zero k

/-- The exact remaining affine algebra criterion suffices for dominance
of the already constructed scheme projection. It is kept explicit: this
lemma does not assert injectivity from the matrix-net hypotheses. -/
theorem incidenceMinorParameterProjection_isDominant_of_injective
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4)
    (hinj : Function.Injective (incidenceParameterChartMap M k p)) :
    IsDominant (incidenceMinorParameterProjection M k p) := by
  letI : IsDominant
      (Spec.map (CommRingCat.ofHom (incidenceParameterChartMap M k p).toRingHom)) := by
    refine ⟨?_⟩
    apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr
    change RingHom.ker (incidenceParameterChartMap M k p).toRingHom ≤ _
    rw [(RingHom.injective_iff_ker_eq_bot (incidenceParameterChartMap M k p).toRingHom).mp hinj]
    exact bot_le
  letI := incidenceParameterChart_isDominant (K := K) k
  unfold incidenceMinorParameterProjection
  infer_instance

/-- The same algebra criterion gives genuine dominance of the projection
from the specified open of the global incidence scheme. -/
theorem globalIncidenceMinorParameterProjection_isDominant_of_injective
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4)
    (h : (cross (segreChartRow (netLinearRow M) k p)
      (segreChartRow (netQuadraticRow M) k p)).z ≠ 0)
    (hinj : Function.Injective (incidenceParameterChartMap M k p)) :
    IsDominant (globalIncidenceMinorParameterProjection M k p h) := by
  letI := incidenceMinorParameterProjection_isDominant_of_injective M k p hinj
  unfold globalIncidenceMinorParameterProjection
  infer_instance

end EvenQuinticConic.Incidence
