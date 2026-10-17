import EvenQuinticConic.IncidenceParameterFieldIdentification
import EvenQuinticConic.AffineGenericFiberLocalization

/-!
# The actual generic fibre of the global incidence open

The generic parameter morphism is built from the actual projective chart
and its fraction field. The base change of the actual global-open projection
is identified with the spectrum of the actual parameter localization.
Both projections are preserved; the comparison is not an abstract isomorphism.
-/

noncomputable section
namespace EvenQuinticConic.Incidence
open MvPolynomial AlgebraicGeometry CategoryTheory CategoryTheory.Limits
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type*} [Field K]

/-- The literal normalized parameter chart is an integral domain. -/
instance incidenceParameterChartDomain (k : Fin 3) :
    IsDomain (ProjectiveCoordinateQuotient (K := K) k) :=
  incidenceParameterChart_isDomain (K := K) k

/-- The parameter algebra action is the actual pivot-column pullback. -/
instance incidenceMinorParameterAlgebra
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4) :
    Algebra (ProjectiveCoordinateQuotient (K := K) k)
      (SegreIncidenceMinorLocalization M k p) :=
  (incidenceParameterChartMap M k p).toRingHom.toAlgebra

instance incidenceMinorParameterScalarTower
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4) :
    IsScalarTower K (ProjectiveCoordinateQuotient (K := K) k)
      (SegreIncidenceMinorLocalization M k p) :=
  IsScalarTower.of_algHom (incidenceParameterChartMap M k p)

/-- The actual parameter function field in the selected standard chart. -/
abbrev IncidenceParameterChartField (k : Fin 3) :=
  FractionRing (ProjectiveCoordinateQuotient (K := K) k)

/-- The fraction-field point followed by the genuine projective chart. -/
def incidenceParameterGenericPoint (k : Fin 3) :
    Spec (CommRingCat.of (IncidenceParameterChartField (K := K) k)) ⟶
      IncidenceParameterPlane K :=
  Spec.map (CommRingCat.ofHom
    (algebraMap (ProjectiveCoordinateQuotient (K := K) k)
      (IncidenceParameterChartField (K := K) k))) ≫
    projectiveCoordinateQuotientChartMap (K := K) k

/-- This field-valued point is dominant, hence lies at the generic point
of the actual parameter plane. -/
theorem incidenceParameterGenericPoint_isDominant (k : Fin 3) :
    IsDominant (incidenceParameterGenericPoint (K := K) k) := by
  letI : IsDominant (Spec.map (CommRingCat.ofHom
      (algebraMap (ProjectiveCoordinateQuotient (K := K) k)
        (IncidenceParameterChartField (K := K) k)))) := by
    refine ⟨?_⟩
    apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr
    change RingHom.ker (algebraMap (ProjectiveCoordinateQuotient (K := K) k)
      (IncidenceParameterChartField (K := K) k)) ≤ _
    rw [(RingHom.injective_iff_ker_eq_bot _).mp
      (IsFractionRing.injective (ProjectiveCoordinateQuotient (K := K) k)
        (IncidenceParameterChartField (K := K) k))]
    exact bot_le
  letI := incidenceParameterChart_isDominant (K := K) k
  unfold incidenceParameterGenericPoint
  infer_instance

/-- The actual coordinate ring after passing to the generic parameter. -/
abbrev IncidenceGenericFiberRing
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4) :=
  AffineGenericFiberLocalization (ProjectiveCoordinateQuotient (K := K) k)
    (SegreIncidenceMinorLocalization M k p)

/-- The genuine categorical base change of the already constructed
projection on the global incidence open. -/
abbrev GlobalIncidenceOpenGenericFiber
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4)
    (h : (cross (segreChartRow (netLinearRow M) k p)
      (segreChartRow (netQuadraticRow M) k p)).z ≠ 0) :=
  pullback (globalIncidenceMinorParameterProjection M k p h)
    (incidenceParameterGenericPoint (K := K) k)

/-- The localization spectrum maps back to the actual global incidence open. -/
def incidenceGenericFiberToGlobalOpen
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4)
    (h : (cross (segreChartRow (netLinearRow M) k p)
      (segreChartRow (netQuadraticRow M) k p)).z ≠ 0) :
    Spec (CommRingCat.of (IncidenceGenericFiberRing M k p)) ⟶
      (globalIncidenceMinorOpen M p (k.succAbove 0) (k.succAbove 1) k).toScheme :=
  Spec.map (CommRingCat.ofHom
    (algebraMap (SegreIncidenceMinorLocalization M k p) (IncidenceGenericFiberRing M k p))) ≫
      (globalIncidenceMinorOpenIso M p k h).inv

/-- Its parameter-field structure is the canonical localization map. -/
def incidenceGenericFiberToParameter
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4) :
    Spec (CommRingCat.of (IncidenceGenericFiberRing M k p)) ⟶
      Spec (CommRingCat.of (IncidenceParameterChartField (K := K) k)) :=
  Spec.map (CommRingCat.ofHom
    (affineGenericFiberFractionMap (ProjectiveCoordinateQuotient (K := K) k)
      (SegreIncidenceMinorLocalization M k p)))

/-- The constructed square is the actual base change of the original
global-open parameter projection, including both specified maps. -/
theorem incidenceGenericFiber_isPullback
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4)
    (h : (cross (segreChartRow (netLinearRow M) k p)
      (segreChartRow (netQuadraticRow M) k p)).z ≠ 0) :
    IsPullback (incidenceGenericFiberToGlobalOpen M k p h)
      (incidenceGenericFiberToParameter M k p)
      (globalIncidenceMinorParameterProjection M k p h)
      (incidenceParameterGenericPoint (K := K) k) := by
  let A := ProjectiveCoordinateQuotient (K := K) k
  let B := SegreIncidenceMinorLocalization M k p
  let f := Spec.map (CommRingCat.ofHom (algebraMap A B))
  let g := Spec.map (CommRingCat.ofHom (algebraMap A (FractionRing A)))
  let j := projectiveCoordinateQuotientChartMap (K := K) k
  have hb : IsPullback g (𝟙 _) j (g ≫ j) :=
    IsPullback.of_vert_isIso_mono ⟨by simp⟩
  have ha := (affineGenericFiberLocalization_isPullback A B).paste_vert hb
  have hi : IsPullback (globalIncidenceMinorOpenIso M p k h).inv
      (incidenceMinorParameterProjection M k p)
      (globalIncidenceMinorParameterProjection M k p h) (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by
      simp [globalIncidenceMinorParameterProjection]⟩
  simpa only [Category.comp_id, incidenceGenericFiberToGlobalOpen,
    incidenceGenericFiberToParameter, incidenceParameterGenericPoint,
    incidenceMinorParameterProjection, A, B, f, g, j] using
      ha.paste_horiz hi

/-- The actual generic base change of the global open has the computed
localization as its affine coordinate algebra. -/
def globalIncidenceOpenGenericFiberIso
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4)
    (h : (cross (segreChartRow (netLinearRow M) k p)
      (segreChartRow (netQuadraticRow M) k p)).z ≠ 0) :
    GlobalIncidenceOpenGenericFiber M k p h ≅
      Spec (CommRingCat.of (IncidenceGenericFiberRing M k p)) :=
  (incidenceGenericFiber_isPullback M k p h).isoPullback.symm

@[reassoc (attr := simp)]
theorem globalIncidenceOpenGenericFiberIso_inv_fst
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4)
    (h : (cross (segreChartRow (netLinearRow M) k p)
      (segreChartRow (netQuadraticRow M) k p)).z ≠ 0) :
    (globalIncidenceOpenGenericFiberIso M k p h).inv ≫ pullback.fst _ _ =
      incidenceGenericFiberToGlobalOpen M k p h :=
  (incidenceGenericFiber_isPullback M k p h).isoPullback_hom_fst

@[reassoc (attr := simp)]
theorem globalIncidenceOpenGenericFiberIso_inv_snd
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4)
    (h : (cross (segreChartRow (netLinearRow M) k p)
      (segreChartRow (netQuadraticRow M) k p)).z ≠ 0) :
    (globalIncidenceOpenGenericFiberIso M k p h).inv ≫ pullback.snd _ _ =
      incidenceGenericFiberToParameter M k p :=
  (incidenceGenericFiber_isPullback M k p h).isoPullback_hom_snd

end EvenQuinticConic.Incidence
