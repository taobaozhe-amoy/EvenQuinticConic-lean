import EvenQuinticConic.SegreIncidenceChartAlgebra
import EvenQuinticConic.IncidenceLocalization
import EvenQuinticConic.IncidenceFunctionField

/-!
# Localizing the genuine Segre incidence chart

The open defined by the actual homogeneous minor in the Segre coordinate
quotient has the explicit affine incidence algebra obtained by localizing
the coefficient ring. The comparison preserves the original field and
identifies the fraction field with the rational function field in three
variables whenever the minor is nonzero.
-/

noncomputable section

namespace EvenQuinticConic.Incidence

open MvPolynomial AlgebraicGeometry CategoryTheory

variable {K : Type*} [Field K]

/-- The actual global cubic minor, viewed in the standard Segre chart quotient. -/
def segreIncidenceChartMinor
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4) :
    SegreIncidenceChartAlgebra M k p :=
  Ideal.Quotient.mk _ (globalIncidenceMinor M (k.succAbove 0) (k.succAbove 1) k)

/-- The principal-open coordinate ring of the genuine Segre incidence chart. -/
abbrev SegreIncidenceMinorLocalization
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4) :=
  Localization.Away (segreIncidenceChartMinor M k p)

@[simp] theorem segreIncidenceChartAlgEquiv_chartMinor
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4) :
    segreIncidenceChartAlgEquiv M k p (segreIncidenceChartMinor M k p) =
      algebraMap (MvPolynomial (Fin 3) K)
        (AffineIncidenceAlgebra (segreChartRow (netLinearRow M) k p)
          (segreChartRow (netQuadraticRow M) k p))
        (cross (segreChartRow (netLinearRow M) k p)
          (segreChartRow (netQuadraticRow M) k p)).z := by
  rw [segreIncidenceChartMinor, segreIncidenceChartAlgEquiv_minor,
    segreChartRow_cross_z]

/-- The exact chart isomorphism transports powers of the actual minor to
powers of the coefficient minor used for affine elimination. -/
theorem segreIncidenceChartAlgEquiv_minor_powers
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4) :
    (Submonoid.powers (segreIncidenceChartMinor M k p)).map
        (segreIncidenceChartAlgEquiv M k p) =
      Submonoid.powers
        (algebraMap (MvPolynomial (Fin 3) K)
          (AffineIncidenceAlgebra (segreChartRow (netLinearRow M) k p)
            (segreChartRow (netQuadraticRow M) k p))
          (cross (segreChartRow (netLinearRow M) k p)
            (segreChartRow (netQuadraticRow M) k p)).z) := by
  rw [Submonoid.map_powers, segreIncidenceChartAlgEquiv_chartMinor]

/-- Localizing the actual chart isomorphism at its actual minor. -/
def segreIncidenceMinorToAffineLocalizationEquiv
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4) :
    SegreIncidenceMinorLocalization M k p ≃ₐ[K]
      Localization.Away
        (algebraMap (MvPolynomial (Fin 3) K)
          (AffineIncidenceAlgebra (segreChartRow (netLinearRow M) k p)
            (segreChartRow (netQuadraticRow M) k p))
          (cross (segreChartRow (netLinearRow M) k p)
            (segreChartRow (netQuadraticRow M) k p)).z) :=
  IsLocalization.algEquivOfAlgEquiv _ _ (segreIncidenceChartAlgEquiv M k p)
    (segreIncidenceChartAlgEquiv_minor_powers M k p)

/-- The quotient-localization comparison preserves the original ground
field, with the actual coefficient maps on both sides. -/
def affineIncidenceLocalizationBaseAlgEquiv
    (a b : Vec3 (MvPolynomial (Fin 3) K)) :
    Localization.Away
      (algebraMap (MvPolynomial (Fin 3) K) (AffineIncidenceAlgebra a b) (cross a b).z)
      ≃ₐ[K] LocalizedIncidenceAlgebra a b := by
  letI := localizedIncidenceCoefficientAlgebra a b
  refine { (affineIncidenceLocalizationEquiv a b).toRingEquiv with commutes' := ?_ }
  intro c
  change affineIncidenceLocalizationEquiv a b
    (algebraMap K
      (Localization.Away
        (algebraMap (MvPolynomial (Fin 3) K) (AffineIncidenceAlgebra a b)
          (cross a b).z)) c) = _
  rw [IsScalarTower.algebraMap_apply K (AffineIncidenceAlgebra a b)
    (Localization.Away
      (algebraMap (MvPolynomial (Fin 3) K) (AffineIncidenceAlgebra a b) (cross a b).z)),
    AlgEquiv.commutes]
  change Ideal.Quotient.mk _
    (MvPolynomial.map (algebraMap (MvPolynomial (Fin 3) K)
      (Localization.Away (cross a b).z)) (C (C c))) = _
  rw [MvPolynomial.map_C]
  rfl

/-- The genuine minor-open Segre coordinate algebra is the actual localized
two-equation incidence algebra. No comparison is a hypothesis. -/
def segreIncidenceMinorLocalizationAlgEquiv
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4) :
    SegreIncidenceMinorLocalization M k p ≃ₐ[K]
      LocalizedIncidenceAlgebra (segreChartRow (netLinearRow M) k p)
        (segreChartRow (netQuadraticRow M) k p) :=
  (segreIncidenceMinorToAffineLocalizationEquiv M k p).trans
    (affineIncidenceLocalizationBaseAlgEquiv _ _)

@[simp] theorem segreIncidenceMinorToAffineLocalizationEquiv_algebraMap
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4)
    (F : SegreIncidenceChartAlgebra M k p) :
    segreIncidenceMinorToAffineLocalizationEquiv M k p
        (algebraMap (SegreIncidenceChartAlgebra M k p)
          (SegreIncidenceMinorLocalization M k p) F) =
      algebraMap _ _ (segreIncidenceChartAlgEquiv M k p F) :=
  IsLocalization.algEquivOfAlgEquiv_eq
    (segreIncidenceChartAlgEquiv_minor_powers M k p) F

/-- The localized isomorphism extends the explicit Segre substitution
followed by the canonical coefficient-localization map. -/
@[simp] theorem segreIncidenceMinorLocalizationAlgEquiv_algebraMap
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4)
    (F : SegreIncidenceChartAlgebra M k p) :
    segreIncidenceMinorLocalizationAlgEquiv M k p
        (algebraMap (SegreIncidenceChartAlgebra M k p)
          (SegreIncidenceMinorLocalization M k p) F) =
      affineIncidenceCoefficientMap
        (algebraMap (MvPolynomial (Fin 3) K)
          (Localization.Away (cross (segreChartRow (netLinearRow M) k p)
            (segreChartRow (netQuadraticRow M) k p)).z))
        (segreChartRow (netLinearRow M) k p)
        (segreChartRow (netQuadraticRow M) k p)
        (segreIncidenceChartAlgEquiv M k p F) := by
  change affineIncidenceLocalizationBaseAlgEquiv _ _
    (segreIncidenceMinorToAffineLocalizationEquiv M k p
      (algebraMap _ _ F)) = _
  rw [segreIncidenceMinorToAffineLocalizationEquiv_algebraMap]
  letI := localizedIncidenceCoefficientAlgebra
    (segreChartRow (netLinearRow M) k p) (segreChartRow (netQuadraticRow M) k p)
  exact (affineIncidenceLocalizationEquiv _ _).commutes
    (segreIncidenceChartAlgEquiv M k p F)

/-- Nonvanishing of the minor proves that the actual localized Segre
quotient is an integral domain. -/
theorem segreIncidenceMinorLocalization_isDomain
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4)
    (h : (cross (segreChartRow (netLinearRow M) k p)
      (segreChartRow (netQuadraticRow M) k p)).z ≠ 0) :
    IsDomain (SegreIncidenceMinorLocalization M k p) := by
  letI : IsDomain (LocalizedIncidenceAlgebra (segreChartRow (netLinearRow M) k p)
      (segreChartRow (netQuadraticRow M) k p)) := localizedIncidence_isDomain _ _ h
  exact Function.Injective.isDomain (segreIncidenceMinorLocalizationAlgEquiv M k p).toRingHom
    (segreIncidenceMinorLocalizationAlgEquiv M k p).injective

/-- The fraction field of the genuine Segre minor open is the rational
function field in three variables, by an equivalence preserving `K`. -/
def segreIncidenceMinorFractionFieldEquiv
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4)
    (h : (cross (segreChartRow (netLinearRow M) k p)
      (segreChartRow (netQuadraticRow M) k p)).z ≠ 0) :
    FractionRing (SegreIncidenceMinorLocalization M k p) ≃ₐ[K]
      FractionRing (MvPolynomial (Fin 3) K) :=
  (IsFractionRing.algEquivOfAlgEquiv
    (segreIncidenceMinorLocalizationAlgEquiv M k p)).trans
      (threeVariableIncidenceFractionRingEquiv _ _ h)

set_option synthInstance.maxHeartbeats 100000 in
/-- The algebra comparison gives an actual affine scheme isomorphism. -/
def segreIncidenceMinorSchemeIso
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4) :
    Spec (CommRingCat.of (SegreIncidenceMinorLocalization M k p)) ≅
      Spec (CommRingCat.of
        (LocalizedIncidenceAlgebra (segreChartRow (netLinearRow M) k p)
          (segreChartRow (netQuadraticRow M) k p))) :=
  Scheme.Spec.mapIso
    (segreIncidenceMinorLocalizationAlgEquiv M k p).toRingEquiv.symm.toCommRingCatIso.op

/-- The minor-open Segre chart is the actual basic open defined by the
minor in the three-variable affine coefficient space. -/
def segreIncidenceMinorBasicOpenIso
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4) :
    Spec (CommRingCat.of (SegreIncidenceMinorLocalization M k p)) ≅
      Scheme.Opens.toScheme (X := Spec (CommRingCat.of (MvPolynomial (Fin 3) K)))
        (PrimeSpectrum.basicOpen
          (cross (segreChartRow (netLinearRow M) k p)
            (segreChartRow (netQuadraticRow M) k p)).z) :=
  segreIncidenceMinorSchemeIso M k p ≪≫ localizedIncidenceBasicOpenIso _ _

theorem segreIncidenceMinorScheme_nonempty_of_eval
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4) (x : Fin 3 → K)
    (h : eval x (cross (segreChartRow (netLinearRow M) k p)
      (segreChartRow (netQuadraticRow M) k p)).z ≠ 0) :
    Nonempty (Spec (CommRingCat.of (SegreIncidenceMinorLocalization M k p))) := by
  obtain ⟨y⟩ := localizedIncidenceScheme_nonempty_of_eval (eval x)
    (segreChartRow (netLinearRow M) k p) (segreChartRow (netQuadraticRow M) k p) h
  exact ⟨(segreIncidenceMinorSchemeIso M k p).inv.base y⟩

/-- From the original matrix-net assumptions obtain a nonempty genuine
Segre minor open with integral coordinate ring and a purely transcendental
function field, without assuming either an isomorphism or a nonzero minor. -/
theorem exists_rational_segreIncidenceMinor_after_common_point_normalization
    [Infinite K] (h2 : (2 : K) ≠ 0)
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (hM : ∀ i, (M i).IsSymm)
    (P : Fin 5 → K) (hP : P ≠ 0)
    (hisotropic : ∀ i, dotProduct P ((M i).mulVec P) = 0)
    (hsmooth : ∀ t : Fin 3 → K, t ≠ 0 → eval t (linearMatrixNet M).det = 0 →
      ∃ i, eval t (pderiv i (linearMatrixNet M).det) ≠ 0) :
    ∃ B : Matrix (Fin 5) (Fin 5) K, B.det ≠ 0 ∧ (∀ j, B j 0 = P j) ∧
      ∃ (k : Fin 3) (p : Fin 4),
        Nonempty (Spec (CommRingCat.of
          (SegreIncidenceMinorLocalization (matrixNetCongruence M B) k p))) ∧
        IsDomain (SegreIncidenceMinorLocalization (matrixNetCongruence M B) k p) ∧
        Nonempty (FractionRing
          (SegreIncidenceMinorLocalization (matrixNetCongruence M B) k p) ≃ₐ[K]
            FractionRing (MvPolynomial (Fin 3) K)) := by
  obtain ⟨B, hB, hcol, k, p, x, hx⟩ :=
    exists_canonical_segreChartRow_minor_after_common_point_normalization
      h2 M hM P hP hisotropic hsmooth
  have h : (cross (segreChartRow (netLinearRow (matrixNetCongruence M B)) k p)
      (segreChartRow (netQuadraticRow (matrixNetCongruence M B)) k p)).z ≠ 0 := by
    intro hz
    exact hx (by rw [hz, map_zero])
  exact ⟨B, hB, hcol, k, p,
    segreIncidenceMinorScheme_nonempty_of_eval _ k p x hx,
    segreIncidenceMinorLocalization_isDomain _ k p h,
    ⟨segreIncidenceMinorFractionFieldEquiv _ k p h⟩⟩

end EvenQuinticConic.Incidence
