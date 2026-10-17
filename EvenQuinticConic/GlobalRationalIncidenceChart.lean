import EvenQuinticConic.GlobalIncidenceOpenChart

/-!
# A nonempty rational open of the actual global incidence scheme

The matrix-net assumptions now produce an open of the actual global
projective incidence scheme, with its actual affine coordinate algebra.
Neither an open-chart isomorphism nor the nonzero minor is an input of
the assembled endpoint. This does not assert density in the whole global
incidence scheme, dominance over the parameter plane, or comparison with
the conic bundle in the original problem.
-/

noncomputable section
namespace EvenQuinticConic.Incidence

open MvPolynomial AlgebraicGeometry CategoryTheory

variable {K : Type*} [Field K]

/-- Nonvanishing of the actual coefficient minor makes the constructed
open of the global incidence scheme nonempty. -/
theorem globalIncidenceMinorOpen_nonempty_of_ne_zero
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4)
    (h : (cross (segreChartRow (netLinearRow M) k p)
      (segreChartRow (netQuadraticRow M) k p)).z ≠ 0) :
    Nonempty (globalIncidenceMinorOpen M p (k.succAbove 0) (k.succAbove 1) k) := by
  letI := segreIncidenceMinorLocalization_isDomain M k p h
  let e := globalIncidenceMinorOpenIso M p k h
  exact Nonempty.map e.inv.base inferInstance

/-- This actual open is integral; no integrality assertion is made about
the entire global incidence scheme. -/
theorem globalIncidenceMinorOpen_isIntegral
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4)
    (h : (cross (segreChartRow (netLinearRow M) k p)
      (segreChartRow (netQuadraticRow M) k p)).z ≠ 0) :
    IsIntegral
      (globalIncidenceMinorOpen M p (k.succAbove 0) (k.succAbove 1) k).toScheme := by
  letI := segreIncidenceMinorLocalization_isDomain M k p h
  letI := globalIncidenceMinorOpen_nonempty_of_ne_zero M k p h
  exact isIntegral_of_isOpenImmersion (globalIncidenceMinorOpenIso M p k h).hom

/-- From the actual matrix net, arbitrary common point, and determinant
Jacobian condition, construct a nonempty integral open of the actual
global incidence scheme and its affine algebra with rational fraction
field over the given ground field. All comparisons and nonvanishing
conditions are derived internally. -/
theorem exists_nonempty_rational_globalIncidenceOpen_of_common_point
    [Infinite K] (h2 : (2 : K) ≠ 0)
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (hM : ∀ i, (M i).IsSymm)
    (P : Fin 5 → K) (hP : P ≠ 0)
    (hisotropic : ∀ i, dotProduct P ((M i).mulVec P) = 0)
    (hsmooth : ∀ t : Fin 3 → K, t ≠ 0 → eval t (linearMatrixNet M).det = 0 →
      ∃ i, eval t (pderiv i (linearMatrixNet M).det) ≠ 0) :
    ∃ B : Matrix (Fin 5) (Fin 5) K, B.det ≠ 0 ∧ (∀ j, B j 0 = P j) ∧
      ∃ (k : Fin 3) (p : Fin 4),
        Nonempty (globalIncidenceMinorOpen (matrixNetCongruence M B) p
          (k.succAbove 0) (k.succAbove 1) k) ∧
        IsIntegral (globalIncidenceMinorOpen (matrixNetCongruence M B) p
          (k.succAbove 0) (k.succAbove 1) k).toScheme ∧
        (∃ e : (globalIncidenceMinorOpen (matrixNetCongruence M B) p
          (k.succAbove 0) (k.succAbove 1) k).toScheme ≅
          Spec (CommRingCat.of
            (SegreIncidenceMinorLocalization (matrixNetCongruence M B) k p)),
          e.inv ≫ (globalIncidenceMinorOpen (matrixNetCongruence M B) p
            (k.succAbove 0) (k.succAbove 1) k).ι ≫
              globalIncidenceStructure (matrixNetCongruence M B) =
            Spec.map (CommRingCat.ofHom
              (algebraMap K (SegreIncidenceMinorLocalization (matrixNetCongruence M B) k p)))) ∧
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
    globalIncidenceMinorOpen_nonempty_of_ne_zero _ k p h,
    globalIncidenceMinorOpen_isIntegral _ k p h,
    ⟨globalIncidenceMinorOpenIso _ p k h,
      globalIncidenceMinorOpenIso_inv_comp_structure _ p k h⟩,
    segreIncidenceMinorLocalization_isDomain _ k p h,
    ⟨segreIncidenceMinorFractionFieldEquiv _ k p h⟩⟩

end EvenQuinticConic.Incidence
