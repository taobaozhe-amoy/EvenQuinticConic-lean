import EvenQuinticConic.IncidenceDominance
import EvenQuinticConic.IncidenceJacobianCongruence
import EvenQuinticConic.GlobalRationalIncidenceChart

/-!
# A rational incidence open dominating the actual parameter plane

From a symmetric matrix net, a nonzero common isotropic vector and the
geometric determinant Jacobian certificate, construct a nonempty integral
open of the actual global incidence scheme. Its fraction field is rational
over the ground field and its actual parameter projection is dominant.

The matrix normalization, nonzero minor, parameter pullback injectivity,
and dominance are conclusions, not additional inputs. This theorem does
not identify the incidence scheme with the original conic bundle, nor
assert integrality of the entire incidence scheme.
-/

noncomputable section
namespace EvenQuinticConic.Incidence
open Matrix MvPolynomial AlgebraicGeometry

variable {K : Type*} [Field K]

/-- The common-point construction has a rational integral open dominating
`P²`, under the actual geometric determinant Jacobian condition. -/
theorem exists_dominant_rational_globalIncidenceOpen_of_common_point
    [Infinite K] (h2 : (2 : K) ≠ 0)
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (hM : ∀ i, (M i).IsSymm)
    (P : Fin 5 → K) (hP : P ≠ 0)
    (hisotropic : ∀ i, dotProduct P ((M i).mulVec P) = 0)
    (hCert : ProjectiveJacobianCertificate (linearMatrixNet M).det) :
    ∃ B : Matrix (Fin 5) (Fin 5) K, B.det ≠ 0 ∧ (∀ j, B j 0 = P j) ∧
      ∃ (k : Fin 3) (p : Fin 4),
        ∃ h : (cross (segreChartRow (netLinearRow (matrixNetCongruence M B)) k p)
          (segreChartRow (netQuadraticRow (matrixNetCongruence M B)) k p)).z ≠ 0,
        Nonempty (globalIncidenceMinorOpen (matrixNetCongruence M B) p
          (k.succAbove 0) (k.succAbove 1) k) ∧
        IsIntegral (globalIncidenceMinorOpen (matrixNetCongruence M B) p
          (k.succAbove 0) (k.succAbove 1) k).toScheme ∧
        IsDominant (globalIncidenceMinorParameterProjection (matrixNetCongruence M B) k p h) ∧
        IsDomain (SegreIncidenceMinorLocalization (matrixNetCongruence M B) k p) ∧
        Nonempty (FractionRing
          (SegreIncidenceMinorLocalization (matrixNetCongruence M B) k p) ≃ₐ[K]
            FractionRing (MvPolynomial (Fin 3) K)) := by
  obtain ⟨B, hB, hcol, k, p, x, hx⟩ :=
    exists_canonical_segreChartRow_minor_after_common_point_normalization
      h2 M hM P hP hisotropic hCert.rational_jacobian
  have h : (cross (segreChartRow (netLinearRow (matrixNetCongruence M B)) k p)
      (segreChartRow (netQuadraticRow (matrixNetCongruence M B)) k p)).z ≠ 0 := by
    intro hz
    exact hx (by rw [hz, map_zero])
  have hbase : ∀ i, matrixNetCongruence M B i 0 0 = 0 := by
    intro i
    rw [matrixNetCongruence_zero_zero M B P hcol i, hisotropic i]
  refine ⟨B, hB, hcol, k, p, h,
    globalIncidenceMinorOpen_nonempty_of_ne_zero _ k p h,
    globalIncidenceMinorOpen_isIntegral _ k p h, ?_,
    segreIncidenceMinorLocalization_isDomain _ k p h,
    ⟨segreIncidenceMinorFractionFieldEquiv _ k p h⟩⟩
  exact globalIncidenceMinorParameterProjection_isDominant_of_geometricJacobian
    h2 (matrixNetCongruence M B) (matrixNetCongruence_isSymm M hM B) hbase
    (linearMatrixNet_congruence_jacobianCertificate M B hB hCert) k p h

end EvenQuinticConic.Incidence
