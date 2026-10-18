import EvenQuinticConic.IncidenceGenericConicGeometry
import EvenQuinticConic.TernaryConicSmooth

/-!
# Smoothness of the actual generic incidence conic

The actual selected ternary matrix is nondegenerate by the geometric Jacobian
certificate of the original matrix net. Its displayed projective conic is
therefore integral and smooth of relative dimension one over the actual
parameter subfield. These are conclusions, not additional inputs.
-/

noncomputable section

namespace EvenQuinticConic.Incidence

open AlgebraicGeometry

variable {K : Type} [Field K] [Infinite K]
    (h2 : (2 : K) ≠ 0)
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (hM : ∀ i, (M i).IsSymm)
    (hbase : ∀ i, M i 0 0 = 0)
    (hCert : ProjectiveJacobianCertificate (linearMatrixNet M).det)
    (k : Fin 3) (p : Fin 4)
    (h : (cross (segreChartRow (netLinearRow M) k p)
      (segreChartRow (netQuadraticRow M) k p)).z ≠ 0)
    (q : Fin 3) (hq : incidenceGenericMatrix M k p h (p.succAbove q).succ 0 ≠ 0)

include h2 hM hbase hCert hq in
/-- The actual generic conic structure morphism is smooth of relative dimension
one over its actual parameter subfield. No algebraic closedness, rational
point, primality, or smoothness hypothesis is added. -/
theorem incidenceGenericConicStructure_isSmoothOfRelativeDimension :
    IsSmoothOfRelativeDimension 1
      (planeCurveStructure (incidenceGenericConicPolynomial M k p h q)) := by
  exact ternaryConicStructure_isSmoothOfRelativeDimension
    (incidenceParameterSubfield_two_ne_zero h2 M k p h) _
    (incidenceGenericConicMatrix_isSymm M hM k p h (p.succAbove q))
    (incidenceGenericConicMatrix_det_ne_zero_of_geometricJacobian
      h2 M hM hbase hCert k p h q hq)

include h2 hM hbase hCert hq in
/-- Smoothness of the same actual structure morphism, with its relative
dimension forgotten. -/
theorem incidenceGenericConicStructure_isSmooth :
    IsSmooth (planeCurveStructure (incidenceGenericConicPolynomial M k p h q)) := by
  letI := incidenceGenericConicStructure_isSmoothOfRelativeDimension
    h2 M hM hbase hCert k p h q hq
  exact IsSmoothOfRelativeDimension.isSmooth 1 _

include h2 hM hbase hCert hq in
/-- The whole displayed generic conic is simultaneously integral and smooth
of relative dimension one, derived from the original geometric inputs. -/
theorem incidenceGenericConicScheme_integral_and_smooth :
    IsIntegral (IncidenceGenericConicScheme M k p h q) ∧
      IsSmoothOfRelativeDimension 1
        (planeCurveStructure (incidenceGenericConicPolynomial M k p h q)) :=
  ⟨incidenceGenericConicScheme_isIntegral h2 M hM hbase hCert k p h q hq,
    incidenceGenericConicStructure_isSmoothOfRelativeDimension
      h2 M hM hbase hCert k p h q hq⟩

end EvenQuinticConic.Incidence
