import EvenQuinticConic.IncidenceGenericConicChart
import EvenQuinticConic.TernaryConicIrreducibility

/-!
# Integrality of the actual generic incidence conic

The determinant of the original generic matrix and the actual selected polar
pivot imply nondegeneracy of the displayed ternary matrix. Irreducibility and
integrality are consequences, rather than additional geometric hypotheses.
The scheme here is the actual reduced projective plane locus already used in
the generic-fibre open immersion.
-/

noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace EvenQuinticConic.Incidence

open AlgebraicGeometry MvPolynomial

variable {K : Type*} [Field K]

/-- A nondegenerate symmetric ternary equation defines an integral reduced
projective plane curve over the given field. -/
theorem ternaryConicScheme_isIntegral
    (h2 : (2 : K) ≠ 0) (M : Matrix (Fin 3) (Fin 3) K)
    (hM : M.IsSymm) (hdet : M.det ≠ 0) :
    IsIntegral (PlaneCurveScheme (matrixQuadraticPolynomial M)) := by
  apply planeCurveScheme_isIntegral _ 2 (matrixQuadraticPolynomial_homogeneous M)
  · rw [ternary_matrixQuadraticPolynomial_totalDegree h2 M hM hdet]
    decide
  · exact ternary_matrixQuadraticPolynomial_principal_isPrime h2 M hM hdet

section Geometric

variable [Infinite K] (h2 : (2 : K) ≠ 0)
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (hM : ∀ i, (M i).IsSymm)
    (hbase : ∀ i, M i 0 0 = 0)
    (hCert : ProjectiveJacobianCertificate (linearMatrixNet M).det)
    (k : Fin 3) (p : Fin 4)
    (h : (cross (segreChartRow (netLinearRow M) k p)
      (segreChartRow (netQuadraticRow M) k p)).z ≠ 0)
    (q : Fin 3) (hq : incidenceGenericMatrix M k p h (p.succAbove q).succ 0 ≠ 0)

include h2 in
omit [Infinite K] in
/-- The actual parameter subfield has the same characteristic restriction. -/
theorem incidenceParameterSubfield_two_ne_zero :
    (2 : incidenceParameterSubfield M k p h) ≠ 0 := by
  simpa only [map_ofNat] using
    (map_ne_zero (algebraMap K (incidenceParameterSubfield M k p h))).mpr h2

include h2 hM hbase hCert hq in
/-- Every valid selected affine pivot gives a nondegenerate actual ternary
matrix; this is deduced from the original geometric Jacobian certificate. -/
theorem incidenceGenericConicMatrix_det_ne_zero_of_geometricJacobian :
    (incidenceGenericConicMatrix M k p h (p.succAbove q)).det ≠ 0 := by
  exact incidencePivotRestrictedMatrix_det_ne_zero
    (incidenceGenericMatrix M k p h)
    (incidenceGenericMatrix_isSymm M hM k p h)
    (incidenceGenericMatrix_zero_zero M hbase k p h) (p.succAbove q) hq
    (incidenceGenericMatrix_det_ne_zero h2 M hM hbase hCert k p h)

include h2 hM hbase hCert hq in
/-- The actual homogeneous equation has degree exactly two. -/
theorem incidenceGenericConicPolynomial_totalDegree :
    (incidenceGenericConicPolynomial M k p h q).totalDegree = 2 := by
  exact ternary_matrixQuadraticPolynomial_totalDegree
    (incidenceParameterSubfield_two_ne_zero h2 M k p h) _
    (incidenceGenericConicMatrix_isSymm M hM k p h (p.succAbove q))
    (incidenceGenericConicMatrix_det_ne_zero_of_geometricJacobian
      h2 M hM hbase hCert k p h q hq)

include h2 hM hbase hCert hq in
/-- Irreducibility of the actual equation, without an irreducibility input. -/
theorem incidenceGenericConicPolynomial_irreducible :
    Irreducible (incidenceGenericConicPolynomial M k p h q) := by
  exact ternary_matrixQuadraticPolynomial_irreducible
    (incidenceParameterSubfield_two_ne_zero h2 M k p h) _
    (incidenceGenericConicMatrix_isSymm M hM k p h (p.succAbove q))
    (incidenceGenericConicMatrix_det_ne_zero_of_geometricJacobian
      h2 M hM hbase hCert k p h q hq)

include h2 hM hbase hCert hq in
/-- The actual principal ideal is prime, not merely radical after localization. -/
theorem incidenceGenericConicPolynomial_principal_isPrime :
    (Ideal.span {incidenceGenericConicPolynomial M k p h q}).IsPrime := by
  exact plane_principal_isPrime_of_irreducible _
    (incidenceGenericConicPolynomial_irreducible h2 M hM hbase hCert k p h q hq)

include h2 hM hbase hCert hq in
/-- The whole actual generic incidence conic is integral. This supplies the
target hypothesis needed for its actual generic-stalk function field. -/
theorem incidenceGenericConicScheme_isIntegral :
    IsIntegral (IncidenceGenericConicScheme M k p h q) := by
  exact ternaryConicScheme_isIntegral
    (incidenceParameterSubfield_two_ne_zero h2 M k p h) _
    (incidenceGenericConicMatrix_isSymm M hM k p h (p.succAbove q))
    (incidenceGenericConicMatrix_det_ne_zero_of_geometricJacobian
      h2 M hM hbase hCert k p h q hq)

end Geometric

end EvenQuinticConic.Incidence
