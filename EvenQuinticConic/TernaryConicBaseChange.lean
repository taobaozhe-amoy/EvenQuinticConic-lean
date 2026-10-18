import EvenQuinticConic.PlaneCurveChartBaseChange
import EvenQuinticConic.PlaneCurveFieldBaseChangeCover
import EvenQuinticConic.TernaryConicIrreducibility

/-!
# Integrality of the actual conic after every field extension

The conclusion concerns the categorical pullback of the original curve,
not a newly defined curve over the extension field. The comparison is made
on all three actual affine charts, retaining both projection maps, and then
integrality is glued along their proved nonempty intersections.

The scheme interfaces in this file use fields in `Type` (universe zero).
-/

noncomputable section

namespace EvenQuinticConic

open AlgebraicGeometry MvPolynomial

variable {K L : Type} [Field K] [Field L] [Algebra K L]

/-- Primality and degree of the actual extended equation imply integrality
of the actual pullback of the original projective plane curve. -/
theorem planeCurveFieldBaseChange_isIntegral_of_prime
    (F : PlanePolynomial K) (d : ℕ) (hF : F.IsHomogeneous d)
    (hFdeg : 1 < F.totalDegree) (hprime : (Ideal.span {F}).IsPrime)
    (hFdegL : 1 < (MvPolynomial.map (algebraMap K L) F).totalDegree)
    (hprimeL : (Ideal.span {MvPolynomial.map (algebraMap K L) F}).IsPrime) :
    IsIntegral (PlaneCurveFieldBaseChange L F) := by
  apply planeCurveFieldBaseChange_isIntegral_of_charts L F d hF hFdeg hprime
  intro i
  letI := planeCurveAffineEquationAlgebra_isDomain
    (MvPolynomial.map (algebraMap K L) F) d (hF.map (algebraMap K L))
    hFdegL hprimeL i
  exact planeCurveChartBaseChange_isIntegral (L := L) F d hF hFdeg hprime i

namespace Incidence

/-- Every extension field preserves integrality of the actual projective
conic. Nondegeneracy supplies every primality and domain condition internally;
no rational point, algebraic closedness, or geometric-integrality input occurs. -/
theorem ternaryConicFieldBaseChange_isIntegral
    (h2 : (2 : K) ≠ 0) (M : Matrix (Fin 3) (Fin 3) K)
    (hM : M.IsSymm) (hdet : M.det ≠ 0) :
    IsIntegral (PlaneCurveFieldBaseChange L (matrixQuadraticPolynomial M)) := by
  have hhom := matrixQuadraticPolynomial_homogeneous M
  have hdeg : 1 < (matrixQuadraticPolynomial M).totalDegree := by
    rw [ternary_matrixQuadraticPolynomial_totalDegree h2 M hM hdet]
    decide
  have hhomL := hhom.map (algebraMap K L)
  have hirrL := ternary_matrixQuadraticPolynomial_irreducible_over_field
    h2 M hM hdet (algebraMap K L)
  have hdegL :
      1 < (MvPolynomial.map (algebraMap K L) (matrixQuadraticPolynomial M)).totalDegree := by
    rw [hhomL.totalDegree hirrL.ne_zero]
    decide
  exact planeCurveFieldBaseChange_isIntegral_of_prime (L := L) _ 2 hhom hdeg
    (ternary_matrixQuadraticPolynomial_principal_isPrime h2 M hM hdet) hdegL
    (ternary_matrixQuadraticPolynomial_principal_isPrime_over_field
      h2 M hM hdet (algebraMap K L))

end Incidence

end EvenQuinticConic
