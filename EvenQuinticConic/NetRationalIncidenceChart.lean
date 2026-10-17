import EvenQuinticConic.IncidenceProjectiveChart
import EvenQuinticConic.ProjectiveThreeDensity
import EvenQuinticConic.ProjectiveThreeChartRing
import EvenQuinticConic.IncidenceFunctionField
import Mathlib.AlgebraicGeometry.FunctionField

/-!
# A rational function field for the actual projective incidence chart

The coefficient ring is the genuine degree-zero ring of a projective
standard chart. Its three-variable polynomial presentation, the elimination
of the incidence equations, and the fraction-ring comparison are composed
here. In particular the final field isomorphism preserves the ground field.
The nonempty chart is derived from an actual symmetric matrix net and its
common isotropic point, with the determinant Jacobian condition.

This does not identify a global incidence scheme or the original conic
bundle with this locally defined scheme.
-/

noncomputable section
namespace EvenQuinticConic.Incidence

open MvPolynomial AlgebraicGeometry CategoryTheory

variable {K : Type*} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The projective chart ring is a domain because it is actually a
polynomial ring in three variables. -/
theorem projectiveThreeChartRing_isDomain (p : Fin 4) :
    IsDomain (ProjectiveThreeChartRing (K := K) p) :=
  Function.Injective.isDomain (projectiveThreeChartRingEquiv p)
    (projectiveThreeChartRingEquiv p).injective

attribute [local instance] projectiveThreeChartRing_isDomain

local instance projectiveChartAlgebra (p : Fin 4) :
    Algebra K (ProjectiveThreeChartRing (K := K) p) := threeChartAlgebra p

/-- The literal coordinate algebra used in the actual projective incidence
scheme, not an auxiliary rational model. -/
abbrev NetProjectiveIncidenceAlgebra
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (p : Fin 4) (i j k : Fin 3) :=
  LocalizedIncidenceAlgebra (projectiveNetLinearRow M p i j k)
    (projectiveNetQuadraticRow M p i j k)

/-- Nonvanishing of the original minor proves nonvanishing in the genuine
degree-zero projective chart ring. -/
theorem projectiveNetMinor_ne_zero_of_eval
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (p : Fin 4) (i j k : Fin 3)
    (y : Fin 4 → K) (hyp : y p ≠ 0) (hy : eval y (netIncidenceMinor M i j) ≠ 0) :
    (cross (projectiveNetLinearRow M p i j k) (projectiveNetQuadraticRow M p i j k)).z ≠ 0 := by
  intro hz
  have he := projectiveNetMinor_eval M p i j k y hyp
  rw [hz, map_zero] at he
  exact (mul_ne_zero hy (pow_ne_zero _ (inv_ne_zero hyp))) he.symm

/-- Integrality of the actual projective incidence coordinate algebra is
derived from the original minor evaluation. -/
theorem netProjectiveIncidenceAlgebra_isDomain_of_eval
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (p : Fin 4) (i j k : Fin 3)
    (y : Fin 4 → K) (hyp : y p ≠ 0) (hy : eval y (netIncidenceMinor M i j) ≠ 0) :
    IsDomain (NetProjectiveIncidenceAlgebra M p i j k) :=
  localizedIncidence_isDomain _ _ (projectiveNetMinor_ne_zero_of_eval M p i j k y hyp hy)

/-- The actual quotient coordinate algebra has a purely transcendental
fraction field of degree three, through a ground-field algebra isomorphism. -/
def netProjectiveIncidenceFractionFieldEquiv
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (p : Fin 4) (i j k : Fin 3)
    (h : (cross (projectiveNetLinearRow M p i j k)
      (projectiveNetQuadraticRow M p i j k)).z ≠ 0) :
    FractionRing (NetProjectiveIncidenceAlgebra M p i j k) ≃ₐ[K]
      FractionRing (MvPolynomial (Fin 3) K) :=
  ((localizedIncidenceFractionRingAlgEquiv _ _ h).restrictScalars K).trans
    (IsFractionRing.algEquivOfAlgEquiv (projectiveThreeChartAlgEquiv p))

/-- The corresponding actual affine scheme is integral, with the domain
property obtained from its defining equations and nonzero minor. -/
theorem netProjectiveIncidenceChart_isIntegral
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (p : Fin 4) (i j k : Fin 3)
    (h : (cross (projectiveNetLinearRow M p i j k)
      (projectiveNetQuadraticRow M p i j k)).z ≠ 0) :
    IsIntegral (netProjectiveIncidenceChart M p i j k) := by
  letI := localizedIncidence_isDomain _ _ h
  change IsIntegral (Spec (CommRingCat.of (NetProjectiveIncidenceAlgebra M p i j k)))
  infer_instance

/-- Structural ground-field action on the actual net chart's generic stalk. -/
def netProjectiveIncidenceGenericStalkAlgebra
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (p : Fin 4) (i j k : Fin 3)
    (h : (cross (projectiveNetLinearRow M p i j k)
      (projectiveNetQuadraticRow M p i j k)).z ≠ 0) :
    letI := netProjectiveIncidenceChart_isIntegral M p i j k h
    Algebra K (netProjectiveIncidenceChart M p i j k).functionField := by
  letI := netProjectiveIncidenceChart_isIntegral M p i j k h
  letI := localizedIncidence_isDomain _ _ h
  change Algebra K (Spec (CommRingCat.of (NetProjectiveIncidenceAlgebra M p i j k))).functionField
  exact localizedIncidenceGenericStalkAlgebra (k := K) _ _ h

/-- The field of the actual integral affine scheme, defined as its generic
stalk, is the rational function field with the actual structural scalars. -/
def netProjectiveIncidenceGenericStalkEquiv
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (p : Fin 4) (i j k : Fin 3)
    (h : (cross (projectiveNetLinearRow M p i j k)
      (projectiveNetQuadraticRow M p i j k)).z ≠ 0) :
    letI := localizedIncidence_isDomain _ _ h
    letI := netProjectiveIncidenceChart_isIntegral M p i j k h
    letI := netProjectiveIncidenceGenericStalkAlgebra M p i j k h
    (netProjectiveIncidenceChart M p i j k).functionField ≃ₐ[K]
      FractionRing (MvPolynomial (Fin 3) K) := by
  letI := localizedIncidence_isDomain _ _ h
  letI := netProjectiveIncidenceChart_isIntegral M p i j k h
  letI := netProjectiveIncidenceGenericStalkAlgebra M p i j k h
  letI := localizedIncidenceGenericStalkAlgebra (k := K) _ _ h
  exact (localizedIncidenceGenericStalkAlgEquiv (k := K) _ _ h).trans
    (IsFractionRing.algEquivOfAlgEquiv (projectiveThreeChartAlgEquiv p))

/-- Assembled output from the actual matrix net: a nonempty actual
projective open, the incidence-chart scheme isomorphism, an integral
coordinate algebra, and its ground-field rational function-field
isomorphism. None of these conclusions is supplied as an input. -/
theorem exists_rational_projectiveIncidenceChart_of_common_point
    [Infinite K] (h2 : (2 : K) ≠ 0)
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (hM : ∀ i, (M i).IsSymm)
    (P : Fin 5 → K) (hP : P ≠ 0)
    (hisotropic : ∀ i, dotProduct P ((M i).mulVec P) = 0)
    (hsmooth : ∀ t : Fin 3 → K, t ≠ 0 → eval t (linearMatrixNet M).det = 0 →
      ∃ i, eval t (pderiv i (linearMatrixNet M).det) ≠ 0) :
    ∃ B : Matrix (Fin 5) (Fin 5) K, B.det ≠ 0 ∧ (∀ j, B j 0 = P j) ∧
      ∃ (p : Fin 4) (i j k : Fin 3), i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
        Nonempty (netProjectiveIncidenceOpen (matrixNetCongruence M B) p i j k) ∧
        Dense (netProjectiveIncidenceOpen (matrixNetCongruence M B) p i j k :
          Set (ProjectiveThreeScheme K)) ∧
        Nonempty (netProjectiveIncidenceChart (matrixNetCongruence M B) p i j k ≅
          (netProjectiveIncidenceOpen (matrixNetCongruence M B) p i j k).toScheme) ∧
        IsDomain (NetProjectiveIncidenceAlgebra (matrixNetCongruence M B) p i j k) ∧
        Nonempty (FractionRing (NetProjectiveIncidenceAlgebra (matrixNetCongruence M B)
          p i j k) ≃ₐ[K] FractionRing (MvPolynomial (Fin 3) K)) := by
  obtain ⟨B, hB, hcol, i, j, y, hij, hy0, hy⟩ :=
    exists_projective_netIncidenceMinor_after_common_point_normalization
      h2 M hM P hP hisotropic hsmooth
  obtain ⟨p, hyp⟩ : ∃ p, y p ≠ 0 := by
    by_contra! h
    exact hy0 (funext h)
  obtain ⟨k, hik, hjk⟩ : ∃ k : Fin 3, i ≠ k ∧ j ≠ k := by
    fin_cases i <;> fin_cases j <;> first | exact (hij rfl).elim | decide
  exact ⟨B, hB, hcol, p, i, j, k, hij, hik, hjk,
    netProjectiveIncidenceOpen_nonempty_of_eval _ p i j k y hyp hy,
    netProjectiveIncidenceOpen_dense_of_eval _ p i j k y hyp hy,
    ⟨netProjectiveIncidenceOpenIso _ p i j k⟩,
    netProjectiveIncidenceAlgebra_isDomain_of_eval _ p i j k y hyp hy,
    ⟨netProjectiveIncidenceFractionFieldEquiv _ p i j k
      (projectiveNetMinor_ne_zero_of_eval _ p i j k y hyp hy)⟩⟩

end EvenQuinticConic.Incidence
