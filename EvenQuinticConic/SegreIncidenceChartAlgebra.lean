import EvenQuinticConic.SegreChartAlgebra
import EvenQuinticConic.SegreIncidenceEquations
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# The actual incidence equations in a standard Segre chart

The remaining coordinates on the two projective factors are put in their
original order. This identifies the polynomial algebra of the Segre chart
with a polynomial algebra in two first-factor variables over the algebra
of the three second-factor variables. The actual incidence equations will
then define the two-equation affine incidence algebra.
-/

noncomputable section

namespace EvenQuinticConic.Incidence

open MvPolynomial SegreChart

variable {K : Type*} [Field K]

/-- Order the nonpivot variables of both factors using `Fin.succAbove`. -/
def segreChartVariableEquiv (k : Fin 3) (p : Fin 4) :
    SegreChartVariables k p ≃ Fin 2 ⊕ Fin 3 :=
  Equiv.sumCongr (finSuccAboveEquiv k).symm (finSuccAboveEquiv p).symm

/-- The actual chart polynomial algebra, with first-factor variables outside
and second-factor variables in the coefficient ring. -/
def segreChartNestedAlgEquiv (k : Fin 3) (p : Fin 4) :
    MvPolynomial (SegreChartVariables k p) K ≃ₐ[K]
      MvPolynomial (Fin 2) (MvPolynomial (Fin 3) K) :=
  (renameEquiv K (segreChartVariableEquiv k p)).trans
    (sumAlgEquiv K (Fin 2) (Fin 3))

@[simp] theorem segreChartNestedAlgEquiv_left (k : Fin 3) (p : Fin 4) (i : Fin 3) :
    segreChartNestedAlgEquiv (K := K) k p (segreChartLeftCoordinate K k p i) =
      segreChartT (K := K) k i := by
  induction i using k.succAboveCases with
  | x => simp [segreChartT]
  | p j =>
    simp [segreChartLeftCoordinate, k.succAbove_ne j, segreChartNestedAlgEquiv,
      segreChartVariableEquiv, ← finSuccAboveEquiv_apply, segreChartT]

@[simp] theorem segreChartNestedAlgEquiv_right (k : Fin 3) (p : Fin 4) (j : Fin 4) :
    segreChartNestedAlgEquiv (K := K) k p (segreChartRightCoordinate K k p j) =
      C (dehomogenizeAt p (X j)) := by
  induction j using p.succAboveCases with
  | x => simp
  | p a =>
    simp [segreChartRightCoordinate, p.succAbove_ne a, segreChartNestedAlgEquiv,
      segreChartVariableEquiv, ← finSuccAboveEquiv_apply]

@[simp] theorem segreChartNestedAlgEquiv_eval_X
    (k : Fin 3) (p : Fin 4) (i : Fin 3) (j : Fin 4) :
    segreChartNestedAlgEquiv (K := K) k p (segreChartEval K k p (X (i, j))) =
      segreChartT (K := K) k i * C (dehomogenizeAt p (X j)) := by simp

/-- Nesting the Segre chart coordinates is exactly the explicit incidence
chart substitution, on every polynomial. -/
theorem segreChartNestedAlgEquiv_comp_eval (k : Fin 3) (p : Fin 4) :
    (segreChartNestedAlgEquiv (K := K) k p).toAlgHom.comp (segreChartEval K k p) =
      segreIncidenceChartSubstitution k p := by
  ext q
  rcases q with ⟨i, j⟩
  simp [segreIncidenceChartSubstitution, segreChartY]

@[simp] theorem segreChartNestedAlgEquiv_eval
    (k : Fin 3) (p : Fin 4) (F : MvPolynomial SegreIndex K) :
    segreChartNestedAlgEquiv (K := K) k p (segreChartEval K k p F) =
      segreIncidenceChartSubstitution k p F :=
  AlgHom.congr_fun (segreChartNestedAlgEquiv_comp_eval k p) F

/-- The one linear and three quadratic homogeneous incidence equations. -/
def segreExtraIncidenceEquationSet (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) :
    Set (MvPolynomial SegreIndex K) :=
  {segreIncidenceLinear M} ∪ Set.range (segreIncidenceQuadratic M)

/-- On a standard Segre chart the ideal of all four actual incidence
equations equals the ideal of the two normalized row polynomials. -/
theorem segreIncidenceChart_equations_ideal
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4) :
    Ideal.span (segreIncidenceChartSubstitution k p '' segreExtraIncidenceEquationSet M) =
      affineIncidenceIdeal (segreChartRow (netLinearRow M) k p)
        (segreChartRow (netQuadraticRow M) k p) := by
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨F, hF, rfl⟩
    rcases hF with hF | ⟨a, rfl⟩
    · rcases Set.mem_singleton_iff.mp hF with rfl
      rw [segreIncidenceChartSubstitution_linear]
      exact Ideal.subset_span (by simp)
    · rw [segreIncidenceChartSubstitution_quadratic]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
  · rw [affineIncidenceIdeal, Ideal.span_le]
    intro F hF
    rcases Set.mem_insert_iff.mp hF with rfl | hF
    · rw [← segreIncidenceChartSubstitution_linear M k p]
      exact Ideal.subset_span ⟨_, Or.inl (Set.mem_singleton _), rfl⟩
    · rcases Set.mem_singleton_iff.mp hF with rfl
      rw [← segreIncidenceChartSubstitution_quadratic_pivot M k p]
      exact Ideal.subset_span ⟨_, Or.inr ⟨k, rfl⟩, rfl⟩

/-- The actual Segre equations, incidence equations, and pivot equation
define this quotient; no reduced structure or comparison is postulated. -/
abbrev SegreIncidenceChartAlgebra
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4) :=
  MvPolynomial SegreIndex K ⧸
    (segreChartIdeal K k p ⊔ Ideal.span (segreExtraIncidenceEquationSet M))

/-- Exact transport of the additional ideal under the explicit variable
ordering equivalence. -/
theorem segreIncidenceChart_nested_ideal_map
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4) :
    affineIncidenceIdeal (segreChartRow (netLinearRow M) k p)
        (segreChartRow (netQuadraticRow M) k p) =
      (Ideal.span (segreChartEval K k p '' segreExtraIncidenceEquationSet M)).map
        (segreChartNestedAlgEquiv (K := K) k p).toRingHom := by
  rw [Ideal.map_span, Set.image_image]
  have hfun : (fun x => segreChartNestedAlgEquiv (K := K) k p
      (segreChartEval K k p x)) = segreIncidenceChartSubstitution k p := by
    funext F
    exact segreChartNestedAlgEquiv_eval k p F
  change _ = Ideal.span ((fun x => segreChartNestedAlgEquiv (K := K) k p
    (segreChartEval K k p x)) '' segreExtraIncidenceEquationSet M)
  rw [hfun]
  exact (segreIncidenceChart_equations_ideal M k p).symm

/-- The genuine Segre incidence chart algebra is the existing, unlocalized
two-equation affine incidence algebra. This is an isomorphism of algebras
including any nilpotent structure. -/
def segreIncidenceChartAlgEquiv
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4) :
    SegreIncidenceChartAlgebra M k p ≃ₐ[K]
      AffineIncidenceAlgebra (segreChartRow (netLinearRow M) k p)
        (segreChartRow (netQuadraticRow M) k p) :=
  (segreChartWithEquationsAlgEquiv K k p (segreExtraIncidenceEquationSet M)).trans
    (Ideal.quotientEquivAlg _ _ (segreChartNestedAlgEquiv k p)
      (segreIncidenceChart_nested_ideal_map M k p))

/-- On the actual quotient the isomorphism is the literal normalized Segre
substitution, rather than an unspecified algebra isomorphism. -/
@[simp] theorem segreIncidenceChartAlgEquiv_mk
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4)
    (F : MvPolynomial SegreIndex K) :
    segreIncidenceChartAlgEquiv M k p (Ideal.Quotient.mk _ F) =
      Ideal.Quotient.mk _ (segreIncidenceChartSubstitution k p F) := by
  change Ideal.Quotient.mk _
    (segreChartNestedAlgEquiv (K := K) k p (segreChartEval K k p F)) = _
  rw [segreChartNestedAlgEquiv_eval]

@[simp] theorem segreIncidenceChartAlgEquiv_coordinate
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4)
    (i : Fin 3) (j : Fin 4) :
    segreIncidenceChartAlgEquiv M k p (Ideal.Quotient.mk _ (X (i, j))) =
      Ideal.Quotient.mk _ (segreChartT (K := K) k i * segreChartY p j) := by
  simp [segreIncidenceChartSubstitution]

/-- The homogeneous cubic used to cut out the minor open becomes the
constant polynomial defined by the actual dehomogenized minor. -/
@[simp] theorem segreIncidenceChartAlgEquiv_minor
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4)
    (i j : Fin 3) :
    segreIncidenceChartAlgEquiv M k p
        (Ideal.Quotient.mk _ (globalIncidenceMinor M i j k)) =
      algebraMap (MvPolynomial (Fin 3) K)
        (AffineIncidenceAlgebra (segreChartRow (netLinearRow M) k p)
          (segreChartRow (netQuadraticRow M) k p))
        (netDehomogenizedMinor M p i j) := by
  rw [segreIncidenceChartAlgEquiv_mk, segreIncidenceChartSubstitution_minor]
  rfl

/-- Reading the pivot row gives exactly the coefficient chart coordinates. -/
@[simp] theorem segreIncidenceChartAlgEquiv_pivotRow
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4) (j : Fin 4) :
    segreIncidenceChartAlgEquiv M k p (Ideal.Quotient.mk _ (X (k, j))) =
      algebraMap (MvPolynomial (Fin 3) K)
        (AffineIncidenceAlgebra (segreChartRow (netLinearRow M) k p)
          (segreChartRow (netQuadraticRow M) k p))
        (dehomogenizeAt p (X j)) := by
  rw [segreIncidenceChartAlgEquiv_coordinate, segreChartT_pivot, one_mul]
  rfl

/-- Reading the pivot column gives exactly the two first-factor variables. -/
@[simp] theorem segreIncidenceChartAlgEquiv_pivotColumn
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4) (i : Fin 2) :
    segreIncidenceChartAlgEquiv M k p
        (Ideal.Quotient.mk _ (X (k.succAbove i, p))) =
      Ideal.Quotient.mk _ (X i) := by
  rw [segreIncidenceChartAlgEquiv_coordinate, segreChartY_pivot,
    segreChartT_succAbove, mul_one]

/-- The minor used by affine elimination is literally the old
dehomogenized net minor at the two retained first-factor coordinates. -/
theorem segreChartRow_cross_z
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4) :
    (cross (segreChartRow (netLinearRow M) k p)
      (segreChartRow (netQuadraticRow M) k p)).z =
      netDehomogenizedMinor M p (k.succAbove 0) (k.succAbove 1) := by
  rw [netDehomogenizedMinor_eq]
  rfl

theorem netDehomogenizedMinor_swap
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (p : Fin 4) (i j : Fin 3) :
    netDehomogenizedMinor M p j i = -netDehomogenizedMinor M p i j := by
  simp only [netDehomogenizedMinor_eq]
  ring

/-- A nonzero minor can always be put in the canonical ordering of one
of the three first-factor charts. -/
theorem exists_canonical_segreChartRow_minor_eval_ne_zero
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (p : Fin 4) (x : Fin 3 → K)
    (i j : Fin 3) (hij : i ≠ j)
    (hminor : eval x (netDehomogenizedMinor M p i j) ≠ 0) :
    ∃ k : Fin 3, eval x (cross (segreChartRow (netLinearRow M) k p)
      (segreChartRow (netQuadraticRow M) k p)).z ≠ 0 := by
  have hs : eval x (netDehomogenizedMinor M p j i) ≠ 0 := by
    rw [netDehomogenizedMinor_swap, map_neg]
    exact neg_ne_zero.mpr hminor
  fin_cases i <;> fin_cases j
  all_goals try exact (hij rfl).elim
  · exact ⟨2, by simpa only [segreChartRow_cross_z] using hminor⟩
  · exact ⟨1, by simpa only [segreChartRow_cross_z] using hminor⟩
  · exact ⟨2, by simpa only [segreChartRow_cross_z] using hs⟩
  · exact ⟨0, by simpa only [segreChartRow_cross_z] using hminor⟩
  · exact ⟨1, by simpa only [segreChartRow_cross_z] using hs⟩
  · exact ⟨0, by simpa only [segreChartRow_cross_z] using hs⟩

/-- The hypotheses on the actual symmetric net and its common point
produce a chart with the exact minor inverted by affine elimination. -/
theorem exists_canonical_segreChartRow_minor_after_common_point_normalization
    [Infinite K] (h2 : (2 : K) ≠ 0)
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (hM : ∀ i, (M i).IsSymm)
    (P : Fin 5 → K) (hP : P ≠ 0)
    (hisotropic : ∀ i, dotProduct P ((M i).mulVec P) = 0)
    (hsmooth : ∀ t : Fin 3 → K, t ≠ 0 → eval t (linearMatrixNet M).det = 0 →
      ∃ i, eval t (pderiv i (linearMatrixNet M).det) ≠ 0) :
    ∃ B : Matrix (Fin 5) (Fin 5) K, B.det ≠ 0 ∧ (∀ j, B j 0 = P j) ∧
      ∃ (k : Fin 3) (p : Fin 4) (x : Fin 3 → K),
        eval x (cross
          (segreChartRow (netLinearRow (matrixNetCongruence M B)) k p)
          (segreChartRow (netQuadraticRow (matrixNetCongruence M B)) k p)).z ≠ 0 := by
  obtain ⟨B, hB, hcol, i, j, p, x, hij, hminor⟩ :=
    exists_netDehomogenizedMinor_after_common_point_normalization
      h2 M hM P hP hisotropic hsmooth
  obtain ⟨k, hk⟩ := exists_canonical_segreChartRow_minor_eval_ne_zero
    (matrixNetCongruence M B) p x i j hij hminor
  exact ⟨B, hB, hcol, k, p, x, hk⟩

end EvenQuinticConic.Incidence
