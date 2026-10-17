import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# A field-theoretic criterion for incidence-chart dominance

The result here does not assume dominance or a transcendence-degree bound.
Instead it uses two explicit generation statements and a nonzero polynomial
relation after eliminating the linear incidence equation.  Applying it to a
concrete conic bundle still requires proving those inputs, in particular the
nonvanishing of the polynomial remaining after linear elimination.
-/

noncomputable section

namespace EvenQuinticConic.Incidence

open Algebra MvPolynomial
open scoped IntermediateField.algebraAdjoinAdjoin

universe u

/-- Two algebra generators subject to a genuine polynomial relation give
transcendence degree at most one. The extension may be algebraic over the
algebra they generate, so this also applies to field generators. -/
theorem trdeg_le_one_of_two_generators_relation
    (F L : Type u) [Field F] [Field L] [Algebra F L]
    (v : Fin 2 → L)
    [Algebra.IsAlgebraic (Algebra.adjoin F (Set.range v)) L]
    (P : MvPolynomial (Fin 2) F) (hP : P ≠ 0) (hrel : aeval v P = 0) :
    Algebra.trdeg F L ≤ 1 := by
  by_contra h
  have htwo : (2 : Cardinal) ≤ Algebra.trdeg F L :=
    Cardinal.two_le_iff_one_lt.mpr (lt_of_not_ge h)
  have hv : AlgebraicIndependent F v :=
    (Algebra.IsAlgebraic.isTranscendenceBasis_of_lift_le_trdeg_of_finite F v
      (by simpa using htwo)).1
  exact hP (hv.eq_zero_of_aeval_eq_zero P hrel)

/-- Field generation implies algebraicity over the corresponding ordinary
subalgebra. This establishes the generation hypothesis needed for the
transcendence-degree argument from equality of actual intermediate fields. -/
theorem isAlgebraic_algebraAdjoin_of_fieldAdjoin_eq_top
    (F L : Type u) [Field F] [Field L] [Algebra F L]
    (s : Set L) (hs : IntermediateField.adjoin F s = ⊤) :
    Algebra.IsAlgebraic (Algebra.adjoin F s) L := by
  refine ⟨fun x ↦ ?_⟩
  let x' : IntermediateField.adjoin F s := ⟨x, by rw [hs]; trivial⟩
  exact (isAlgebraic_algebraMap_iff
    (algebraMap (IntermediateField.adjoin F s) L).injective).mpr
      (Algebra.IsAlgebraic.isAlgebraic x')

/-- If a three-dimensional function field is generated over a two-parameter
field by two elements satisfying a genuine polynomial relation, then the two
parameters must be algebraically independent. All dimension inequalities are
proved internally from the supplied generation and polynomial identities. -/
theorem parameters_algebraicIndependent_of_incidence_relation
    (K F L : Type u) [Field K] [Field F] [Field L]
    [Algebra K F] [Algebra F L] [Algebra K L] [IsScalarTower K F L]
    (x : Fin 3 → L) (hx : AlgebraicIndependent K x)
    (t : Fin 2 → F)
    [Algebra.IsAlgebraic (Algebra.adjoin K (Set.range t)) F]
    (v : Fin 2 → L)
    [Algebra.IsAlgebraic (Algebra.adjoin F (Set.range v)) L]
    (P : MvPolynomial (Fin 2) F) (hP : P ≠ 0) (hrel : aeval v P = 0) :
    AlgebraicIndependent K t := by
  by_contra ht
  obtain ⟨Q, hQ, hQt⟩ : ∃ Q : MvPolynomial (Fin 2) K, Q ≠ 0 ∧ aeval t Q = 0 := by
    by_contra h
    apply ht
    apply algebraicIndependent_iff.mpr
    intro Q hQt
    by_contra hQ
    exact h ⟨Q, hQ, hQt⟩
  have hbase : Algebra.trdeg K F ≤ 1 :=
    trdeg_le_one_of_two_generators_relation K F t Q hQ hQt
  have hfiber : Algebra.trdeg F L ≤ 1 :=
    trdeg_le_one_of_two_generators_relation F L v P hP hrel
  have hthree : (3 : Cardinal) ≤ Algebra.trdeg K L := by
    simpa using hx.lift_cardinalMk_le_trdeg
  have htwo : Algebra.trdeg K L ≤ 2 := by
    rw [← trdeg_add_eq K F (A := L)]
    simpa only [one_add_one_eq_two] using add_le_add hbase hfiber
  exact (by norm_num : ¬ (3 : Cardinal) ≤ 2) (hthree.trans htwo)

/-- A version of the criterion whose generation hypotheses are literal
statements that adjoining the listed elements gives the whole field. -/
theorem parameters_algebraicIndependent_of_field_generators_relation
    (K F L : Type u) [Field K] [Field F] [Field L]
    [Algebra K F] [Algebra F L] [Algebra K L] [IsScalarTower K F L]
    (x : Fin 3 → L) (hx : AlgebraicIndependent K x)
    (t : Fin 2 → F) (ht : IntermediateField.adjoin K (Set.range t) = ⊤)
    (v : Fin 2 → L) (hv : IntermediateField.adjoin F (Set.range v) = ⊤)
    (P : MvPolynomial (Fin 2) F) (hP : P ≠ 0) (hrel : aeval v P = 0) :
    AlgebraicIndependent K t := by
  letI := isAlgebraic_algebraAdjoin_of_fieldAdjoin_eq_top K F (Set.range t) ht
  letI := isAlgebraic_algebraAdjoin_of_fieldAdjoin_eq_top F L (Set.range v) hv
  exact parameters_algebraicIndependent_of_incidence_relation K F L x hx t v P hP hrel

/-- The tautological generators generate their actual intermediate field. -/
theorem fieldAdjoin_canonical_generators_eq_top
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    (t : Fin 2 → L) :
    IntermediateField.adjoin K
      (Set.range (fun i ↦ (⟨t i, IntermediateField.subset_adjoin K
        (Set.range t) ⟨i, rfl⟩⟩ : IntermediateField.adjoin K (Set.range t)))) = ⊤ := by
  apply IntermediateField.lift_injective (IntermediateField.adjoin K (Set.range t))
  rw [IntermediateField.lift_adjoin, IntermediateField.lift_top]
  congr 1
  ext a
  constructor
  · rintro ⟨b, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨_, ⟨i, rfl⟩, rfl⟩

/-- A nonzero linear incidence equation eliminates one of three field
coordinates. The other two then generate the same field over the parameter
field. This statement contains no transcendence-degree assumption. -/
theorem fieldAdjoin_two_coordinates_eq_top_of_linear_relation
    (K F L : Type u) [Field K] [Field F] [Field L]
    [Algebra K F] [Algebra F L] [Algebra K L] [IsScalarTower K F L]
    (x : Fin 3 → L) (hx : IntermediateField.adjoin K (Set.range x) = ⊤)
    (a : Fin 3 → F) (c : F) (k : Fin 3) (ha : a k ≠ 0)
    (hlinear : (∑ i, algebraMap F L (a i) * x i) + algebraMap F L c = 0) :
    IntermediateField.adjoin F (Set.range (fun j : Fin 2 ↦ x (k.succAbove j))) = ⊤ := by
  classical
  let S := IntermediateField.adjoin F (Set.range (fun j : Fin 2 ↦ x (k.succAbove j)))
  have hremaining (j : Fin 2) : x (k.succAbove j) ∈ S :=
    IntermediateField.subset_adjoin F _ ⟨j, rfl⟩
  have hsum : (∑ j : Fin 2, algebraMap F L (a (k.succAbove j)) *
      x (k.succAbove j)) ∈ S :=
    S.sum_mem fun j _ ↦ S.mul_mem (S.algebraMap_mem _) (hremaining j)
  have hdenom : algebraMap F L (a k) ≠ 0 := (map_ne_zero (algebraMap F L)).mpr ha
  have hsolve : x k =
      -((∑ j : Fin 2, algebraMap F L (a (k.succAbove j)) * x (k.succAbove j)) +
        algebraMap F L c) / algebraMap F L (a k) := by
    apply (eq_div_iff hdenom).mpr
    rw [Fin.sum_univ_succAbove _ k] at hlinear
    linear_combination hlinear
  have hpivot : x k ∈ S := by
    rw [hsolve]
    exact S.div_mem (S.neg_mem (S.add_mem hsum (S.algebraMap_mem c))) (S.algebraMap_mem _)
  apply IntermediateField.restrictScalars_injective K
  rw [IntermediateField.restrictScalars_top, ← top_le_iff, ← hx,
    IntermediateField.adjoin_le_iff]
  rintro y ⟨i, rfl⟩
  rcases Fin.eq_self_or_eq_succAbove k i with rfl | ⟨j, rfl⟩
  · exact hpivot
  · exact hremaining j

/-- The complete elimination criterion: a nonzero linear coefficient and a
nonzero residual polynomial suffice to certify independence of two field
generators. Neither dominance nor any transcendence-degree bound is an input. -/
theorem parameters_algebraicIndependent_of_linear_elimination
    (K F L : Type u) [Field K] [Field F] [Field L]
    [Algebra K F] [Algebra F L] [Algebra K L] [IsScalarTower K F L]
    (x : Fin 3 → L) (hx : AlgebraicIndependent K x)
    (hxgen : IntermediateField.adjoin K (Set.range x) = ⊤)
    (t : Fin 2 → F) (htgen : IntermediateField.adjoin K (Set.range t) = ⊤)
    (a : Fin 3 → F) (c : F) (k : Fin 3) (ha : a k ≠ 0)
    (hlinear : (∑ i, algebraMap F L (a i) * x i) + algebraMap F L c = 0)
    (P : MvPolynomial (Fin 2) F) (hP : P ≠ 0)
    (hrel : aeval (fun j : Fin 2 ↦ x (k.succAbove j)) P = 0) :
    AlgebraicIndependent K t := by
  have hvgen := fieldAdjoin_two_coordinates_eq_top_of_linear_relation
    K F L x hxgen a c k ha hlinear
  exact parameters_algebraicIndependent_of_field_generators_relation
    K F L x hx t htgen _ hvgen P hP hrel

/-- The three actual affine coordinates remain algebraically independent in
 the ordinary fraction field of the polynomial ring. -/
theorem rationalThreeCoordinates_algebraicIndependent
    (K : Type u) [Field K] :
    AlgebraicIndependent K (fun i : Fin 3 ↦
      algebraMap (MvPolynomial (Fin 3) K) (FractionRing (MvPolynomial (Fin 3) K)) (X i)) := by
  exact (MvPolynomial.algebraicIndependent_X (Fin 3) K).map
    (f := IsScalarTower.toAlgHom K (MvPolynomial (Fin 3) K)
      (FractionRing (MvPolynomial (Fin 3) K)))
    (IsFractionRing.injective (MvPolynomial (Fin 3) K)
      (FractionRing (MvPolynomial (Fin 3) K))).injOn

/-- These same coordinates field-generate the actual rational function field;
this is proved from polynomial induction and fractions, without a supplied
transcendence-basis or dimension certificate. -/
theorem rationalThreeCoordinates_fieldAdjoin_eq_top
    (K : Type u) [Field K] :
    IntermediateField.adjoin K (Set.range (fun i : Fin 3 ↦
      algebraMap (MvPolynomial (Fin 3) K) (FractionRing (MvPolynomial (Fin 3) K)) (X i))) = ⊤ := by
  let R := MvPolynomial (Fin 3) K
  let L := FractionRing R
  let S := IntermediateField.adjoin K
    (Set.range (fun i : Fin 3 ↦ algebraMap R L (X i)))
  have hpoly (p : R) : algebraMap R L p ∈ S := by
    induction p using MvPolynomial.induction_on with
    | C a =>
      change algebraMap R L (algebraMap K R a) ∈ S
      rw [← IsScalarTower.algebraMap_apply]
      exact S.algebraMap_mem a
    | add p q hp hq =>
      rw [map_add]
      exact S.add_mem hp hq
    | mul_X p i hp =>
      rw [map_mul]
      exact S.mul_mem hp (IntermediateField.subset_adjoin K _ ⟨i, rfl⟩)
  apply top_le_iff.mp
  intro z _
  obtain ⟨p, q, _, rfl⟩ := IsFractionRing.div_surjective (A := R) z
  exact S.div_mem (hpoly p) (hpoly q)

/-- Independence of the canonical generators inside their generated field
is exactly independence of their images in the ambient field. Keeping this
comparison generic avoids unfolding a concrete rational-map definition. -/
theorem canonicalParameters_algebraicIndependent_iff
    (K L : Type u) [Field K] [Field L] [Algebra K L] (s : Fin 2 → L) :
    AlgebraicIndependent K (fun i ↦ (⟨s i,
      IntermediateField.subset_adjoin K (Set.range s) ⟨i, rfl⟩⟩ :
      IntermediateField.adjoin K (Set.range s))) ↔ AlgebraicIndependent K s := by
  let u : Fin 2 → IntermediateField.adjoin K (Set.range s) := fun i ↦
    ⟨s i, IntermediateField.subset_adjoin K (Set.range s) ⟨i, rfl⟩⟩
  exact ((IntermediateField.adjoin K (Set.range s)).val.algebraicIndependent_iff
    (x := u) (IntermediateField.adjoin K (Set.range s)).val.injective).symm

end EvenQuinticConic.Incidence
