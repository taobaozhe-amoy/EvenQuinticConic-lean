import EvenQuinticConic.PlaneCurveSheafResidueIdentities

/-!
# Signed residue transitions on actual curve overlaps

Permutation signs normalize the actual residue sections. The resulting
sections have the degree-two hyperplane transition on all pairs of
Jacobian charts. Additional derivative-open inclusions are derived from
actual coordinate scaling and genuine derivative units.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace MvPolynomial

namespace EvenQuinticConic

variable {K : Type} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra planeCurveResidueSectionAlgebra

/-- Invertibility of a homogeneous derivative transfers between actual
coordinate charts on their overlap. No extra derivative-open membership
is assumed on the first chart. -/
theorem planeCurveGradientBasicOpen_changeChart
    (F : PlanePolynomial K) (hF : F.IsHomogeneous 5)
    (hFdeg : 1 < F.totalDegree) (hprime : (Ideal.span {F}).IsPrime)
    (i l j : Fin 3) (W : (PlaneCurveScheme F).Opens)
    (hi : W ≤ planeCurveCoordinateOpen F i)
    (hlj : W ≤ (PlaneCurveScheme F).basicOpen (planeCurveGradientSection F hF l j)) :
    W ≤ (PlaneCurveScheme F).basicOpen (planeCurveGradientSection F hF i j) := by
  letI := planeCurveScheme_isIntegral F 5 hF hFdeg hprime
  letI := planeCurveCoordinateOpen_nonempty F 5 hF hFdeg hprime i
  letI := planeCurveCoordinateOpen_nonempty F 5 hF hFdeg hprime l
  let hl := hlj.trans ((PlaneCurveScheme F).basicOpen_le (planeCurveGradientSection F hF l j))
  have hu := (planeCurveGradientUnitOn F hF l j W hlj *
    planeCurveResidueCoordinateUnit F i l W hi hl ^ 4).isUnit
  rw [planeCurveGradientUnitOn_scaleBack F hF i l j W hlj hi hl,
    planeCurveResidueCoordinates_aeval, planeCurveChartPolynomialMap_pderiv] at hu
  have hb := (PlaneCurveScheme F).basicOpen_of_isUnit hu
  change (PlaneCurveScheme F).basicOpen
    ((PlaneCurveScheme F).presheaf.map (homOfLE hi).op
      (planeCurveGradientSection F hF i j)) = W at hb
  rw [Scheme.basicOpen_res] at hb
  exact inf_eq_left.mp hb

/-- The orientation sign of an ordered triple of distinct plane coordinates. -/
def planeResidueSign (i j k : Fin 3) : ℤ :=
  if (i < j ∧ j < k) ∨ (j < k ∧ k < i) ∨ (k < i ∧ i < j) then 1 else -1

/-- Swapping the two nonradial coordinates reverses the residue sign. -/
theorem planeResidueSign_swap_last (i j k : Fin 3)
    (hji : j ≠ i) (hki : k ≠ i) (hkj : k ≠ j) :
    planeResidueSign i k j = -planeResidueSign i j k := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all [planeResidueSign]

/-- Swapping the chart coordinate and the last coordinate reverses the sign. -/
theorem planeResidueSign_swap_outer (i j k : Fin 3)
    (hji : j ≠ i) (hki : k ≠ i) (hkj : k ≠ j) :
    planeResidueSign k j i = -planeResidueSign i j k := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all [planeResidueSign]

/-- Swapping the chart coordinate and the derivative coordinate reverses the sign. -/
theorem planeResidueSign_swap_first (i j k : Fin 3)
    (hji : j ≠ i) (hki : k ≠ i) (hkj : k ≠ j) :
    planeResidueSign j i k = -planeResidueSign i j k := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all [planeResidueSign]

/-- The actual differential-sheaf residue with its permutation orientation. -/
def planeCurveSignedResidue
    (F : PlanePolynomial K) (hF : F.IsHomogeneous 5) (i j k : Fin 3)
    (W : (PlaneCurveScheme F).Opens)
    (hj : W ≤ (PlaneCurveScheme F).basicOpen (planeCurveGradientSection F hF i j)) :
    (schemeKaehlerSheaf (planeCurveStructure F)).val.obj (op W) :=
  planeResidueSign i j k • planeCurveSheafResidue F hF i j k W hj

/-- The two signed residues on one actual coordinate chart agree. -/
theorem planeCurveSignedResidue_swap
    (F : PlanePolynomial K) (hF : F.IsHomogeneous 5)
    (hFdeg : 1 < F.totalDegree) (hprime : (Ideal.span {F}).IsPrime)
    (i j k : Fin 3) (hji : j ≠ i) (hki : k ≠ i) (hkj : k ≠ j)
    (W : (PlaneCurveScheme F).Opens)
    (hj : W ≤ (PlaneCurveScheme F).basicOpen (planeCurveGradientSection F hF i j))
    (hk : W ≤ (PlaneCurveScheme F).basicOpen (planeCurveGradientSection F hF i k)) :
    planeCurveSignedResidue F hF i k j W hk = planeCurveSignedResidue F hF i j k W hj := by
  unfold planeCurveSignedResidue
  rw [planeResidueSign_swap_last i j k hji hki hkj,
    planeCurveSheafResidue_sameChart F hF hFdeg hprime i j k hji hki hkj W hj hk]
  simp only [neg_smul, smul_neg]

/-- Signed residues with the same derivative on different actual charts
have the actual squared coordinate transition. -/
theorem planeCurveSignedResidue_commonDerivative
    (F : PlanePolynomial K) (hF : F.IsHomogeneous 5)
    (hFdeg : 1 < F.totalDegree) (hprime : (Ideal.span {F}).IsPrime)
    (i l j : Fin 3) (hji : j ≠ i) (hli : l ≠ i) (hlj : l ≠ j)
    (W : (PlaneCurveScheme F).Opens)
    (hij : W ≤ (PlaneCurveScheme F).basicOpen (planeCurveGradientSection F hF i j))
    (hlj' : W ≤ (PlaneCurveScheme F).basicOpen (planeCurveGradientSection F hF l j)) :
    let hi := hij.trans ((PlaneCurveScheme F).basicOpen_le (planeCurveGradientSection F hF i j))
    planeCurveSignedResidue F hF l j i W hlj' =
      (planeCurveResidueCoordinates F i W hi l) ^ 2 •
        planeCurveSignedResidue F hF i j l W hij := by
  unfold planeCurveSignedResidue
  rw [planeResidueSign_swap_outer i j l hji hli hlj, neg_smul, ← smul_neg,
    planeCurveSheafResidue_commonDerivative F hF hFdeg hprime i l j W hij hlj']
  exact smul_comm _ _ _

/-- Signed residues whose derivative and chart coordinates interchange
have the same actual squared coordinate transition. -/
theorem planeCurveSignedResidue_radialDerivatives
    (F : PlanePolynomial K) (hF : F.IsHomogeneous 5)
    (hFdeg : 1 < F.totalDegree) (hprime : (Ideal.span {F}).IsPrime)
    (i l k : Fin 3) (hli : l ≠ i) (hki : k ≠ i) (hkl : k ≠ l)
    (W : (PlaneCurveScheme F).Opens)
    (hil : W ≤ (PlaneCurveScheme F).basicOpen (planeCurveGradientSection F hF i l))
    (hli' : W ≤ (PlaneCurveScheme F).basicOpen (planeCurveGradientSection F hF l i)) :
    let hi := hil.trans ((PlaneCurveScheme F).basicOpen_le (planeCurveGradientSection F hF i l))
    planeCurveSignedResidue F hF l i k W hli' =
      (planeCurveResidueCoordinates F i W hi l) ^ 2 •
        planeCurveSignedResidue F hF i l k W hil := by
  unfold planeCurveSignedResidue
  rw [planeResidueSign_swap_first i l k hli hki hkl, neg_smul, ← smul_neg,
    planeCurveSheafResidue_radialDerivatives F hF hFdeg hprime i l k hli hki hkl W hil hli']
  exact smul_comm _ _ _

/-- Any two admissible derivative choices on one actual coordinate chart
give the same signed residue. -/
theorem planeCurveSignedResidue_sameChart
    (F : PlanePolynomial K) (hF : F.IsHomogeneous 5)
    (hFdeg : 1 < F.totalDegree) (hprime : (Ideal.span {F}).IsPrime)
    (i j k m n : Fin 3)
    (hji : j ≠ i) (hki : k ≠ i) (hkj : k ≠ j)
    (hmi : m ≠ i) (hni : n ≠ i) (hnm : n ≠ m)
    (W : (PlaneCurveScheme F).Opens)
    (hj : W ≤ (PlaneCurveScheme F).basicOpen (planeCurveGradientSection F hF i j))
    (hm : W ≤ (PlaneCurveScheme F).basicOpen (planeCurveGradientSection F hF i m)) :
    planeCurveSignedResidue F hF i m n W hm = planeCurveSignedResidue F hF i j k W hj := by
  by_cases hmj : m = j
  · subst m
    have hnk : n = k := by omega
    subst n
    rfl
  · have hmk : m = k := by omega
    have hnj : n = j := by omega
    subst m
    subst n
    exact planeCurveSignedResidue_swap F hF hFdeg hprime i j k hji hki hkj W hj hm

/-- All pairs of actual Jacobian-chart residues have the degree-two
coordinate transition. The mixed derivative cases are reduced using
proved actual derivative-open inclusions, not extra overlap assumptions. -/
theorem planeCurveSignedResidue_transition
    (F : PlanePolynomial K) (hF : F.IsHomogeneous 5)
    (hFdeg : 1 < F.totalDegree) (hprime : (Ideal.span {F}).IsPrime)
    (i j k l m n : Fin 3)
    (hji : j ≠ i) (hki : k ≠ i) (hkj : k ≠ j)
    (hml : m ≠ l) (hnl : n ≠ l) (hnm : n ≠ m)
    (W : (PlaneCurveScheme F).Opens)
    (hij : W ≤ (PlaneCurveScheme F).basicOpen (planeCurveGradientSection F hF i j))
    (hlm : W ≤ (PlaneCurveScheme F).basicOpen (planeCurveGradientSection F hF l m)) :
    let hi := hij.trans ((PlaneCurveScheme F).basicOpen_le (planeCurveGradientSection F hF i j))
    planeCurveSignedResidue F hF l m n W hlm =
      (planeCurveResidueCoordinates F i W hi l) ^ 2 •
        planeCurveSignedResidue F hF i j k W hij := by
  let hi := hij.trans ((PlaneCurveScheme F).basicOpen_le (planeCurveGradientSection F hF i j))
  let hl := hlm.trans ((PlaneCurveScheme F).basicOpen_le (planeCurveGradientSection F hF l m))
  dsimp only
  by_cases hil : i = l
  · subst l
    rw [planeCurveResidueCoordinates_self, one_pow, one_smul]
    exact planeCurveSignedResidue_sameChart F hF hFdeg hprime i j k m n
      hji hki hkj hml hnl hnm W hij hlm
  · by_cases hmi : m = i
    · subst m
      by_cases hjl : j = l
      · subst j
        have hnk : n = k := by omega
        subst n
        exact planeCurveSignedResidue_radialDerivatives F hF hFdeg hprime
          i l k hji hki hkj W hij hlm
      · have hkl : k = l := by omega
        have hnj : n = j := by omega
        subst k
        subst n
        have hlj := planeCurveGradientBasicOpen_changeChart F hF hFdeg hprime
          l i j W hl hij
        rw [planeCurveSignedResidue_swap F hF hFdeg hprime
          l j i hjl hil hji.symm W hlj hlm]
        exact planeCurveSignedResidue_commonDerivative F hF hFdeg hprime
          i l j hji (Ne.symm hil) (Ne.symm hjl) W hij hlj
    · have hni : n = i := by omega
      subst n
      have him := planeCurveGradientBasicOpen_changeChart F hF hFdeg hprime
        i l m W hi hlm
      have h := planeCurveSignedResidue_commonDerivative F hF hFdeg hprime
        i l m hmi (Ne.symm hil) hml.symm W him hlm
      rw [planeCurveSignedResidue_sameChart F hF hFdeg hprime
        i j k m l hji hki hkj hmi (Ne.symm hil) hml.symm W hij him] at h
      exact h

/-- The transition factor is precisely the square of the already constructed
actual hyperplane cocycle unit, with the same direction of coordinates. -/
theorem planeCurveSignedResidue_transition_unit
    (F : PlanePolynomial K) (hF : F.IsHomogeneous 5)
    (hFdeg : 1 < F.totalDegree) (hprime : (Ideal.span {F}).IsPrime)
    (i j k l m n : Fin 3)
    (hji : j ≠ i) (hki : k ≠ i) (hkj : k ≠ j)
    (hml : m ≠ l) (hnl : n ≠ l) (hnm : n ≠ m)
    (W : (PlaneCurveScheme F).Opens)
    (hij : W ≤ (PlaneCurveScheme F).basicOpen (planeCurveGradientSection F hF i j))
    (hlm : W ≤ (PlaneCurveScheme F).basicOpen (planeCurveGradientSection F hF l m)) :
    let hi := hij.trans ((PlaneCurveScheme F).basicOpen_le (planeCurveGradientSection F hF i j))
    let hl := hlm.trans ((PlaneCurveScheme F).basicOpen_le (planeCurveGradientSection F hF l m))
    planeCurveSignedResidue F hF l m n W hlm =
      ((planeCurveResidueCoordinateUnit F i l W hi hl : Γ(PlaneCurveScheme F, W)) ^ 2) •
        planeCurveSignedResidue F hF i j k W hij := by
  dsimp only
  rw [planeCurveResidueCoordinateUnit_val]
  exact planeCurveSignedResidue_transition F hF hFdeg hprime i j k l m n
    hji hki hkj hml hnl hnm W hij hlm

/-- Signed residues are natural under every actual restriction of opens. -/
theorem planeCurveSignedResidue_restrict
    (F : PlanePolynomial K) (hF : F.IsHomogeneous 5) (i j k : Fin 3)
    (W V : (PlaneCurveScheme F).Opens)
    (hj : W ≤ (PlaneCurveScheme F).basicOpen (planeCurveGradientSection F hF i j))
    (hVW : V ≤ W) :
    (schemeKaehlerSheaf (planeCurveStructure F)).val.map (homOfLE hVW).op
        (planeCurveSignedResidue F hF i j k W hj) =
      planeCurveSignedResidue F hF i j k V (hVW.trans hj) := by
  simp only [planeCurveSignedResidue, map_zsmul, planeCurveSheafResidue_restrict]

/-- The orientation sign as a genuine unit in any coefficient ring, for
rescaling actual local frames. -/
def planeResidueSignUnit {S : Type*} [CommRing S] (i j k : Fin 3) : Sˣ :=
  if (i < j ∧ j < k) ∨ (j < k ∧ k < i) ∨ (k < i ∧ i < j) then 1 else -1

/-- The orientation unit is precisely the integer orientation sign in the ring. -/
theorem planeResidueSignUnit_val {S : Type*} [CommRing S] (i j k : Fin 3) :
    (planeResidueSignUnit (S := S) i j k : S) = (planeResidueSign i j k : S) := by
  unfold planeResidueSignUnit planeResidueSign
  split_ifs <;> simp

/-- Rescaling by the orientation unit agrees with the sign used in the
actual signed residue sections. -/
theorem planeResidueSignUnit_smul {S M : Type*} [CommRing S]
    [AddCommGroup M] [Module S M] (i j k : Fin 3) (m : M) :
    (planeResidueSignUnit (S := S) i j k : S) • m = planeResidueSign i j k • m := by
  unfold planeResidueSignUnit planeResidueSign
  split_ifs <;> simp

end EvenQuinticConic
