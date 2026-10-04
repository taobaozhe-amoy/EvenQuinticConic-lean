import EvenQuinticConic.SchemeScalarAction
import EvenQuinticConic.ModulePairing
import EvenQuinticConic.ThetaSectionBridge

/-!
# Actual quadratic sections from three global sections

The six quadratic monomials are evaluated by the actual natural pairing.
Their generic coefficient is computed from the actual scheme scalar action
and restriction maps, rather than supplied as a lifting hypothesis.
-/

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open MvPolynomial

universe u

namespace EvenQuinticConic

private theorem fin3_degree_two_cases (d : Fin 3 →₀ ℕ) (hd : d.degree = 2) :
    d = Finsupp.single 0 2 ∨ d = Finsupp.single 1 2 ∨ d = Finsupp.single 2 2 ∨
      d = Finsupp.single 0 1 + Finsupp.single 1 1 ∨
      d = Finsupp.single 0 1 + Finsupp.single 2 1 ∨
      d = Finsupp.single 1 1 + Finsupp.single 2 1 := by
  have hsum : d 0 + d 1 + d 2 = 2 := by
    simpa [Finsupp.degree_eq_sum, Fin.sum_univ_three, add_assoc] using hd
  have hcases : (d 0 = 2 ∧ d 1 = 0 ∧ d 2 = 0) ∨
      (d 0 = 0 ∧ d 1 = 2 ∧ d 2 = 0) ∨
      (d 0 = 0 ∧ d 1 = 0 ∧ d 2 = 2) ∨
      (d 0 = 1 ∧ d 1 = 1 ∧ d 2 = 0) ∨
      (d 0 = 1 ∧ d 1 = 0 ∧ d 2 = 1) ∨
      (d 0 = 0 ∧ d 1 = 1 ∧ d 2 = 1) := by omega
  rcases hcases with h | h | h | h | h | h
  · left; ext i; fin_cases i <;> simp [h.1, h.2.1, h.2.2]
  · right; left; ext i; fin_cases i <;> simp [h.1, h.2.1, h.2.2]
  · right; right; left; ext i; fin_cases i <;> simp [h.1, h.2.1, h.2.2]
  · right; right; right; left; ext i; fin_cases i <;> simp [h.1, h.2.1, h.2.2]
  · right; right; right; right; left; ext i; fin_cases i <;> simp [h.1, h.2.1, h.2.2]
  · right; right; right; right; right; ext i; fin_cases i <;> simp [h.1, h.2.1, h.2.2]

/-- Every homogeneous quadratic in three coordinates is the sum of its six
quadratic monomials. This includes characteristic two without division by two. -/
theorem homogeneous_quadratic_fin3_eq {K : Type*} [CommSemiring K]
    (A : MvPolynomial (Fin 3) K) (hA : A.IsHomogeneous 2) :
    A = monomial (Finsupp.single 0 2) (A.coeff (Finsupp.single 0 2)) +
      monomial (Finsupp.single 1 2) (A.coeff (Finsupp.single 1 2)) +
      monomial (Finsupp.single 2 2) (A.coeff (Finsupp.single 2 2)) +
      monomial (Finsupp.single 0 1 + Finsupp.single 1 1)
        (A.coeff (Finsupp.single 0 1 + Finsupp.single 1 1)) +
      monomial (Finsupp.single 0 1 + Finsupp.single 2 1)
        (A.coeff (Finsupp.single 0 1 + Finsupp.single 2 1)) +
      monomial (Finsupp.single 1 1 + Finsupp.single 2 1)
        (A.coeff (Finsupp.single 1 1 + Finsupp.single 2 1)) := by
  classical
  ext d
  by_cases hd : d.degree = 2
  · rcases fin3_degree_two_cases d hd with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [coeff_monomial, Finsupp.ext_iff, Fin.forall_fin_succ]
  · have hne (e : Fin 3 →₀ ℕ) (he : e.degree = 2) : e ≠ d := by
      intro h; exact hd (h ▸ he)
    have he01 : (Finsupp.single (0 : Fin 3) 1 + Finsupp.single 1 1).degree = 2 := by
      simp
    have he02 : (Finsupp.single (0 : Fin 3) 1 + Finsupp.single 2 1).degree = 2 := by
      simp
    have he12 : (Finsupp.single (1 : Fin 3) 1 + Finsupp.single 2 1).degree = 2 := by
      simp
    have he0 := hne (Finsupp.single 0 2) (by simp)
    have he1 := hne (Finsupp.single 1 2) (by simp)
    have he2 := hne (Finsupp.single 2 2) (by simp)
    simp [hA.coeff_eq_zero hd, coeff_monomial, he0, he1, he2,
      hne _ he01, hne _ he02, hne _ he12]

/-- Evaluation of a homogeneous quadratic is the six-term quadratic form. -/
theorem homogeneous_quadratic_fin3_aeval {K L : Type*} [CommSemiring K]
    [CommSemiring L] [Algebra K L] (f : Fin 3 → L)
    (A : MvPolynomial (Fin 3) K) (hA : A.IsHomogeneous 2) :
    aeval f A = algebraMap K L (A.coeff (Finsupp.single 0 2)) * f 0 ^ 2 +
      algebraMap K L (A.coeff (Finsupp.single 1 2)) * f 1 ^ 2 +
      algebraMap K L (A.coeff (Finsupp.single 2 2)) * f 2 ^ 2 +
      algebraMap K L (A.coeff (Finsupp.single 0 1 + Finsupp.single 1 1)) * f 0 * f 1 +
      algebraMap K L (A.coeff (Finsupp.single 0 1 + Finsupp.single 2 1)) * f 0 * f 2 +
      algebraMap K L (A.coeff (Finsupp.single 1 1 + Finsupp.single 2 1)) * f 1 * f 2 := by
  nth_rw 1 [homogeneous_quadratic_fin3_eq A hA]
  simp [aeval_monomial, Finsupp.prod_add_index, pow_add, mul_assoc]

open scoped SchemeScalars

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (CommRingCat.of K))]

/-- Evaluate a quadratic polynomial by the actual pairing of three genuine
sections. No square root and no choice of local frame enters the construction. -/
noncomputable def quadraticPolynomialSection
    {H T : X.Modules} (ν : ModuleSheafPairing H H T)
    (e : Fin 3 → H.val.obj (op ⊤)) (A : MvPolynomial (Fin 3) K) :
    T.val.obj (op ⊤) :=
  A.coeff (Finsupp.single 0 2) • ν.app ⊤ (e 0) (e 0) +
    A.coeff (Finsupp.single 1 2) • ν.app ⊤ (e 1) (e 1) +
    A.coeff (Finsupp.single 2 2) • ν.app ⊤ (e 2) (e 2) +
    A.coeff (Finsupp.single 0 1 + Finsupp.single 1 1) • ν.app ⊤ (e 0) (e 1) +
    A.coeff (Finsupp.single 0 1 + Finsupp.single 2 1) • ν.app ⊤ (e 0) (e 2) +
    A.coeff (Finsupp.single 1 1 + Finsupp.single 2 1) • ν.app ⊤ (e 1) (e 2)

/-- The six-term construction is genuinely linear over the base field. -/
noncomputable def quadraticPolynomialSectionMap
    {H T : X.Modules} (ν : ModuleSheafPairing H H T)
    (e : Fin 3 → H.val.obj (op ⊤)) :
    MvPolynomial (Fin 3) K →ₗ[K] T.val.obj (op ⊤) where
  toFun := quadraticPolynomialSection ν e
  map_add' A B := by
    simp only [quadraticPolynomialSection, coeff_add, add_smul]
    abel
  map_smul' c A := by
    simp [quadraticPolynomialSection, coeff_smul, mul_smul, smul_add]

/-- The actual restriction map from degree-two homogeneous polynomials to
actual global sections of the square of the hyperplane sheaf. -/
noncomputable def quadraticSectionMap
    {H T : X.Modules} (ν : ModuleSheafPairing H H T)
    (e : Fin 3 → H.val.obj (op ⊤)) :
    homogeneousSubmodule (Fin 3) K 2 →ₗ[K] T.val.obj (op ⊤) :=
  (quadraticPolynomialSectionMap ν e).comp
    (homogeneousSubmodule (Fin 3) K 2).subtype

omit [IsIntegral X] in
/-- Surjectivity of the actual degree-two restriction map supplies genuine
homogeneous polynomial lifts, with an equality in global sections. -/
theorem exists_quadratic_lift_of_surjective
    {H T : X.Modules} (ν : ModuleSheafPairing H H T)
    (e : Fin 3 → H.val.obj (op ⊤))
    (h2 : Function.Surjective (quadraticSectionMap (K := K) ν e))
    (s : T.val.obj (op ⊤)) :
    ∃ A : MvPolynomial (Fin 3) K, A.IsHomogeneous 2 ∧
      quadraticPolynomialSection ν e A = s := by
  obtain ⟨A, hA⟩ := h2 s
  exact ⟨A.val, A.property, hA⟩

/-- The generic coefficient of the constructed global section is precisely
the polynomial restriction computed from the actual pairing and frames. -/
theorem genericCoefficient_quadraticPolynomialSection
    {H T : X.Modules} (ν : ModuleSheafPairing H H T)
    (V : X.Opens) [Nonempty V] (h : ModuleSheafFrame H V)
    (p : ModuleSheafFrame T V) (e : Fin 3 → H.val.obj (op ⊤))
    (A : MvPolynomial (Fin 3) K) (hA : A.IsHomogeneous 2) :
    schemeGenericLinearMap (K := K) T V p (quadraticPolynomialSection ν e A) =
      quadraticGenericRestriction ν V h p e A := by
  simp only [quadraticPolynomialSection, map_add, map_smul]
  simp only [quadraticGenericRestriction, homogeneous_quadratic_fin3_aeval _ A hA]
  have hpair (i j : Fin 3) := moduleGlobalGenericLinearMap_pairing ν V h p (e i) (e j)
  change ∀ i j : Fin 3,
    schemeGenericLinearMap (K := K) T V p (ν.app ⊤ (e i) (e j)) =
      X.germToFunctionField V (modulePairingCoefficient ν V h p) *
        schemeGenericLinearMap (K := K) H V h (e i) *
        schemeGenericLinearMap (K := K) H V h (e j) at hpair
  simp only [hpair, Algebra.smul_def]
  ring

end EvenQuinticConic
