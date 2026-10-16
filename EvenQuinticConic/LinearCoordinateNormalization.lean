import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.MvPolynomial.Equiv
import EvenQuinticConic.NetBasePoint

/-!
# Normalizing independent linear forms by an actual coordinate equivalence

Three independent coefficient vectors in four variables extend to a basis.
The basis and its inverse give inverse polynomial substitutions.  Thus the
normalization used in the incidence argument is constructed, not supplied as
an extra hypothesis.  Both substitutions preserve every homogeneous degree.
-/

noncomputable section
namespace EvenQuinticConic
open MvPolynomial Module

variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

/-- The homogeneous linear polynomial with the specified coefficient vector. -/
def coefficientLinearPolynomial (v : ι → K) : MvPolynomial ι K :=
  ∑ j, C (v j) * X j

omit [DecidableEq ι] in
theorem coefficientLinearPolynomial_homogeneous (v : ι → K) :
    (coefficientLinearPolynomial v).IsHomogeneous 1 := by
  exact IsHomogeneous.sum _ _ _ (fun j _ => isHomogeneous_C_mul_X _ _)

@[simp] theorem coefficientLinearPolynomial_single (i : ι) :
    coefficientLinearPolynomial (Pi.single i (1 : K)) = X i := by
  classical
  simp [coefficientLinearPolynomial, Pi.single_apply]

/-- The polynomial substitution associated to a basis of coefficient vectors. -/
def basisLinearSubstitution (b : Basis ι K (ι → K)) :
    MvPolynomial ι K →ₐ[K] MvPolynomial ι K :=
  aeval (fun i => coefficientLinearPolynomial (b i))

/-- The inverse substitution uses the coordinates of the original standard basis. -/
def basisLinearSubstitutionInverse (b : Basis ι K (ι → K)) :
    MvPolynomial ι K →ₐ[K] MvPolynomial ι K :=
  aeval (fun i => coefficientLinearPolynomial (fun j => b.repr (Pi.single i 1) j))

omit [DecidableEq ι] in
theorem basisLinearSubstitution_apply_linear (b : Basis ι K (ι → K)) (v : ι → K) :
    basisLinearSubstitution b (coefficientLinearPolynomial v) =
      coefficientLinearPolynomial (∑ i, v i • b i) := by
  simp only [basisLinearSubstitution, coefficientLinearPolynomial, map_sum, map_mul,
    aeval_C, algebraMap_eq, aeval_X, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    map_sum, map_mul, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem basisLinearSubstitutionInverse_apply_linear
    (b : Basis ι K (ι → K)) (v : ι → K) :
    basisLinearSubstitutionInverse b (coefficientLinearPolynomial v) =
      coefficientLinearPolynomial (fun j => b.repr v j) := by
  have hv : ∑ i, v i • (Pi.single i (1 : K) : ι → K) = v := by
    ext j
    simp [Pi.single_apply]
  have hrepr (j : ι) : ∑ i, v i * b.repr (Pi.single i 1) j = b.repr v j := by
    have h := congrArg (fun w => b.repr w j) hv
    simpa using h
  simp only [basisLinearSubstitutionInverse, coefficientLinearPolynomial, map_sum,
    map_mul, aeval_C, algebraMap_eq, aeval_X]
  simp_rw [Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Finset.sum_mul]
  simp_rw [← map_mul]
  rw [← map_sum, hrepr]

/-- An actual polynomial algebra equivalence, with both inverse laws proved. -/
def basisLinearPolynomialEquiv (b : Basis ι K (ι → K)) :
    MvPolynomial ι K ≃ₐ[K] MvPolynomial ι K :=
  AlgEquiv.ofAlgHom (basisLinearSubstitution b) (basisLinearSubstitutionInverse b)
    (by
      ext i : 1
      simp only [AlgHom.comp_apply, basisLinearSubstitutionInverse, aeval_X, AlgHom.id_apply]
      change basisLinearSubstitution b
        (coefficientLinearPolynomial (fun j => b.repr (Pi.single i 1) j)) = X i
      rw [basisLinearSubstitution_apply_linear, b.sum_repr,
        coefficientLinearPolynomial_single])
    (by
      ext i : 1
      simp only [AlgHom.comp_apply, basisLinearSubstitution, aeval_X, AlgHom.id_apply]
      change basisLinearSubstitutionInverse b (coefficientLinearPolynomial (b i)) = X i
      rw [basisLinearSubstitutionInverse_apply_linear]
      simp [b.repr_self, coefficientLinearPolynomial, Finsupp.single_apply])

theorem basisLinearPolynomialEquiv_homogeneous
    (b : Basis ι K (ι → K)) {p : MvPolynomial ι K} {d : ℕ}
    (hp : p.IsHomogeneous d) : (basisLinearPolynomialEquiv b p).IsHomogeneous d := by
  simpa [basisLinearPolynomialEquiv, basisLinearSubstitution] using
    hp.aeval (fun i => coefficientLinearPolynomial (b i))
      (fun i => coefficientLinearPolynomial_homogeneous (b i))

theorem basisLinearPolynomialEquiv_symm_homogeneous
    (b : Basis ι K (ι → K)) {p : MvPolynomial ι K} {d : ℕ}
    (hp : p.IsHomogeneous d) : ((basisLinearPolynomialEquiv b).symm p).IsHomogeneous d := by
  simpa [basisLinearPolynomialEquiv, basisLinearSubstitutionInverse] using
    hp.aeval (fun i => coefficientLinearPolynomial (fun j => b.repr (Pi.single i 1) j))
      (fun i => coefficientLinearPolynomial_homogeneous _)

/-- Independent linear forms in four variables can be made the first three
coordinates by a genuine invertible homogeneous polynomial substitution. -/
theorem exists_normalizing_linear_coordinate_equiv
    (l : Fin 3 → Fin 4 → K) (hl : LinearIndependent K l) :
    ∃ e : MvPolynomial (Fin 4) K ≃ₐ[K] MvPolynomial (Fin 4) K,
      (∀ i, e (coefficientLinearPolynomial (l i)) = X i.castSucc) ∧
      (∀ {p : MvPolynomial (Fin 4) K} {d : ℕ}, p.IsHomogeneous d →
        (e p).IsHomogeneous d) ∧
      (∀ {p : MvPolynomial (Fin 4) K} {d : ℕ}, p.IsHomogeneous d →
        (e.symm p).IsHomogeneous d) := by
  classical
  obtain ⟨v, hv⟩ := exists_linearIndependent_snoc_of_lt_finrank hl
    (by simp : 3 < Module.finrank K (Fin 4 → K))
  let b : Basis (Fin 4) K (Fin 4 → K) :=
    basisOfPiSpaceOfLinearIndependent hv
  have hb (i : Fin 4) : b i = (Fin.snoc l v : Fin 4 → (Fin 4 → K)) i := by
    exact congrFun (coe_basisOfPiSpaceOfLinearIndependent hv) i
  refine ⟨(basisLinearPolynomialEquiv b).symm, ?_,
    fun hp => basisLinearPolynomialEquiv_symm_homogeneous b hp,
    fun hp => basisLinearPolynomialEquiv_homogeneous b hp⟩
  intro i
  apply (basisLinearPolynomialEquiv b).injective
  rw [AlgEquiv.apply_symm_apply]
  change coefficientLinearPolynomial (l i) = basisLinearSubstitution b (X i.castSucc)
  rw [basisLinearSubstitution, aeval_X, hb, Fin.snoc_castSucc]

set_option maxRecDepth 2048 in
/-- The coordinate normalization for the actual polar forms is derived from
the determinant Jacobian condition and the common coordinate point. Neither
linear independence nor an invertible substitution is a separate input. -/
theorem linearMatrixNet_exists_normalizing_polar_coordinates
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K)
    (hM : ∀ i, (M i).IsSymm) (hbase : ∀ i, M i 0 0 = 0)
    (hsmooth : ∀ t : Fin 3 → K, t ≠ 0 → eval t (linearMatrixNet M).det = 0 →
      ∃ i, eval t (pderiv i (linearMatrixNet M).det) ≠ 0) :
    ∃ e : MvPolynomial (Fin 4) K ≃ₐ[K] MvPolynomial (Fin 4) K,
      (∀ i, e (coefficientLinearPolynomial (fun j : Fin 4 => M i j.succ 0)) =
        X i.castSucc) ∧
      (∀ {p : MvPolynomial (Fin 4) K} {d : ℕ}, p.IsHomogeneous d →
        (e p).IsHomogeneous d) ∧
      (∀ {p : MvPolynomial (Fin 4) K} {d : ℕ}, p.IsHomogeneous d →
        (e.symm p).IsHomogeneous d) :=
  exists_normalizing_linear_coordinate_equiv _
    (linearMatrixNet_polar_tails_linearIndependent M hM hbase hsmooth)

end EvenQuinticConic
