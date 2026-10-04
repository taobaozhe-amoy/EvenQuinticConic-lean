import EvenQuinticConic.RestrictionModel
import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# A restriction map retaining the homogeneous degree

The map constructed here sends `X i` to `C (f i) * X` in the univariate
polynomial ring over the coefficient algebra. The new variable retains the
homogeneous degree. Its coefficient in degree `d` is the ordinary evaluation
of the degree-`d` homogeneous component.

These are actual polynomial algebra homomorphisms, not maps from a geometric
section ring. `PlaneHomogeneousKernel` supplies the geometric vanishing-ideal
theorem that identifies this kernel for an actual integral plane curve.
-/

noncomputable section

namespace EvenQuinticConic

open MvPolynomial

variable {σ K L : Type*} [CommSemiring K] [CommSemiring L]

/-- Homogeneous evaluation respects scaling of all coordinates. -/
theorem homogeneous_eval₂_scale (g : K →+* L) (f : σ → L) (t : L)
    (P : MvPolynomial σ K) (d : ℕ) (hP : P.IsHomogeneous d) :
    eval₂ g (fun i => f i * t) P = eval₂ g f P * t ^ d := by
  classical
  simp only [eval₂_eq, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro m hm
  have hmdeg : (∑ i ∈ m.support, m i) = d := by
    simpa only [Finsupp.weight_apply, Pi.one_apply, smul_eq_mul, mul_one,
      Finsupp.sum] using hP (mem_support_iff.mp hm)
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hmdeg]
  ring

/-- A concrete restriction map into a polynomial ring, retaining the degree. -/
def gradedRestriction [Algebra K L] (f : σ → L) :
    MvPolynomial σ K →ₐ[K] Polynomial L :=
  aeval (fun i => Polynomial.C (f i) * Polynomial.X)

@[simp]
theorem gradedRestriction_X [Algebra K L] (f : σ → L) (i : σ) :
    gradedRestriction (K := K) f (X i) = Polynomial.C (f i) * Polynomial.X := by
  simp [gradedRestriction]

/-- Homogeneous forms retain their degree under the concrete restriction map. -/
theorem gradedRestriction_of_isHomogeneous [Algebra K L] (f : σ → L)
    (P : MvPolynomial σ K) (d : ℕ) (hP : P.IsHomogeneous d) :
    gradedRestriction f P = Polynomial.C (aeval f P) * Polynomial.X ^ d := by
  rw [gradedRestriction, aeval_def,
    homogeneous_eval₂_scale (algebraMap K (Polynomial L))
      (fun i => Polynomial.C (f i)) Polynomial.X P d hP]
  congr 1
  rw [aeval_def, eval₂_comp_left]
  rfl

/-- The new variable records the evaluations of all homogeneous components. -/
theorem gradedRestriction_eq_sum [Algebra K L] (f : σ → L)
    (P : MvPolynomial σ K) :
    gradedRestriction f P =
      ∑ d ∈ Finset.range (P.totalDegree + 1),
        Polynomial.C (aeval f (homogeneousComponent d P)) * Polynomial.X ^ d := by
  calc
    gradedRestriction f P = gradedRestriction f
        (∑ d ∈ Finset.range (P.totalDegree + 1), homogeneousComponent d P) := by
      rw [sum_homogeneousComponent]
    _ = _ := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro d _
      exact gradedRestriction_of_isHomogeneous f _ d
        (homogeneousComponent_isHomogeneous d P)

/-- Distinct homogeneous degrees cannot cancel after graded restriction. -/
theorem coeff_gradedRestriction [Algebra K L] (f : σ → L)
    (P : MvPolynomial σ K) (d : ℕ) :
    (gradedRestriction f P).coeff d = aeval f (homogeneousComponent d P) := by
  rw [gradedRestriction_eq_sum, Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  by_cases hd : d < P.totalDegree + 1
  · simp [hd]
  · have hd' : P.totalDegree < d := by omega
    simp [hd, homogeneousComponent_eq_zero d P hd']

/-- Vanishing of the graded restriction is equivalent to vanishing separately
in every homogeneous degree. Ordinary affine evaluation lacks this property. -/
theorem gradedRestriction_eq_zero_iff [Algebra K L] (f : σ → L)
    (P : MvPolynomial σ K) :
    gradedRestriction f P = 0 ↔
      ∀ d : ℕ, aeval f (homogeneousComponent d P) = 0 := by
  rw [Polynomial.ext_iff]
  simp only [coeff_gradedRestriction, Polynomial.coeff_zero]

/-- Every homogeneous component of a polynomial in the restriction kernel
also lies in that kernel. -/
theorem gradedRestriction_homogeneousComponent_eq_zero [Algebra K L]
    (f : σ → L) (P : MvPolynomial σ K)
    (hP : gradedRestriction f P = 0) (d : ℕ) :
    gradedRestriction f (homogeneousComponent d P) = 0 := by
  rw [gradedRestriction_of_isHomogeneous f _ d
    (homogeneousComponent_isHomogeneous d P),
    (gradedRestriction_eq_zero_iff f P).mp hP d]
  simp

/-- The degreewise description of the actual kernel of graded restriction. -/
theorem mem_ker_gradedRestriction_iff [Algebra K L] (f : σ → L)
    (P : MvPolynomial σ K) :
    P ∈ RingHom.ker (gradedRestriction f).toRingHom ↔
      ∀ d : ℕ, aeval f (homogeneousComponent d P) = 0 := by
  rw [RingHom.mem_ker]
  exact gradedRestriction_eq_zero_iff f P

/-- A homogeneous vanishing-ideal theorem is enough to identify the entire
kernel. The hypothesis only concerns homogeneous forms; the degree variable
then rules out cancellation between components of an arbitrary polynomial. -/
theorem ker_gradedRestriction_eq_span_of_homogeneous_vanishing [Algebra K L]
    (f : σ → L) (F : MvPolynomial σ K) (e : ℕ)
    (hF : F.IsHomogeneous e) (hFzero : aeval f F = 0)
    (hvan : ∀ (P : MvPolynomial σ K) (d : ℕ),
      P.IsHomogeneous d → aeval f P = 0 → P ∈ Ideal.span {F}) :
    RingHom.ker (gradedRestriction f).toRingHom = Ideal.span {F} := by
  apply le_antisymm
  · intro P hP
    rw [mem_ker_gradedRestriction_iff] at hP
    rw [← sum_homogeneousComponent P]
    exact Ideal.sum_mem _ fun d _ =>
      hvan _ d (homogeneousComponent_isHomogeneous d P) (hP d)
  · apply Ideal.span_le.mpr
    intro P hP
    have hPF : P = F := Set.mem_singleton_iff.mp hP
    subst P
    change gradedRestriction f F = 0
    rw [gradedRestriction_of_isHomogeneous f F e hF, hFzero]
    simp

section ScalarExtension

variable {E : Type*} [CommSemiring E] [Algebra K L] [Algebra K E]

/-- Extension of coefficients commutes with the graded restriction map. -/
theorem mapAlgHom_comp_gradedRestriction (g : L →ₐ[K] E) (f : σ → L) :
    (Polynomial.mapAlgHom g).comp (gradedRestriction f) =
      gradedRestriction (fun i => g (f i)) := by
  ext i
  simp [gradedRestriction, Polynomial.coe_mapAlgHom]

/-- An injective extension of coefficients does not change the restriction
kernel, because the degree variable remains transcendental. -/
theorem ker_gradedRestriction_scalarExtension (g : L →ₐ[K] E)
    (hg : Function.Injective g) (f : σ → L) :
    RingHom.ker (gradedRestriction (K := K) (fun i => g (f i))).toRingHom =
      RingHom.ker (gradedRestriction (K := K) f).toRingHom := by
  ext P
  simp only [RingHom.mem_ker]
  change gradedRestriction (fun i => g (f i)) P = 0 ↔ gradedRestriction f P = 0
  rw [← mapAlgHom_comp_gradedRestriction g f]
  change Polynomial.map g.toRingHom (gradedRestriction f P) = 0 ↔ _
  exact Polynomial.map_eq_zero_iff hg

end ScalarExtension

end EvenQuinticConic
