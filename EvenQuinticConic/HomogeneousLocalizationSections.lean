import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.Localization.AsSubring
import EvenQuinticConic.PlaneQuintic

/-!
# Clearing two coordinate denominators on a monic hypersurface

A monic equation over a two-coordinate polynomial ring gives a genuine free
module basis of its quotient algebra. Relatively prime coordinate powers
can therefore be cancelled coefficient by coefficient, even when the
hypersurface quotient is not a unique factorization domain.

A second, separate result extracts a homogeneous polynomial representative
from an element of the actual plane-curve cone ring once denominators have
been cleared. It uses the grading of the actual principal homogeneous ideal.

This is an algebraic input to the calculation of projective twisting-sheaf
sections. The later `PlaneQuadraticSurjectivity` proof connects these results
to actual sheaf sections using explicit good coordinates, actual cone
equivalences, and regular functions on arbitrary linear charts. The lemmas
in this file alone do not perform those geometric comparisons.
-/

noncomputable section

namespace EvenQuinticConic

section FreeModule

variable {R M : Type*} [CommRing R] [IsDomain R] [DecompositionMonoid R]
  [AddCommGroup M] [Module R M]

/-- Clear relatively prime scalar denominators in a genuine finite free
module, by applying the actual basis coordinates. -/
theorem exists_common_numerator_of_basis
    {ι : Type*} [Fintype ι] (basis : Module.Basis ι R M)
    (x y : R) (hx : x ≠ 0) (hxy : IsRelPrime x y) (m n : ℕ)
    (a b : M) (h : y ^ n • a = x ^ m • b) :
    ∃ c : M, a = x ^ m • c ∧ b = y ^ n • c := by
  classical
  have hcoord (i : ι) :
      y ^ n * basis.equivFun a i = x ^ m * basis.equivFun b i := by
    have hi := congrArg (fun z ↦ basis.equivFun z i) h
    simpa only [map_smul, Pi.smul_apply, smul_eq_mul] using hi
  have hdiv (i : ι) : x ^ m ∣ basis.equivFun a i :=
    (hxy.pow (m := m) (n := n)).dvd_of_dvd_mul_left ⟨basis.equivFun b i, hcoord i⟩
  choose coeff hcoeff using hdiv
  let c := basis.equivFun.symm coeff
  have hc (i : ι) : basis.equivFun c i = coeff i :=
    congrFun (basis.equivFun.apply_symm_apply coeff) i
  refine ⟨c, ?_, ?_⟩
  · apply basis.equivFun.injective
    funext i
    simpa only [map_smul, Pi.smul_apply, smul_eq_mul, hc] using hcoeff i
  · apply basis.equivFun.injective
    funext i
    simp only [map_smul, Pi.smul_apply, smul_eq_mul, hc]
    apply mul_left_cancel₀ (pow_ne_zero m hx)
    calc
      x ^ m * basis.equivFun b i = y ^ n * basis.equivFun a i := (hcoord i).symm
      _ = y ^ n * (x ^ m * coeff i) := by rw [hcoeff i]
      _ = x ^ m * (y ^ n * coeff i) := by ring

end FreeModule

section MonicHypersurface

variable {R : Type*} [CommRing R] [IsDomain R] [DecompositionMonoid R]

/-- A monic hypersurface quotient has enough actual basis coordinates to
clear two relatively prime base-coordinate denominators. No factoriality
of the quotient algebra is assumed. -/
theorem monic_hypersurface_clear_denominators
    (F : Polynomial R) (hF : F.Monic)
    (x y : R) (hx : x ≠ 0) (hxy : IsRelPrime x y) (m n : ℕ)
    (a b : AdjoinRoot F)
    (h : y ^ n • a = x ^ m • b) :
    ∃ c : AdjoinRoot F, a = x ^ m • c ∧ b = y ^ n • c :=
  exists_common_numerator_of_basis (AdjoinRoot.powerBasisAux' hF) x y hx hxy m n a b h

omit [DecompositionMonoid R] in
/-- The base ring embeds into a positive-degree monic hypersurface quotient;
this is proved from the actual quotient presentation. -/
theorem monic_hypersurface_base_injective
    (F : Polynomial R) (_hF : F.Monic) (hdeg : 0 < F.natDegree) :
    Function.Injective (algebraMap R (AdjoinRoot F)) := by
  apply AdjoinRoot.of.injective_of_degree_ne_zero
  exact ne_of_gt (Polynomial.natDegree_pos_iff_degree_pos.mp hdeg)

/-- Equal fractions with the two base-coordinate power denominators come
from an element of the actual monic hypersurface quotient. -/
theorem monic_hypersurface_common_fraction
    (F : Polynomial R) (hF : F.Monic) (hdeg : 0 < F.natDegree)
    [IsDomain (AdjoinRoot F)]
    (L : Type*) [Field L] [Algebra (AdjoinRoot F) L] [IsFractionRing (AdjoinRoot F) L]
    (x y : R) (hx : x ≠ 0) (hy : y ≠ 0) (hxy : IsRelPrime x y)
    (m n : ℕ) (a b : AdjoinRoot F)
    (h : algebraMap (AdjoinRoot F) L a /
          (algebraMap (AdjoinRoot F) L (algebraMap R (AdjoinRoot F) x)) ^ m =
        algebraMap (AdjoinRoot F) L b /
          (algebraMap (AdjoinRoot F) L (algebraMap R (AdjoinRoot F) y)) ^ n) :
    ∃ c : AdjoinRoot F,
      algebraMap (AdjoinRoot F) L a /
          (algebraMap (AdjoinRoot F) L (algebraMap R (AdjoinRoot F) x)) ^ m =
        algebraMap (AdjoinRoot F) L c := by
  let ι := algebraMap R (AdjoinRoot F)
  let j := algebraMap (AdjoinRoot F) L
  have hι := monic_hypersurface_base_injective F hF hdeg
  have hj := IsFractionRing.injective (AdjoinRoot F) L
  have hxA : ι x ≠ 0 := by simpa only [map_zero] using hι.ne hx
  have hyA : ι y ≠ 0 := by simpa only [map_zero] using hι.ne hy
  have hxL : j (ι x) ≠ 0 := by simpa only [map_zero] using hj.ne hxA
  have hyL : j (ι y) ≠ 0 := by simpa only [map_zero] using hj.ne hyA
  have hcross := (div_eq_div_iff (pow_ne_zero m hxL) (pow_ne_zero n hyL)).mp h
  have hquot : y ^ n • a = x ^ m • b := by
    apply hj
    simp only [Algebra.smul_def, map_mul, map_pow]
    simpa only [mul_comm] using hcross
  obtain ⟨c, ha, _⟩ := monic_hypersurface_clear_denominators F hF x y hx hxy m n a b hquot
  refine ⟨c, ?_⟩
  apply (div_eq_iff (pow_ne_zero m hxL)).mpr
  rw [ha]
  simp only [Algebra.smul_def, map_mul, map_pow]
  exact mul_comm _ _

end MonicHypersurface

section CoordinateLocalization

variable {A : Type*} [CommRing A] [IsDomain A]
  (L : Type*) [Field L] [Algebra A L] [IsFractionRing A L]

/-- The actual localization away from a coordinate, embedded as a subalgebra
of the actual fraction field. It carries mathlib's localization structure. -/
def coordinateLocalizationSubalgebra (x : A) (hx : x ≠ 0) : Subalgebra A L :=
  Localization.subalgebra.ofField L (Submonoid.powers x)
    (powers_le_nonZeroDivisors_of_noZeroDivisors hx)

instance coordinateLocalizationSubalgebra_isLocalization (x : A) (hx : x ≠ 0) :
    IsLocalization.Away x (coordinateLocalizationSubalgebra L x hx) := by
  unfold coordinateLocalizationSubalgebra
  infer_instance

/-- Membership in the genuine coordinate localization is equivalent to a
fraction whose denominator is a nonnegative power of that coordinate. -/
theorem mem_coordinateLocalizationSubalgebra_iff (x : A) (hx : x ≠ 0) (z : L) :
    z ∈ coordinateLocalizationSubalgebra L x hx ↔
      ∃ (n : ℕ) (a : A), z = algebraMap A L a / algebraMap A L x ^ n := by
  change (∃ (a s : A) (_ : s ∈ Submonoid.powers x),
    z = algebraMap A L a * (algebraMap A L s)⁻¹) ↔ _
  constructor
  · rintro ⟨a, s, ⟨n, rfl⟩, hz⟩
    exact ⟨n, a, by simpa only [map_pow, div_eq_mul_inv] using hz⟩
  · rintro ⟨n, a, hz⟩
    exact ⟨a, x ^ n, ⟨n, rfl⟩, by simpa only [map_pow, div_eq_mul_inv] using hz⟩

end CoordinateLocalization

section MonicIntersection

variable {R : Type*} [CommRing R] [IsDomain R] [DecompositionMonoid R]

omit [DecompositionMonoid R] in
/-- A nonzero base coordinate stays nonzero in the positive-degree monic
hypersurface algebra. -/
theorem monic_hypersurface_base_ne_zero
    (F : Polynomial R) (hF : F.Monic) (hdeg : 0 < F.natDegree)
    (x : R) (hx : x ≠ 0) : algebraMap R (AdjoinRoot F) x ≠ 0 := by
  simpa only [map_zero] using (monic_hypersurface_base_injective F hF hdeg).ne hx

/-- The two actual coordinate localizations intersect in precisely the
original monic hypersurface algebra inside its fraction field. Here bottom
means the image of that algebra, not the zero subring. -/
theorem monic_hypersurface_coordinate_localizations_intersection
    (F : Polynomial R) (hF : F.Monic) (hdeg : 0 < F.natDegree)
    [IsDomain (AdjoinRoot F)]
    (L : Type*) [Field L] [Algebra (AdjoinRoot F) L] [IsFractionRing (AdjoinRoot F) L]
    (x y : R) (hx : x ≠ 0) (hy : y ≠ 0) (hxy : IsRelPrime x y) :
    coordinateLocalizationSubalgebra L (algebraMap R (AdjoinRoot F) x)
        (monic_hypersurface_base_ne_zero F hF hdeg x hx) ⊓
      coordinateLocalizationSubalgebra L (algebraMap R (AdjoinRoot F) y)
        (monic_hypersurface_base_ne_zero F hF hdeg y hy) = ⊥ := by
  apply eq_bot_iff.mpr
  intro z hz
  obtain ⟨m, a, ha⟩ := (mem_coordinateLocalizationSubalgebra_iff L _ _ z).mp hz.1
  obtain ⟨n, b, hb⟩ := (mem_coordinateLocalizationSubalgebra_iff L _ _ z).mp hz.2
  obtain ⟨c, hc⟩ := monic_hypersurface_common_fraction F hF hdeg L x y hx hy hxy
    m n a b (ha.symm.trans hb)
  exact Algebra.mem_bot.mpr ⟨c, (ha.trans hc).symm⟩

end MonicIntersection

section TwoPolynomialCoordinates

variable (K : Type*) [Field K]

/-- A concrete polynomial ring in two independent coordinates. The first
coordinate is the coefficient polynomial variable; the second is the outer
polynomial variable. -/
abbrev TwoCoordinatePolynomial := Polynomial (Polynomial K)

/-- The two concrete polynomial coordinates have no nonunit common factor;
this is proved, rather than assumed as a geometric cover condition. -/
theorem two_polynomial_coordinates_relPrime :
    IsRelPrime (Polynomial.C (Polynomial.X : Polynomial K) : TwoCoordinatePolynomial K)
      Polynomial.X := by
  apply IsRelPrime.symm
  apply Polynomial.irreducible_X.isRelPrime_iff_not_dvd.mpr
  simp [Polynomial.X_dvd_iff]

/-- Concrete form of the denominator-clearing theorem for a monic plane
hypersurface equation in a third variable over the two-coordinate ring. -/
theorem plane_monic_coordinate_localizations_intersection
    (F : Polynomial (TwoCoordinatePolynomial K)) (hF : F.Monic)
    (hdeg : 0 < F.natDegree) [IsDomain (AdjoinRoot F)] :
    coordinateLocalizationSubalgebra (FractionRing (AdjoinRoot F))
        (algebraMap (TwoCoordinatePolynomial K) (AdjoinRoot F)
          (Polynomial.C (Polynomial.X : Polynomial K)))
        (monic_hypersurface_base_ne_zero F hF hdeg _ (by simp)) ⊓
      coordinateLocalizationSubalgebra (FractionRing (AdjoinRoot F))
        (algebraMap (TwoCoordinatePolynomial K) (AdjoinRoot F) Polynomial.X)
        (monic_hypersurface_base_ne_zero F hF hdeg _ (by simp)) = ⊥ := by
  exact monic_hypersurface_coordinate_localizations_intersection F hF hdeg
    (FractionRing (AdjoinRoot F)) _ _ (by simp) (by simp)
    (two_polynomial_coordinates_relPrime K)

end TwoPolynomialCoordinates

section HomogeneousSlice

open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K : Type*} [Field K]

/-- Once coordinate denominators have been cleared in the actual cone ring,
a homogeneous numerator forces a homogeneous representative of the predicted
degree. The result is obtained by projecting an actual ideal relation and
cancelling the coordinate power in the prime homogeneous ideal.

The comparison with actual sheaf sections and the monic quotient presentation
is supplied by the later quadratic-surjectivity construction. -/
theorem plane_cone_homogeneous_representative (F : PlanePolynomial K) (e : ℕ) (hF : F.IsHomogeneous e)
    [(Ideal.span {F}).IsPrime] (hFdeg : 1 < F.totalDegree)
    (j : Fin 3) (m d : ℕ) (A : PlanePolynomial K) (hA : A.IsHomogeneous (m+d))
    (c : PlaneConeQuotient F)
    (h : (Ideal.Quotient.mk (Ideal.span {F}) (X j)) ^ m * c =
      Ideal.Quotient.mk (Ideal.span {F}) A) :
    ∃ P : PlanePolynomial K, P.IsHomogeneous d ∧
      Ideal.Quotient.mk (Ideal.span {F}) P = c := by
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective c
  have hi : (X j)^m*g-A ∈ Ideal.span {F} := by
    apply (Ideal.Quotient.eq_zero_iff_mem).mp
    simp only [map_sub, map_mul, map_pow, h, sub_self]
  have hic := (planeHomogeneousPrincipal F e hF).isHomogeneous (m+d) hi
  change GradedRing.proj (homogeneousSubmodule (Fin 3) K) (m+d) ((X j)^m*g-A) ∈
    Ideal.span {F} at hic
  have hmono : ((X j : PlanePolynomial K)^m).IsHomogeneous m := by
    simpa using (isHomogeneous_X K j).pow m
  have hh : GradedRing.proj (homogeneousSubmodule (Fin 3) K) (m+d) ((X j)^m*g) =
      (X j)^m * GradedRing.proj (homogeneousSubmodule (Fin 3) K) d g :=
    DirectSum.coe_decompose_mul_add_of_left_mem (homogeneousSubmodule (Fin 3) K) hmono
  have hAp : GradedRing.proj (homogeneousSubmodule (Fin 3) K) (m+d) A = A :=
    DirectSum.decompose_of_mem_same (homogeneousSubmodule (Fin 3) K) hA
  rw [map_sub, hh, hAp] at hic
  have hdiv : (X j)^m * (g - GradedRing.proj (homogeneousSubmodule (Fin 3) K) d g) ∈ Ideal.span {F} := by
    convert (Ideal.span {F}).sub_mem hi hic using 1
    ring
  have hxnot : (X j)^m ∉ Ideal.span {F} := by
    intro hp
    have hp' : X j ∈ Ideal.span {F} := (Ideal.IsPrime.mem_of_pow_mem inferInstance m hp)
    exact plane_coordinate_not_mem_principal F hFdeg j hp'
  have hdiff : g-GradedRing.proj (homogeneousSubmodule (Fin 3) K) d g ∈ Ideal.span {F} :=
    ((inferInstance : (Ideal.span {F}).IsPrime).mem_or_mem hdiv).resolve_left hxnot
  refine ⟨GradedRing.proj (homogeneousSubmodule (Fin 3) K) d g,
    (DirectSum.decompose (homogeneousSubmodule (Fin 3) K) g d).property, ?_⟩
  apply (Ideal.Quotient.eq).mpr
  simpa only [neg_sub] using (Ideal.span {F}).neg_mem hdiff

/-- Degree-two specialization of homogeneous representative extraction. -/
theorem plane_cone_quadratic_representative
    (F : PlanePolynomial K) (e : ℕ) (hF : F.IsHomogeneous e)
    [(Ideal.span {F}).IsPrime] (hFdeg : 1 < F.totalDegree)
    (j : Fin 3) (m : ℕ) (A : PlanePolynomial K) (hA : A.IsHomogeneous (m + 2))
    (c : PlaneConeQuotient F)
    (h : (Ideal.Quotient.mk (Ideal.span {F}) (X j)) ^ m * c =
      Ideal.Quotient.mk (Ideal.span {F}) A) :
    ∃ P : PlanePolynomial K, P.IsHomogeneous 2 ∧
      Ideal.Quotient.mk (Ideal.span {F}) P = c :=
  plane_cone_homogeneous_representative F e hF hFdeg j m 2 A hA c h

end HomogeneousSlice

end EvenQuinticConic
