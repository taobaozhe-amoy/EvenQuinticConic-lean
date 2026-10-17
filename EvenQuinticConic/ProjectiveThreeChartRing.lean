import EvenQuinticConic.GradedRestriction
import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
import Mathlib.Data.Fin.Tuple.Basic

/-!
# The genuine standard chart ring of projective three-space

The equivalence here starts with degree-zero homogeneous fractions in four
variables. It identifies this actual ring with a polynomial ring in three
variables, by setting the selected homogeneous coordinate equal to one.
-/

noncomputable section
namespace EvenQuinticConic

open MvPolynomial HomogeneousLocalization

universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Constants in the degree-zero ring of the selected projective chart. -/
def threeChartConstants (p : Fin 4) :
    K →+* Away (homogeneousSubmodule (Fin 4) K) (X p) :=
  (HomogeneousLocalization.fromZeroRingHom (homogeneousSubmodule (Fin 4) K)
    (Submonoid.powers (X p))).comp
      (algebraMap K (homogeneousSubmodule (Fin 4) K 0))

/-- The actual homogeneous fraction `X_i / X_p`. -/
def threeChartRatio (p i : Fin 4) :
    Away (homogeneousSubmodule (Fin 4) K) (X p) :=
  Away.mk (homogeneousSubmodule (Fin 4) K) (isHomogeneous_X K p) 1 (X i)
    (by simpa using isHomogeneous_X K i)

/-- The actual fraction `F / X_p^d`. -/
def threeChartFraction (p : Fin 4) (d : ℕ) (F : MvPolynomial (Fin 4) K)
    (hF : F.IsHomogeneous d) : Away (homogeneousSubmodule (Fin 4) K) (X p) :=
  Away.mk (homogeneousSubmodule (Fin 4) K) (isHomogeneous_X K p) d F
    (by simpa using hF)

/-- Evaluation on normalized homogeneous coordinates recovers the
homogeneous fraction, with its actual denominator. -/
theorem threeChart_eval₂_homogeneous (p : Fin 4) (d : ℕ)
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous d) :
    eval₂ (threeChartConstants p) (threeChartRatio p) F =
      threeChartFraction p d F hF := by
  let S := MvPolynomial (Fin 4) K
  let L := Localization.Away (X p : S)
  let q : Away (homogeneousSubmodule (Fin 4) K) (X p) →+* L := algebraMap _ _
  let z : Submonoid.powers (X p : S) := ⟨X p, Submonoid.mem_powers _⟩
  let t : L := Localization.mk 1 z
  have hc : q.comp (threeChartConstants p) = (algebraMap S L).comp C := by
    ext c
    change Localization.mk (C c) (1 : Submonoid.powers (X p : S)) =
      algebraMap S L (C c)
    rfl
  have hx : (q ∘ threeChartRatio p) = fun i ↦ algebraMap S L (X i) * t := by
    funext i
    change (threeChartRatio p i).val =
      Localization.mk (X i) (1 : Submonoid.powers (X p : S)) * Localization.mk 1 z
    simp only [threeChartRatio, Away.val_mk, pow_one]
    rw [Localization.mk_mul, mul_one, one_mul]
  have heval : eval₂ ((algebraMap S L).comp C) (fun i ↦ algebraMap S L (X i)) F =
      algebraMap S L F := by
    calc
      _ = (algebraMap S L) (eval₂ C MvPolynomial.X F) :=
        (eval₂_comp_left (algebraMap S L) C MvPolynomial.X F).symm
      _ = _ := congrArg (algebraMap S L) (MvPolynomial.eval₂_eta F)
  apply HomogeneousLocalization.val_injective (Submonoid.powers (X p : S))
  change q (eval₂ (threeChartConstants p) (threeChartRatio p) F) = _
  rw [eval₂_comp_left, hc, hx, homogeneous_eval₂_scale _ _ t F d hF, heval]
  change Localization.mk F (1 : Submonoid.powers (X p : S)) *
    (Localization.mk 1 z) ^ d = Localization.mk F (z ^ d)
  rw [Localization.mk_pow, one_pow, Localization.mk_mul, mul_one, one_mul]

@[simp] theorem threeChartRatio_pivot (p : Fin 4) :
    threeChartRatio (K := K) p p = 1 := by
  apply HomogeneousLocalization.val_injective
    (𝒜 := homogeneousSubmodule (Fin 4) K) (Submonoid.powers (X p))
  simp only [threeChartRatio, Away.val_mk, pow_one, val_one]
  rw [Localization.mk_eq_mk', IsLocalization.mk'_self]

/-- Dehomogenization extended to the ordinary localization, whose selected
coordinate maps to the unit one. -/
def threeChartOrdinaryEvaluation (p : Fin 4) :
    Localization.Away (X p : MvPolynomial (Fin 4) K) →+* MvPolynomial (Fin 3) K :=
  IsLocalization.Away.lift (X p)
    (g := eval₂Hom C (Fin.insertNth p 1 X)) (by simp)

/-- Dehomogenization of actual degree-zero homogeneous fractions. -/
def threeChartToPolynomial (p : Fin 4) :
    Away (homogeneousSubmodule (Fin 4) K) (X p) →+* MvPolynomial (Fin 3) K :=
  (threeChartOrdinaryEvaluation p).comp (algebraMap _ _)

/-- The three affine coordinates are ratios of the other homogeneous
coordinates by the selected coordinate. -/
def polynomialToThreeChart (p : Fin 4) :
    MvPolynomial (Fin 3) K →+* Away (homogeneousSubmodule (Fin 4) K) (X p) :=
  eval₂Hom (threeChartConstants p) (fun i => threeChartRatio p (p.succAbove i))

/-- The denominator of a homogeneous chart fraction evaluates to one. -/
@[simp] theorem threeChartToPolynomial_fraction (p : Fin 4) (d : ℕ)
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous d) :
    threeChartToPolynomial p (threeChartFraction p d F hF) =
      eval₂ C (Fin.insertNth p 1 X) F := by
  change threeChartOrdinaryEvaluation p
    (Localization.mk F ⟨(X p) ^ d, by use d⟩) = _
  rw [Localization.mk_eq_mk']
  unfold threeChartOrdinaryEvaluation IsLocalization.Away.lift
  apply (IsLocalization.lift_mk'_spec _ _ _ _).2
  simp

@[simp] theorem threeChartToPolynomial_constants (p : Fin 4) (c : K) :
    threeChartToPolynomial p (threeChartConstants p c) = C c := by
  change threeChartOrdinaryEvaluation p
    (algebraMap (MvPolynomial (Fin 4) K) (Localization.Away (X p : MvPolynomial (Fin 4) K)) (C c)) = C c
  simp [threeChartOrdinaryEvaluation]

@[simp] theorem threeChartToPolynomial_ratio (p i : Fin 4) :
    threeChartToPolynomial (K := K) p (threeChartRatio p i) =
      Fin.insertNth (α := fun _ : Fin 4 => MvPolynomial (Fin 3) K) p 1 X i := by
  have h := threeChartToPolynomial_fraction p 1 (X i) (isHomogeneous_X K i)
  simpa [threeChartRatio, threeChartFraction] using h

/-- Substituting the three ratios after dehomogenization recovers evaluation
in all four normalized homogeneous coordinates. -/
theorem polynomialToThreeChart_dehomogenize (p : Fin 4)
    (F : MvPolynomial (Fin 4) K) :
    polynomialToThreeChart p (eval₂ C (Fin.insertNth p 1 X) F) =
      eval₂ (threeChartConstants p) (threeChartRatio p) F := by
  rw [eval₂_comp_left]
  have hc : (polynomialToThreeChart (K := K) p).comp C = threeChartConstants p := by
    ext c
    simp [polynomialToThreeChart]
  rw [hc]
  congr 1
  funext i
  exact Fin.succAboveCases p (by simp)
    (fun j => by simp [polynomialToThreeChart]) i

/-- One inverse law is checked on the three actual affine coordinates. -/
theorem threeChartToPolynomial_comp_polynomialToThreeChart (p : Fin 4) :
    (threeChartToPolynomial p).comp (polynomialToThreeChart p) =
      RingHom.id (MvPolynomial (Fin 3) K) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [polynomialToThreeChart]
  · intro i
    simp [polynomialToThreeChart]

/-- The other inverse law uses that every degree-zero homogeneous fraction
has a homogeneous numerator and a power of the selected coordinate below. -/
theorem polynomialToThreeChart_comp_threeChartToPolynomial (p : Fin 4) :
    (polynomialToThreeChart p).comp (threeChartToPolynomial p) =
      RingHom.id (Away (homogeneousSubmodule (Fin 4) K) (X p)) := by
  apply RingHom.ext
  intro z
  obtain ⟨d, F, hF, rfl⟩ := Away.mk_surjective
    (homogeneousSubmodule (Fin 4) K) (isHomogeneous_X K p) z
  have hF' : F.IsHomogeneous d := by simpa using hF
  change polynomialToThreeChart p
    (threeChartToPolynomial p (threeChartFraction p d F hF')) =
      threeChartFraction p d F hF'
  rw [threeChartToPolynomial_fraction, polynomialToThreeChart_dehomogenize,
    threeChart_eval₂_homogeneous]

/-- The actual standard chart of projective three-space has the polynomial
coordinate ring in three variables. -/
def projectiveThreeChartRingEquiv (p : Fin 4) :
    Away (homogeneousSubmodule (Fin 4) K) (X p) ≃+* MvPolynomial (Fin 3) K :=
  RingEquiv.ofHomInv (threeChartToPolynomial p) (polynomialToThreeChart p)
    (polynomialToThreeChart_comp_threeChartToPolynomial p)
    (threeChartToPolynomial_comp_polynomialToThreeChart p)

@[simp] theorem projectiveThreeChartRingEquiv_constants (p : Fin 4) (c : K) :
    projectiveThreeChartRingEquiv p (threeChartConstants p c) = C c :=
  threeChartToPolynomial_constants p c

@[simp] theorem projectiveThreeChartRingEquiv_fraction (p : Fin 4) (d : ℕ)
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous d) :
    projectiveThreeChartRingEquiv p (threeChartFraction p d F hF) =
      eval₂ C (Fin.insertNth p 1 X) F :=
  threeChartToPolynomial_fraction p d F hF

/-- The coefficient algebra on the genuine homogeneous chart ring. It is
named explicitly so later constructions use this same coefficient map. -/
def threeChartAlgebra (p : Fin 4) :
    Algebra K (Away (homogeneousSubmodule (Fin 4) K) (X p)) :=
  (threeChartConstants p).toAlgebra

/-- The standard chart equivalence respects the ground field, not merely
the underlying commutative rings. -/
def projectiveThreeChartAlgEquiv (p : Fin 4) :
    letI := threeChartAlgebra (K := K) p
    Away (homogeneousSubmodule (Fin 4) K) (X p) ≃ₐ[K] MvPolynomial (Fin 3) K := by
  letI := threeChartAlgebra (K := K) p
  exact AlgEquiv.ofRingEquiv (f := projectiveThreeChartRingEquiv p)
    (projectiveThreeChartRingEquiv_constants p)

end EvenQuinticConic
