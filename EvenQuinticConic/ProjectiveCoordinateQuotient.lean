import EvenQuinticConic.GradedRestriction
import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-!
# A projective standard chart as the quotient `X_p = 1`

This construction works with any index type and the genuine degree-zero
homogeneous localization. It retains every homogeneous coordinate, imposing
the single pivot relation, so it can be composed directly with homogeneous
closed equations in a Segre ambient space.
-/

noncomputable section
namespace EvenQuinticConic
open MvPolynomial HomogeneousLocalization

universe u v
variable {K : Type u} [Field K] {σ : Type v}
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The explicit equation setting the chosen homogeneous coordinate to one. -/
def projectiveCoordinateIdeal (p : σ) : Ideal (MvPolynomial σ K) :=
  Ideal.span {X p - 1}

/-- The affine coordinate ring retaining all coordinates and the pivot relation. -/
abbrev ProjectiveCoordinateQuotient (p : σ) :=
  MvPolynomial σ K ⧸ projectiveCoordinateIdeal (K := K) p

/-- The actual coefficient map into homogeneous degree-zero fractions. -/
def projectiveCoordinateConstants (p : σ) :
    K →+* Away (homogeneousSubmodule σ K) (X p) :=
  (HomogeneousLocalization.fromZeroRingHom (homogeneousSubmodule σ K)
    (Submonoid.powers (X p))).comp (algebraMap K (homogeneousSubmodule σ K 0))

/-- The actual degree-zero fraction `X_i/X_p`. -/
def projectiveCoordinateRatio (p i : σ) :
    Away (homogeneousSubmodule σ K) (X p) :=
  Away.mk (homogeneousSubmodule σ K) (isHomogeneous_X K p) 1 (X i)
    (by simpa using isHomogeneous_X K i)

/-- The actual degree-zero fraction with homogeneous numerator `F`. -/
def projectiveCoordinateFraction (p : σ) (d : ℕ) (F : MvPolynomial σ K)
    (hF : F.IsHomogeneous d) : Away (homogeneousSubmodule σ K) (X p) :=
  Away.mk (homogeneousSubmodule σ K) (isHomogeneous_X K p) d F
    (by simpa using hF)

/-- Evaluation on ratios equals the homogeneous fraction itself. -/
theorem projectiveCoordinate_eval₂_homogeneous (p : σ) (d : ℕ)
    (F : MvPolynomial σ K) (hF : F.IsHomogeneous d) :
    eval₂ (projectiveCoordinateConstants (K := K) p) (projectiveCoordinateRatio (K := K) p) F =
      projectiveCoordinateFraction (K := K) p d F hF := by
  let S := MvPolynomial σ K
  let L := Localization.Away (X p : S)
  let q : Away (homogeneousSubmodule σ K) (X p) →+* L := algebraMap _ _
  let z : Submonoid.powers (X p : S) := ⟨X p, Submonoid.mem_powers _⟩
  let t : L := Localization.mk 1 z
  have hc : q.comp (projectiveCoordinateConstants (K := K) p) = (algebraMap S L).comp C := by
    ext c
    change Localization.mk (C c) (1 : Submonoid.powers (X p : S)) =
      algebraMap S L (C c)
    rfl
  have hx : (q ∘ projectiveCoordinateRatio (K := K) p) = fun i ↦ algebraMap S L (X i) * t := by
    funext i
    change (projectiveCoordinateRatio (K := K) p i).val =
      Localization.mk (X i) (1 : Submonoid.powers (X p : S)) * Localization.mk 1 z
    simp only [projectiveCoordinateRatio, Away.val_mk, pow_one]
    rw [Localization.mk_mul, mul_one, one_mul]
  have heval : eval₂ ((algebraMap S L).comp C) (fun i ↦ algebraMap S L (X i)) F =
      algebraMap S L F := by
    calc
      _ = (algebraMap S L) (eval₂ C MvPolynomial.X F) :=
        (eval₂_comp_left (algebraMap S L) C MvPolynomial.X F).symm
      _ = _ := congrArg (algebraMap S L) (MvPolynomial.eval₂_eta F)
  apply HomogeneousLocalization.val_injective (Submonoid.powers (X p : S))
  change q (eval₂ (projectiveCoordinateConstants (K := K) p) (projectiveCoordinateRatio (K := K) p) F) = _
  rw [eval₂_comp_left, hc, hx, homogeneous_eval₂_scale _ _ t F d hF, heval]
  change Localization.mk F (1 : Submonoid.powers (X p : S)) *
    (Localization.mk 1 z) ^ d = Localization.mk F (z ^ d)
  rw [Localization.mk_pow, one_pow, Localization.mk_mul, mul_one, one_mul]

@[simp] theorem projectiveCoordinateRatio_pivot (p : σ) :
    projectiveCoordinateRatio (K := K) p p = 1 := by
  apply HomogeneousLocalization.val_injective
    (𝒜 := homogeneousSubmodule σ K) (Submonoid.powers (X p))
  simp only [projectiveCoordinateRatio, Away.val_mk, pow_one, val_one]
  rw [Localization.mk_eq_mk', IsLocalization.mk'_self]

@[simp] theorem projectiveCoordinateQuotient_pivot (p : σ) :
    Ideal.Quotient.mk (projectiveCoordinateIdeal (K := K) p) (X p) = 1 := by
  have h : Ideal.Quotient.mk (projectiveCoordinateIdeal (K := K) p) (X p - 1) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  simpa only [map_sub, map_one, sub_eq_zero] using h

/-- Ordinary localization can be evaluated in the pivot quotient since the
selected coordinate maps to the unit one. -/
def projectiveCoordinateOrdinaryEvaluation (p : σ) :
    Localization.Away (X p : MvPolynomial σ K) →+* ProjectiveCoordinateQuotient (K := K) p :=
  IsLocalization.Away.lift (X p)
    (g := Ideal.Quotient.mk (projectiveCoordinateIdeal (K := K) p)) (by simp)

/-- Evaluation of genuine degree-zero fractions in the pivot quotient. -/
def projectiveCoordinateToQuotient (p : σ) :
    Away (homogeneousSubmodule σ K) (X p) →+* ProjectiveCoordinateQuotient (K := K) p :=
  (projectiveCoordinateOrdinaryEvaluation (K := K) p).comp (algebraMap _ _)

/-- Substitution by the coordinate ratios kills the pivot relation. -/
theorem projectiveCoordinateIdeal_le_ker (p : σ) :
    projectiveCoordinateIdeal (K := K) p ≤
      RingHom.ker (eval₂Hom (projectiveCoordinateConstants (K := K) p) (projectiveCoordinateRatio (K := K) p)) := by
  rw [projectiveCoordinateIdeal, Ideal.span_le]
  intro F hF
  have hF' : F = X p - 1 := Set.mem_singleton_iff.mp hF
  subst F
  simp [RingHom.mem_ker]

/-- The inverse substitution from the literal pivot quotient into the
actual homogeneous chart ring. -/
def projectiveQuotientToCoordinate (p : σ) :
    ProjectiveCoordinateQuotient (K := K) p →+* Away (homogeneousSubmodule σ K) (X p) :=
  Ideal.Quotient.lift (projectiveCoordinateIdeal (K := K) p)
    (eval₂Hom (projectiveCoordinateConstants (K := K) p) (projectiveCoordinateRatio (K := K) p))
    (fun _ h => RingHom.mem_ker.mp (projectiveCoordinateIdeal_le_ker (K := K) p h))

@[simp] theorem projectiveQuotientToCoordinate_mk (p : σ) (F : MvPolynomial σ K) :
    projectiveQuotientToCoordinate (K := K) p (Ideal.Quotient.mk (projectiveCoordinateIdeal (K := K) p) F) =
      eval₂ (projectiveCoordinateConstants (K := K) p) (projectiveCoordinateRatio (K := K) p) F := rfl

/-- The denominator becomes one; the numerator maps to its literal quotient class. -/
@[simp] theorem projectiveCoordinateToQuotient_fraction (p : σ) (d : ℕ)
    (F : MvPolynomial σ K) (hF : F.IsHomogeneous d) :
    projectiveCoordinateToQuotient (K := K) p (projectiveCoordinateFraction (K := K) p d F hF) =
      Ideal.Quotient.mk (projectiveCoordinateIdeal (K := K) p) F := by
  change projectiveCoordinateOrdinaryEvaluation (K := K) p
    (Localization.mk F ⟨(X p) ^ d, by use d⟩) = _
  rw [Localization.mk_eq_mk']
  unfold projectiveCoordinateOrdinaryEvaluation IsLocalization.Away.lift
  apply (IsLocalization.lift_mk'_spec _ _ _ _).2
  simp

@[simp] theorem projectiveCoordinateToQuotient_constants (p : σ) (c : K) :
    projectiveCoordinateToQuotient (K := K) p (projectiveCoordinateConstants (K := K) p c) =
      Ideal.Quotient.mk (projectiveCoordinateIdeal (K := K) p) (C c) := by
  change projectiveCoordinateOrdinaryEvaluation (K := K) p
    (algebraMap (MvPolynomial σ K) (Localization.Away (X p : MvPolynomial σ K)) (C c)) = _
  simp [projectiveCoordinateOrdinaryEvaluation]

@[simp] theorem projectiveCoordinateToQuotient_ratio (p i : σ) :
    projectiveCoordinateToQuotient (K := K) p (projectiveCoordinateRatio (K := K) p i) =
      Ideal.Quotient.mk (projectiveCoordinateIdeal (K := K) p) (X i) := by
  simpa only [projectiveCoordinateRatio, projectiveCoordinateFraction] using
    projectiveCoordinateToQuotient_fraction p 1 (X i) (isHomogeneous_X K i)

theorem projectiveCoordinateToQuotient_comp_eval₂Hom (p : σ) :
    (projectiveCoordinateToQuotient (K := K) p).comp
        (eval₂Hom (projectiveCoordinateConstants (K := K) p) (projectiveCoordinateRatio (K := K) p)) =
      Ideal.Quotient.mk (projectiveCoordinateIdeal (K := K) p) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp
  · intro i
    simp

/-- The quotient-first composite is the identity on actual quotient classes. -/
theorem projectiveCoordinateToQuotient_comp_projectiveQuotientToCoordinate (p : σ) :
    (projectiveCoordinateToQuotient (K := K) p).comp (projectiveQuotientToCoordinate (K := K) p) =
      RingHom.id (ProjectiveCoordinateQuotient (K := K) p) := by
  apply RingHom.ext
  intro z
  obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective z
  exact congrArg (fun f : MvPolynomial σ K →+* ProjectiveCoordinateQuotient (K := K) p => f F)
    (projectiveCoordinateToQuotient_comp_eval₂Hom p)

/-- The fraction-first composite is the identity on every homogeneous fraction. -/
theorem projectiveQuotientToCoordinate_comp_projectiveCoordinateToQuotient (p : σ) :
    (projectiveQuotientToCoordinate (K := K) p).comp (projectiveCoordinateToQuotient (K := K) p) =
      RingHom.id (Away (homogeneousSubmodule σ K) (X p)) := by
  apply RingHom.ext
  intro z
  obtain ⟨d, F, hF, rfl⟩ := Away.mk_surjective
    (homogeneousSubmodule σ K) (isHomogeneous_X K p) z
  have hF' : F.IsHomogeneous d := by simpa using hF
  change projectiveQuotientToCoordinate (K := K) p
    (projectiveCoordinateToQuotient (K := K) p (projectiveCoordinateFraction (K := K) p d F hF')) =
      projectiveCoordinateFraction (K := K) p d F hF'
  rw [projectiveCoordinateToQuotient_fraction, projectiveQuotientToCoordinate_mk,
    projectiveCoordinate_eval₂_homogeneous]

/-- The actual standard chart ring is the quotient by `X_p = 1`. -/
def projectiveCoordinateQuotientRingEquiv (p : σ) :
    Away (homogeneousSubmodule σ K) (X p) ≃+* ProjectiveCoordinateQuotient (K := K) p :=
  RingEquiv.ofHomInv (projectiveCoordinateToQuotient (K := K) p) (projectiveQuotientToCoordinate (K := K) p)
    (projectiveQuotientToCoordinate_comp_projectiveCoordinateToQuotient (K := K) p)
    (projectiveCoordinateToQuotient_comp_projectiveQuotientToCoordinate (K := K) p)

@[simp] theorem projectiveCoordinateQuotientRingEquiv_fraction (p : σ) (d : ℕ)
    (F : MvPolynomial σ K) (hF : F.IsHomogeneous d) :
    projectiveCoordinateQuotientRingEquiv p (projectiveCoordinateFraction (K := K) p d F hF) =
      Ideal.Quotient.mk (projectiveCoordinateIdeal (K := K) p) F :=
  projectiveCoordinateToQuotient_fraction p d F hF

/-- The fraction used by the projective basic-open localization API maps
to the numerator class itself when the pivot has degree one. -/
@[simp] theorem projectiveCoordinateQuotientRingEquiv_isLocalizationElem (p : σ)
    (d : ℕ) (F : MvPolynomial σ K) (hF : F.IsHomogeneous d) :
    projectiveCoordinateQuotientRingEquiv (K := K) p
        (Away.isLocalizationElem (isHomogeneous_X K p) hF) =
      Ideal.Quotient.mk (projectiveCoordinateIdeal (K := K) p) F := by
  simpa only [Away.isLocalizationElem, pow_one, projectiveCoordinateFraction] using
    projectiveCoordinateQuotientRingEquiv_fraction p d F hF

/-- The coefficient algebra is explicitly the degree-zero constant map. -/
def projectiveCoordinateAlgebra (p : σ) :
    Algebra K (Away (homogeneousSubmodule σ K) (X p)) :=
  (projectiveCoordinateConstants (K := K) p).toAlgebra

/-- The chart comparison respects the actual structural ground-field action. -/
def projectiveCoordinateQuotientAlgEquiv (p : σ) :
    letI := projectiveCoordinateAlgebra (K := K) p
    Away (homogeneousSubmodule σ K) (X p) ≃ₐ[K] ProjectiveCoordinateQuotient (K := K) p := by
  letI := projectiveCoordinateAlgebra (K := K) p
  refine AlgEquiv.ofRingEquiv (f := projectiveCoordinateQuotientRingEquiv p) ?_
  intro c
  exact projectiveCoordinateToQuotient_constants p c

open AlgebraicGeometry CategoryTheory

/-- The actual projective standard open is the spectrum of the literal
pivot quotient. This uses the projective scheme's standard chart isomorphism. -/
def projectiveCoordinateQuotientBasicOpenIso (p : σ) :
    (Proj.basicOpen (homogeneousSubmodule σ K) (X p)).toScheme ≅
      Spec (CommRingCat.of (ProjectiveCoordinateQuotient (K := K) p)) :=
  Proj.basicOpenIsoSpec (homogeneousSubmodule σ K) (X p)
      (isHomogeneous_X K p) (by decide) ≪≫
    Scheme.Spec.mapIso (projectiveCoordinateQuotientRingEquiv (K := K) p).symm.toCommRingCatIso.op

/-- The actual affine chart morphism from the pivot quotient into projective
space. Its coordinate map is precisely the preceding ring equivalence. -/
def projectiveCoordinateQuotientChartMap (p : σ) :
    Spec (CommRingCat.of (ProjectiveCoordinateQuotient (K := K) p)) ⟶
      Proj (homogeneousSubmodule σ K) :=
  (Scheme.Spec.mapIso (projectiveCoordinateQuotientRingEquiv (K := K) p).symm.toCommRingCatIso.op).inv ≫
    Proj.awayι (homogeneousSubmodule σ K) (X p) (isHomogeneous_X K p) (by decide)

instance projectiveCoordinateQuotientChartMap_isOpenImmersion (p : σ) :
    IsOpenImmersion (projectiveCoordinateQuotientChartMap (K := K) p) := by
  unfold projectiveCoordinateQuotientChartMap
  infer_instance

/-- The chart map is the expected map induced by homogeneous-fraction
evaluation followed by the canonical projective chart immersion. -/
theorem projectiveCoordinateQuotientChartMap_eq (p : σ) :
    projectiveCoordinateQuotientChartMap (K := K) p =
      Spec.map (CommRingCat.ofHom (projectiveCoordinateQuotientRingEquiv (K := K) p).toRingHom) ≫
        Proj.awayι (homogeneousSubmodule σ K) (X p) (isHomogeneous_X K p) (by decide) := rfl

section Structure

variable {ι : Type}

/-- The canonical coefficient-field structure on the ambient projective scheme. -/
def projectiveCoordinateStructure :
    Proj (homogeneousSubmodule ι K) ⟶ Spec (CommRingCat.of K) :=
  Proj.toSpecZero (homogeneousSubmodule ι K) ≫
    Spec.map (CommRingCat.ofHom (algebraMap K (homogeneousSubmodule ι K 0)))

/-- The actual projective chart morphism is over the coefficient field:
the structural pullback of a scalar is its literal quotient coefficient. -/
theorem projectiveCoordinateQuotientChartMap_comp_structure (p : ι) :
    projectiveCoordinateQuotientChartMap (K := K) p ≫
        projectiveCoordinateStructure (K := K) (ι := ι) =
      Spec.map (CommRingCat.ofHom
        (algebraMap K (ProjectiveCoordinateQuotient (K := K) p))) := by
  rw [projectiveCoordinateQuotientChartMap_eq, projectiveCoordinateStructure,
    Category.assoc, ← Category.assoc (Proj.awayι _ _ _ _),
    Proj.awayι_toSpecZero, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  exact projectiveCoordinateToQuotient_constants p c

end Structure

end EvenQuinticConic
