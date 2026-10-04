import EvenQuinticConic.PlaneQuintic
import EvenQuinticConic.GenericPointInjection
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-!
# Actual projective chart maps into actual function fields

All maps here are built from `Proj.awayToSection`, actual scheme pullback,
and the generic stalk map of an integral scheme. The affine cone's fraction
field is never identified with the projective curve's function field.
-/

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open HomogeneousLocalization

universe u

namespace EvenQuinticConic

section GeneralCharts

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
  {X : Scheme.{u}} (p : X ⟶ Proj 𝒜)

/-- Pullback of the actual projective chart's ring of homogeneous fractions. -/
noncomputable def projectiveChartPullback (f : A) :
    Away 𝒜 f →+* Γ(X, p ⁻¹ᵁ Proj.basicOpen 𝒜 f) :=
  (p.app (Proj.basicOpen 𝒜 f)).hom.comp (Proj.awayToSection 𝒜 f).hom

variable [IsIntegral X]

/-- The actual map from homogeneous chart fractions to the actual function
field, for any scheme morphism to projective spectrum. -/
noncomputable def projectiveChartToFunctionField (f : A)
    [Nonempty (p ⁻¹ᵁ Proj.basicOpen 𝒜 f)] :
    Away 𝒜 f →+* X.functionField :=
  (X.germToFunctionField (p ⁻¹ᵁ Proj.basicOpen 𝒜 f)).hom.comp
    (projectiveChartPullback 𝒜 p f)

/-- Generic vanishing of a pulled-back fraction is equivalent to its actual
vanishing as a section on the nonempty chart. -/
theorem projectiveChartToFunctionField_eq_zero_iff (f : A)
    [Nonempty (p ⁻¹ᵁ Proj.basicOpen 𝒜 f)] (z : Away 𝒜 f) :
    projectiveChartToFunctionField 𝒜 p f z = 0 ↔
      projectiveChartPullback 𝒜 p f z = 0 := by
  exact (X.germToFunctionField_injective (p ⁻¹ᵁ Proj.basicOpen 𝒜 f)).eq_iff'
    (map_zero _)

end GeneralCharts

section PlaneCharts

open MvPolynomial

variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Constant polynomials as degree-zero homogeneous chart fractions. -/
noncomputable def planeChartConstants (j : Fin 3) :
    K →+* Away (homogeneousSubmodule (Fin 3) K) (X j) :=
  (HomogeneousLocalization.fromZeroRingHom (homogeneousSubmodule (Fin 3) K)
    (Submonoid.powers (X j))).comp (algebraMap K (homogeneousSubmodule (Fin 3) K 0))

/-- The genuine homogeneous-localization element `X_i / X_j`. -/
noncomputable def planeChartRatio (j i : Fin 3) :
    Away (homogeneousSubmodule (Fin 3) K) (X j) :=
  Away.mk (homogeneousSubmodule (Fin 3) K) (isHomogeneous_X K j) 1 (X i)
    (by simpa using isHomogeneous_X K i)

/-- A homogeneous polynomial as the actual chart fraction `P / X_j^d`. -/
noncomputable def planeHomogeneousChartFraction (j : Fin 3) (d : ℕ)
    (P : PlanePolynomial K) (hP : P.IsHomogeneous d) :
    Away (homogeneousSubmodule (Fin 3) K) (X j) :=
  Away.mk (homogeneousSubmodule (Fin 3) K) (isHomogeneous_X K j) d P
    (by simpa using hP)

/-- Polynomial evaluation of normalized homogeneous coordinates is the
actual homogeneous-localization fraction `P / X_j^d`. -/
theorem planeChart_eval₂_homogeneous (j : Fin 3) (d : ℕ)
    (P : PlanePolynomial K) (hP : P.IsHomogeneous d) :
    eval₂ (planeChartConstants j) (planeChartRatio j) P =
      planeHomogeneousChartFraction j d P hP := by
  let S := PlanePolynomial K
  let L := Localization.Away (X j : S)
  let q : Away (homogeneousSubmodule (Fin 3) K) (X j) →+* L := algebraMap _ _
  let z : Submonoid.powers (X j : S) := ⟨X j, Submonoid.mem_powers _⟩
  let t : L := Localization.mk 1 z
  have hc : q.comp (planeChartConstants j) = (algebraMap S L).comp C := by
    ext c
    change Localization.mk (C c) (1 : Submonoid.powers (X j : S)) =
      algebraMap S L (C c)
    rfl
  have hx : (q ∘ planeChartRatio j) = fun i ↦ algebraMap S L (X i) * t := by
    funext i
    change (planeChartRatio j i).val =
      Localization.mk (X i) (1 : Submonoid.powers (X j : S)) * Localization.mk 1 z
    simp only [planeChartRatio, Away.val_mk, pow_one]
    rw [Localization.mk_mul, mul_one, one_mul]
  have heval : eval₂ ((algebraMap S L).comp C) (fun i ↦ algebraMap S L (X i)) P =
      algebraMap S L P := by
    calc
      _ = (algebraMap S L) (eval₂ C MvPolynomial.X P) :=
        (eval₂_comp_left (algebraMap S L) C MvPolynomial.X P).symm
      _ = _ := congrArg (algebraMap S L) (MvPolynomial.eval₂_eta P)
  apply HomogeneousLocalization.val_injective (Submonoid.powers (X j : S))
  change q (eval₂ (planeChartConstants j) (planeChartRatio j) P) = _
  rw [eval₂_comp_left, hc, hx, homogeneous_eval₂_scale _ _ t P d hP, heval]
  change Localization.mk P (1 : Submonoid.powers (X j : S)) *
    (Localization.mk 1 z) ^ d = Localization.mk P (z ^ d)
  rw [Localization.mk_pow, one_pow, Localization.mk_mul, mul_one, one_mul]

/-- The normalization formula remains valid after any actual chart-ring map,
in particular the pullback to a curve's actual function field. -/
theorem planeChart_map_eval₂_homogeneous {L : Type*} [CommRing L]
    (j : Fin 3) (d : ℕ) (P : PlanePolynomial K) (hP : P.IsHomogeneous d)
    (q : Away (homogeneousSubmodule (Fin 3) K) (X j) →+* L) :
    eval₂ (q.comp (planeChartConstants j)) (fun i ↦ q (planeChartRatio j i)) P =
      q (planeHomogeneousChartFraction j d P hP) := by
  calc
    _ = q (eval₂ (planeChartConstants j) (planeChartRatio j) P) :=
      (eval₂_comp_left q (planeChartConstants j) (planeChartRatio j) P).symm
    _ = _ := congrArg q (planeChart_eval₂_homogeneous j d P hP)

end PlaneCharts

end EvenQuinticConic
