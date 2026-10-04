import EvenQuinticConic.PlaneQuintic
import EvenQuinticConic.LineBundleGluing
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-!
# Actual coordinate-ratio sections on the projective plane

The coordinate ratio `Xⱼ/Xᵢ` is constructed in the degree-zero homogeneous
localization at `Xᵢ` and mapped by `Proj.awayToSection` to the actual structure
sheaf on the standard open `D₊(Xᵢ)`. No formal coordinate ring is substituted
for this ring of actual sections.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace MvPolynomial

namespace EvenQuinticConic

variable (K : Type*) [Field K]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual projective plane scheme defined by the standard polynomial grading. -/
abbrev PlaneProjectiveScheme : Scheme := Proj (homogeneousSubmodule (Fin 3) K)

/-- The actual standard open where the coordinate `Xᵢ` is nonzero. -/
def planeCoordinateOpen (i : Fin 3) : (PlaneProjectiveScheme K).Opens :=
  Proj.basicOpen (homogeneousSubmodule (Fin 3) K) (X i)

/-- The three actual standard coordinate opens cover the projective plane. -/
theorem planeCoordinateOpen_cover : (⨆ i : Fin 3, planeCoordinateOpen K i) = ⊤ := by
  apply Proj.iSup_basicOpen_eq_top'
  · intro i
    exact ⟨1, isHomogeneous_X K i⟩
  · apply top_unique
    intro P hPtop
    clear hPtop
    induction P using MvPolynomial.induction_on with
    | C a =>
      exact Subalgebra.algebraMap_mem _
        (⟨C a, isHomogeneous_C (Fin 3) a⟩ : homogeneousSubmodule (Fin 3) K 0)
    | add P Q hP hQ => exact add_mem hP hQ
    | mul_X P i hP => exact mul_mem hP (Algebra.subset_adjoin ⟨i, rfl⟩)

/-- Each standard coordinate open is genuinely affine. -/
theorem planeCoordinateOpen_isAffine (i : Fin 3) : IsAffineOpen (planeCoordinateOpen K i) :=
  Proj.isAffineOpen_basicOpen _ _ (isHomogeneous_X K i) (by decide : 0 < (1 : ℕ))

/-- `Xⱼ/Xᵢ` in the actual degree-zero localization at `Xᵢ`. -/
def planeCoordinateRatioAway (i j : Fin 3) :
    HomogeneousLocalization.Away (homogeneousSubmodule (Fin 3) K) (X i) :=
  HomogeneousLocalization.Away.mk _ (isHomogeneous_X K i) 1 (X j)
    (by simpa using isHomogeneous_X K j)

/-- The actual regular coordinate-ratio section on `D₊(Xᵢ)`. -/
def planeCoordinateRatio (i j : Fin 3) :
    Γ(PlaneProjectiveScheme K, planeCoordinateOpen K i) :=
  Proj.awayToSection (homogeneousSubmodule (Fin 3) K) (X i)
    (planeCoordinateRatioAway K i j)

/-- Evaluation of the actual coordinate-ratio section at a projective point,
viewed in the ordinary localization of the homogeneous coordinate ring. -/
theorem planeCoordinateRatio_val (i j : Fin 3)
    (p : planeCoordinateOpen K i) :
    ((planeCoordinateRatio K i j).val p).val =
      Localization.mk (X j : PlanePolynomial K)
        ⟨X i, (show X i ∈ p.val.asHomogeneousIdeal.toIdeal.primeCompl from p.property)⟩ := by
  change (HomogeneousLocalization.mapId (homogeneousSubmodule (Fin 3) K)
    (Submonoid.powers_le.mpr p.property) (planeCoordinateRatioAway K i j)).val = _
  simp only [planeCoordinateRatioAway, HomogeneousLocalization.Away.mk,
    HomogeneousLocalization.mapId, HomogeneousLocalization.map_mk,
    HomogeneousLocalization.val_mk, RingHom.id_apply, pow_one]

/-- The coordinate ratio with equal indices is the unit section. -/
@[simp]
theorem planeCoordinateRatio_self (i : Fin 3) :
    planeCoordinateRatio K i i = 1 := by
  apply Subtype.ext
  funext p
  apply HomogeneousLocalization.val_injective
  rw [planeCoordinateRatio_val]
  simp only [Proj.one_apply, HomogeneousLocalization.val_one]
  exact Localization.mk_self
    (⟨X i, p.property⟩ : p.val.asHomogeneousIdeal.toIdeal.primeCompl)

/-- Restriction of `Xⱼ/Xᵢ` to any open contained in `D₊(Xᵢ)`. -/
def planeCoordinateRatioOn (W : (PlaneProjectiveScheme K).Opens)
    (i j : Fin 3) (hi : W ≤ planeCoordinateOpen K i) :
    Γ(PlaneProjectiveScheme K, W) :=
  (PlaneProjectiveScheme K).presheaf.map (homOfLE hi).op (planeCoordinateRatio K i j)

/-- The restricted coordinate ratio has the same literal homogeneous fraction
in the localization at each projective point. -/
theorem planeCoordinateRatioOn_val (W : (PlaneProjectiveScheme K).Opens)
    (i j : Fin 3) (hi : W ≤ planeCoordinateOpen K i) (p : W) :
    ((planeCoordinateRatioOn K W i j hi).val p).val =
      Localization.mk (X j : PlanePolynomial K)
        ⟨X i, (show X i ∈ p.val.asHomogeneousIdeal.toIdeal.primeCompl from hi p.property)⟩ :=
  planeCoordinateRatio_val K i j ⟨p.val, hi p.property⟩

@[simp]
theorem planeCoordinateRatioOn_self (W : (PlaneProjectiveScheme K).Opens)
    (i : Fin 3) (hi : W ≤ planeCoordinateOpen K i) :
    planeCoordinateRatioOn K W i i hi = 1 := by
  simp only [planeCoordinateRatioOn, planeCoordinateRatio_self, map_one]

/-- Coordinate ratios satisfy the cocycle identity on every common subopen.
The proof is pointwise equality in the actual localizations, and also applies
to the empty open. -/
theorem planeCoordinateRatioOn_cocycle (W : (PlaneProjectiveScheme K).Opens)
    (i j k : Fin 3) (hi : W ≤ planeCoordinateOpen K i)
    (hj : W ≤ planeCoordinateOpen K j) :
    planeCoordinateRatioOn K W i j hi * planeCoordinateRatioOn K W j k hj =
      planeCoordinateRatioOn K W i k hi := by
  apply Subtype.ext
  funext p
  apply HomogeneousLocalization.val_injective
  have hmul := Proj.mul_apply (homogeneousSubmodule (Fin 3) K)
    (planeCoordinateRatioOn K W i j hi) (planeCoordinateRatioOn K W j k hj) p
  rw [hmul, HomogeneousLocalization.val_mul, planeCoordinateRatioOn_val,
    planeCoordinateRatioOn_val, planeCoordinateRatioOn_val, Localization.mk_mul]
  apply Localization.mk_eq_mk_iff.mpr
  rw [Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul, Submonoid.coe_mul]
  ring

/-- The transition unit on any common subopen. With local frames `Xᵢ`, the
convention is `coordinateᵢ = transitionᵢⱼ * coordinateⱼ`. -/
def planeCoordinateTransition (i j : Fin 3)
    (W : (PlaneProjectiveScheme K).Opens)
    (hi : W ≤ planeCoordinateOpen K i) (hj : W ≤ planeCoordinateOpen K j) :
    Γ(PlaneProjectiveScheme K, W)ˣ where
  val := planeCoordinateRatioOn K W i j hi
  inv := planeCoordinateRatioOn K W j i hj
  val_inv := (planeCoordinateRatioOn_cocycle K W i j i hi hj).trans
    (planeCoordinateRatioOn_self K W i hi)
  inv_val := (planeCoordinateRatioOn_cocycle K W j i j hj hi).trans
    (planeCoordinateRatioOn_self K W j hj)

/-- These actual transition units commute with actual structure-sheaf
restriction maps on all subopens. -/
theorem planeCoordinateTransition_restrict (i j : Fin 3)
    (W V : (PlaneProjectiveScheme K).Opens)
    (hi : W ≤ planeCoordinateOpen K i) (hj : W ≤ planeCoordinateOpen K j)
    (hVW : V ≤ W) :
    Units.map ((PlaneProjectiveScheme K).presheaf.map (homOfLE hVW).op).hom.toMonoidHom
      (planeCoordinateTransition K i j W hi hj) =
      planeCoordinateTransition K i j V (hVW.trans hi) (hVW.trans hj) := by
  apply Units.ext
  change (PlaneProjectiveScheme K).presheaf.map (homOfLE hVW).op
      ((PlaneProjectiveScheme K).presheaf.map (homOfLE hi).op (planeCoordinateRatio K i j)) =
    (PlaneProjectiveScheme K).presheaf.map (homOfLE (hVW.trans hi)).op
      (planeCoordinateRatio K i j)
  rw [← ConcreteCategory.comp_apply, ← (PlaneProjectiveScheme K).presheaf.map_comp]
  rfl

@[simp]
theorem planeCoordinateTransition_self (i : Fin 3)
    (W : (PlaneProjectiveScheme K).Opens) (hi : W ≤ planeCoordinateOpen K i) :
    planeCoordinateTransition K i i W hi hi = 1 := by
  apply Units.ext
  exact planeCoordinateRatioOn_self K W i hi

/-- The actual unit-valued cocycle identity for the coordinate transitions. -/
theorem planeCoordinateTransition_cocycle (i j k : Fin 3)
    (W : (PlaneProjectiveScheme K).Opens)
    (hi : W ≤ planeCoordinateOpen K i) (hj : W ≤ planeCoordinateOpen K j)
    (hk : W ≤ planeCoordinateOpen K k) :
    planeCoordinateTransition K i j W hi hj * planeCoordinateTransition K j k W hj hk =
      planeCoordinateTransition K i k W hi hk := by
  apply Units.ext
  exact planeCoordinateRatioOn_cocycle K W i j k hi hj

/-- The actual coordinate transitions bundled as rank-one gluing data.
The small-universe specialization matches the three-element chart index and
includes both `ℝ` and `ℂ`; the preceding unbundled lemmas are universe-general. -/
def planeCoordinateUnitTransition (k : Type) [Field k] :
    UnitTransition (PlaneProjectiveScheme k) (planeCoordinateOpen k) where
  transition := planeCoordinateTransition k
  restrict := planeCoordinateTransition_restrict k
  self := planeCoordinateTransition_self k
  cocycle := planeCoordinateTransition_cocycle k

end EvenQuinticConic
