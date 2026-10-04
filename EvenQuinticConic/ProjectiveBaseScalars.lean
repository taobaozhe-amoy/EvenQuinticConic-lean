import EvenQuinticConic.ProjectiveGenericChart
import EvenQuinticConic.SchemeScalarAction
import EvenQuinticConic.PlaneCurveScheme

/-!
# Base scalars in genuine projective chart maps

This file compares homogeneous localization constants with pullback along
the actual structure morphism, so the resulting function-field coordinates
use the scheme's canonical base-field action.
-/

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open HomogeneousLocalization

universe u

namespace EvenQuinticConic

section General

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
  (f : A) {d : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d)

include hf hd in
/-- On a positive-degree affine chart, constants from degree zero are the
restrictions of the global constants induced by the actual structure map. -/
theorem projectiveChart_degreeZero_constants :
    CommRingCat.ofHom (fromZeroRingHom 𝒜 (Submonoid.powers f)) ≫
        Proj.awayToSection 𝒜 f =
      (Scheme.ΓSpecIso (CommRingCat.of (𝒜 0))).inv ≫
        (Proj.toSpecZero 𝒜).appTop ≫
        (Proj 𝒜).presheaf.map (homOfLE (show Proj.basicOpen 𝒜 f ≤ ⊤ from le_top)).op := by
  have h : (Proj.basicOpen 𝒜 f).ι ≫ Proj.toSpecZero 𝒜 =
      (Proj.basicOpenIsoSpec 𝒜 f hf hd).hom ≫
        Spec.map (CommRingCat.ofHom (fromZeroRingHom 𝒜 (Submonoid.powers f))) := by
    apply (cancel_epi (Proj.basicOpenIsoSpec 𝒜 f hf hd).inv).mp
    simpa only [← Category.assoc, Proj.basicOpenIsoSpec_inv_ι,
      Iso.inv_hom_id, Category.id_comp] using Proj.awayι_toSpecZero 𝒜 f hf hd
  have hh := congrArg (fun g => g.appTop) h
  simp only [Scheme.comp_appTop,
    Proj.basicOpenIsoSpec_hom, Proj.basicOpenToSpec_app_top] at hh
  apply (cancel_mono (Proj.basicOpen 𝒜 f).topIso.inv).mp
  calc
    _ = (Scheme.ΓSpecIso (CommRingCat.of (𝒜 0))).inv ≫
        (Spec.map (CommRingCat.ofHom (fromZeroRingHom 𝒜 (Submonoid.powers f)))).appTop ≫
        (Scheme.ΓSpecIso _).hom ≫ Proj.awayToSection 𝒜 f ≫
        (Proj.basicOpen 𝒜 f).topIso.inv := by simp
    _ = (Scheme.ΓSpecIso (CommRingCat.of (𝒜 0))).inv ≫
        (Proj.toSpecZero 𝒜).appTop ≫ (Proj.basicOpen 𝒜 f).ι.appTop := by rw [hh]
    _ = _ := by
      simp only [Scheme.Opens.ι_appTop, Scheme.Opens.topIso_inv,
        Category.assoc, ← Functor.map_comp]
      rfl

/-- The top open of an integral scheme is nonempty. -/
local instance {X : Scheme.{u}} [IsIntegral X] : Nonempty (⊤ : X.Opens) :=
  ⟨⟨genericPoint X, trivial⟩⟩

include hf hd in
/-- The chart map sends degree-zero constants to their actual generic value
under the composite structure morphism. -/
theorem projectiveChartToFunctionField_fromZero
    {X : Scheme.{u}} [IsIntegral X] (p : X ⟶ Proj 𝒜)
    [Nonempty (p ⁻¹ᵁ Proj.basicOpen 𝒜 f)] (a : 𝒜 0) :
    projectiveChartToFunctionField 𝒜 p f
        (fromZeroRingHom 𝒜 (Submonoid.powers f) a) =
      X.germToFunctionField ⊤
        ((p ≫ Proj.toSpecZero 𝒜).appTop
          ((Scheme.ΓSpecIso (CommRingCat.of (𝒜 0))).inv a)) := by
  letI : Nonempty ((Opens.map p.base).obj ⊤) := ⟨⟨genericPoint X, trivial⟩⟩
  have hc := congrArg
    (fun k : CommRingCat.of (𝒜 0) ⟶ Γ(Proj 𝒜, Proj.basicOpen 𝒜 f) => k a)
    (projectiveChart_degreeZero_constants 𝒜 f hf hd)
  change (Proj.awayToSection 𝒜 f) (fromZeroRingHom 𝒜 (Submonoid.powers f) a) =
    (Proj 𝒜).presheaf.map (homOfLE (show Proj.basicOpen 𝒜 f ≤ ⊤ from le_top)).op
      ((Proj.toSpecZero 𝒜).appTop ((Scheme.ΓSpecIso (CommRingCat.of (𝒜 0))).inv a)) at hc
  change X.germToFunctionField _ ((p.app _) ((Proj.awayToSection 𝒜 f)
    (fromZeroRingHom 𝒜 (Submonoid.powers f) a))) = _
  rw [hc]
  have hn := congrArg (fun k => k
      ((Proj.toSpecZero 𝒜).appTop ((Scheme.ΓSpecIso (CommRingCat.of (𝒜 0))).inv a)))
    (p.naturality (homOfLE (show Proj.basicOpen 𝒜 f ≤ ⊤ from le_top)).op)
  dsimp only at hn
  simp only [CommRingCat.comp_apply] at hn
  rw [hn, generic_germ_restrict, Scheme.comp_appTop]
  rfl

end General

section Plane

open MvPolynomial
open scoped SchemeScalars

variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

local instance {X : Scheme.{u}} [IsIntegral X] : Nonempty (⊤ : X.Opens) :=
  ⟨⟨genericPoint X, trivial⟩⟩

/-- Constants in normalized plane coordinates come from the actual
composite morphism to `Spec K`. -/
theorem planeChartToFunctionField_constants
    {X : Scheme.{u}} [IsIntegral X] (p : X ⟶ ProjectivePlaneScheme K)
    (j : Fin 3) [Nonempty (p ⁻¹ᵁ Proj.basicOpen
      (homogeneousSubmodule (Fin 3) K) (MvPolynomial.X j))] (c : K) :
    projectiveChartToFunctionField (homogeneousSubmodule (Fin 3) K) p
        (MvPolynomial.X j) (planeChartConstants j c) =
      X.germToFunctionField ⊤
        (schemeBaseScalarHom (p ≫ projectivePlaneStructure K) c) := by
  rw [planeChartConstants, RingHom.comp_apply,
    projectiveChartToFunctionField_fromZero
      (homogeneousSubmodule (Fin 3) K) (MvPolynomial.X j)
      (isHomogeneous_X K j) (by decide)]
  congr 1
  have hn := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom
    (algebraMap K (homogeneousSubmodule (Fin 3) K 0)))
  have he := congrArg (fun k => k c) hn
  change (Scheme.ΓSpecIso (CommRingCat.of (homogeneousSubmodule (Fin 3) K 0))).inv
      (algebraMap K (homogeneousSubmodule (Fin 3) K 0) c) =
    (Spec.map (CommRingCat.ofHom (algebraMap K (homogeneousSubmodule (Fin 3) K 0)))).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of K)).inv c) at he
  change (p ≫ Proj.toSpecZero _).appTop _ =
    (p ≫ projectivePlaneStructure K).appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv c)
  rw [he, projectivePlaneStructure, ← Category.assoc, Scheme.comp_appTop]
  rfl

/-- For a genuine morphism of `K`-schemes into projective space, the chart
coefficient map equals the canonical scalar map on the actual function field. -/
theorem planeChartToFunctionField_constants_eq_algebraMap
    {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
    (p : X ⟶ ProjectivePlaneScheme K) [p.IsOver (Spec (CommRingCat.of K))]
    (j : Fin 3) [Nonempty (p ⁻¹ᵁ Proj.basicOpen
      (homogeneousSubmodule (Fin 3) K) (MvPolynomial.X j))] :
    (projectiveChartToFunctionField (homogeneousSubmodule (Fin 3) K) p
      (MvPolynomial.X j)).comp (planeChartConstants j) =
        algebraMap K X.functionField := by
  ext c
  change projectiveChartToFunctionField _ p _ (planeChartConstants j c) = _
  rw [planeChartToFunctionField_constants]
  have hp : p ≫ projectivePlaneStructure K = X ↘ Spec (CommRingCat.of K) :=
    (Scheme.Hom.isOver_iff (Spec (CommRingCat.of K))).mp inferInstance
  rw [hp]
  rfl

end Plane

end EvenQuinticConic
