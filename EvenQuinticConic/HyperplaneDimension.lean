import EvenQuinticConic.QuadraticSections
import EvenQuinticConic.GlobalSectionDimension
import Mathlib.LinearAlgebra.Basis.Basic

/-!
# The hyperplane section space is three-dimensional from restriction data

The three actual coordinate sections are independent by injectivity of
homogeneous quartic restriction. Surjectivity of the actual quadratic
restriction map then forces them to span all global hyperplane sections.
No finite-dimensionality, properness, or independent dimension hypothesis
is assumed. Normality is not needed for this argument.
-/

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open MvPolynomial
open scoped EvenQuinticConic.SchemeScalars

universe u

namespace EvenQuinticConic

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (CommRingCat.of K))]

/-- Quartic restriction injectivity forces the three actual coordinate
sections to be linearly independent: raise a putative linear relation to
its fourth power. -/
theorem coordinate_sections_linearIndependent_of_quartic_injective
    (H : X.Modules) (V : X.Opens) [Nonempty V]
    (frame : ModuleSheafFrame H V) (e : Fin 3 → H.val.obj (op ⊤))
    (h4 : ∀ P : MvPolynomial (Fin 3) K, P.IsHomogeneous 4 →
      aeval (fun i ↦ schemeGenericLinearMap (K := K) H V frame (e i)) P = 0 →
      P = 0) :
    LinearIndependent K e := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  let P : MvPolynomial (Fin 3) K := ∑ j : Fin 3, C (c j) * MvPolynomial.X j
  have hP : P.IsHomogeneous 1 := by
    exact IsHomogeneous.sum Finset.univ _ 1 (fun j _ ↦ isHomogeneous_C_mul_X (c j) j)
  have heval : aeval (fun j ↦ schemeGenericLinearMap (K := K) H V frame (e j)) P = 0 := by
    simpa [P, Algebra.smul_def] using
      congrArg (schemeGenericLinearMap (K := K) H V frame) hc
  have hP4 : P ^ 4 = 0 := h4 (P ^ 4) (by simpa using hP.pow 4) (by simp [heval])
  have hP0 : P = 0 := pow_eq_zero hP4
  have hcoeff := congrArg (MvPolynomial.coeff (Finsupp.single i 1)) hP0
  fin_cases i <;>
    simpa [P, Fin.sum_univ_three, coeff_X', Finsupp.single_eq_single_iff] using hcoeff

/-- Proportional actual paired squares give proportional genuine global
sections over an algebraically closed base field. The common local pairing
coefficient is computed and cancelled, and generic injectivity supplies
the equality of global sections. -/
theorem exists_scalar_multiple_of_actual_pairing_square [IsAlgClosed K]
    (H T : X.Modules) (ν : ModuleSheafPairing H H T)
    {ι : Type*} (U : ι → X.Opens) [∀ i, Nonempty (U i)]
    (hcover : iSup U = ⊤) (frames : ∀ i, ModuleSheafFrame H (U i))
    (V : X.Opens) [Nonempty V] (hframe : ModuleSheafFrame H V)
    (tframe : ModuleSheafFrame T V)
    (hν : Function.Bijective (TensorProduct.lift (ν.app V)))
    (s a : H.val.obj (op ⊤)) (c : K)
    (hsquare : ν.app ⊤ s s = c • ν.app ⊤ a a) :
    ∃ d : K, s = d • a := by
  let g := schemeGenericLinearMap (K := K) H V hframe
  let v := X.germToFunctionField V (modulePairingCoefficient ν V hframe tframe)
  have hv : v ≠ 0 := modulePairingCoefficient_generic_ne_zero ν V hframe tframe hν
  have hg := congrArg (schemeGenericLinearMap (K := K) T V tframe) hsquare
  rw [map_smul] at hg
  have hpair (x y : H.val.obj (op ⊤)) :=
    moduleGlobalGenericLinearMap_pairing ν V hframe tframe x y
  change ∀ x y : H.val.obj (op ⊤),
    schemeGenericLinearMap (K := K) T V tframe (ν.app ⊤ x y) = v * g x * g y at hpair
  rw [hpair, hpair] at hg
  change v * g s * g s = algebraMap K X.functionField c * (v * g a * g a) at hg
  have hrel : g s ^ 2 = algebraMap K X.functionField c * g a ^ 2 := by
    apply mul_left_cancel₀ hv
    calc
      v * g s ^ 2 = v * g s * g s := by ring
      _ = algebraMap K X.functionField c * (v * g a * g a) := hg
      _ = v * (algebraMap K X.functionField c * g a ^ 2) := by ring
  obtain ⟨d, hd⟩ := exists_scalar_multiple_of_sq_eq_scalar_sq (g s) (g a) c hrel
  refine ⟨d, ?_⟩
  apply schemeGenericLinearMap_injective (K := K) H U hcover frames V hframe
  simpa only [map_smul, Algebra.smul_def] using hd

/-- The three genuine coordinate sections span all global hyperplane
sections. Quadratic surjectivity supplies lifts for the three products of
any hypothetical fourth independent direction with one coordinate. -/
theorem coordinate_sections_span_of_quadratic_surjective [IsAlgClosed K]
    (H T : X.Modules) (ν : ModuleSheafPairing H H T)
    {ι : Type*} (U : ι → X.Opens) [∀ i, Nonempty (U i)]
    (hcover : iSup U = ⊤)
    (hframes : ∀ i, ModuleSheafFrame H (U i))
    (tframes : ∀ i, ModuleSheafFrame T (U i))
    (V : X.Opens) [Nonempty V] (hframe : ModuleSheafFrame H V)
    (tframe : ModuleSheafFrame T V)
    (hν : Function.Bijective (TensorProduct.lift (ν.app V)))
    (e : Fin 3 → H.val.obj (op ⊤))
    (h2 : Function.Surjective (quadraticSectionMap (K := K) ν e))
    (h4 : ∀ P : MvPolynomial (Fin 3) K, P.IsHomogeneous 4 →
      aeval (fun i ↦ schemeGenericLinearMap (K := K) H V hframe (e i)) P = 0 →
      P = 0) :
    Submodule.span K (Set.range e) = ⊤ := by
  classical
  have he := coordinate_sections_linearIndependent_of_quartic_injective H V hframe e h4
  have he0 : e 0 ≠ 0 := he.ne_zero 0
  apply top_unique
  intro s _
  by_contra hs
  have hse : LinearIndependent K ![s, e 0] := by
    apply linearIndependent_fin2.mpr
    refine ⟨he0, ?_⟩
    intro d hd
    change d • e 0 = s at hd
    apply hs
    rw [← hd]
    exact (Submodule.span K (Set.range e)).smul_mem d (Submodule.subset_span ⟨0, rfl⟩)
  obtain ⟨A, hA, hAs⟩ := exists_quadratic_lift_of_surjective ν e h2 (ν.app ⊤ s s)
  obtain ⟨B, hB, hBse⟩ := exists_quadratic_lift_of_surjective ν e h2 (ν.app ⊤ s (e 0))
  obtain ⟨D, hD, hDe⟩ := exists_quadratic_lift_of_surjective ν e h2 (ν.app ⊤ (e 0) (e 0))
  have hAg : schemeGenericLinearMap (K := K) T V tframe (ν.app ⊤ s s) =
      quadraticGenericRestriction ν V hframe tframe e A := by
    rw [← hAs]
    exact genericCoefficient_quadraticPolynomialSection ν V hframe tframe e A hA
  have hBg : schemeGenericLinearMap (K := K) T V tframe (ν.app ⊤ s (e 0)) =
      quadraticGenericRestriction ν V hframe tframe e B := by
    rw [← hBse]
    exact genericCoefficient_quadraticPolynomialSection ν V hframe tframe e B hB
  have hDg : schemeGenericLinearMap (K := K) T V tframe (ν.app ⊤ (e 0) (e 0)) =
      quadraticGenericRestriction ν V hframe tframe e D := by
    rw [← hDe]
    exact genericCoefficient_quadraticPolynomialSection ν V hframe tframe e D hD
  obtain ⟨c, a, _, _, _, hsquare⟩ :=
    exists_linear_section_of_quadratic_lifts H H T ν ν U hcover hframes tframes
      V hframe hframe tframe hν hν e s (e 0) hse A B D hA hB hD h4 hAg hBg hDg
  obtain ⟨d, hd⟩ := exists_scalar_multiple_of_actual_pairing_square H T ν U hcover hframes
    V hframe tframe hν s (linearPolynomialSection H e a) c hsquare
  apply hs
  rw [hd]
  apply (Submodule.span K (Set.range e)).smul_mem
  apply Submodule.sum_mem
  intro j _
  exact (Submodule.span K (Set.range e)).smul_mem _ (Submodule.subset_span ⟨j, rfl⟩)

/-- The usual value `h⁰(H)=3` follows from the actual degree-two and degree-four
restriction data. It is no longer an additional geometric hypothesis. -/
theorem hyperplane_finrank_eq_three_of_quadratic_surjective [IsAlgClosed K]
    (H T : X.Modules) (ν : ModuleSheafPairing H H T)
    {ι : Type*} (U : ι → X.Opens) [∀ i, Nonempty (U i)]
    (hcover : iSup U = ⊤)
    (hframes : ∀ i, ModuleSheafFrame H (U i))
    (tframes : ∀ i, ModuleSheafFrame T (U i))
    (V : X.Opens) [Nonempty V] (hframe : ModuleSheafFrame H V)
    (tframe : ModuleSheafFrame T V)
    (hν : Function.Bijective (TensorProduct.lift (ν.app V)))
    (e : Fin 3 → H.val.obj (op ⊤))
    (h2 : Function.Surjective (quadraticSectionMap (K := K) ν e))
    (h4 : ∀ P : MvPolynomial (Fin 3) K, P.IsHomogeneous 4 →
      aeval (fun i ↦ schemeGenericLinearMap (K := K) H V hframe (e i)) P = 0 →
      P = 0) :
    Module.finrank K (H.val.obj (op ⊤)) = 3 := by
  let basis : Module.Basis (Fin 3) K (H.val.obj (op ⊤)) := Module.Basis.mk
    (coordinate_sections_linearIndependent_of_quartic_injective H V hframe e h4)
    (coordinate_sections_span_of_quadratic_surjective H T ν U hcover hframes tframes
      V hframe tframe hν e h2 h4).ge
  simpa using Module.finrank_eq_card_basis basis

end EvenQuinticConic
