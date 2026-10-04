import EvenQuinticConic.QuadraticSections
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Finite-dimensionality derived from actual quadratic surjectivity

The actual quadratic restriction map lands in the span of its six specified
paired sections. Its surjectivity therefore makes the target space of actual
global sections finite-dimensional. A nonzero theta section then gives an
injective linear map into this target by pairing with that section. Injectivity
is proved from the actual generic-coefficient product formula and local
perfectness; it is not an additional hypothesis.

Consequently finite-dimensional theta sections need not be separately assumed
in the conditional ineffectivity theorem. No properness or coherent-cohomology
theorem is postulated here.
-/

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace MvPolynomial
open scoped EvenQuinticConic.SchemeScalars

universe u

namespace EvenQuinticConic

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (CommRingCat.of K))]

/-- The six actual quadratic products define a linear map from `K^6` to the
actual module of global sections of the square sheaf. -/
noncomputable def sixQuadraticSectionsMap
    {H T : X.Modules} (ν : ModuleSheafPairing H H T)
    (e : Fin 3 → H.val.obj (op ⊤)) :
    (Fin 6 → K) →ₗ[K] T.val.obj (op ⊤) where
  toFun c := c 0 • ν.app ⊤ (e 0) (e 0) +
    c 1 • ν.app ⊤ (e 1) (e 1) + c 2 • ν.app ⊤ (e 2) (e 2) +
    c 3 • ν.app ⊤ (e 0) (e 1) + c 4 • ν.app ⊤ (e 0) (e 2) +
    c 5 • ν.app ⊤ (e 1) (e 2)
  map_add' c d := by
    simp only [Pi.add_apply, add_smul]
    abel
  map_smul' c d := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, smul_add, RingHom.id_apply]

omit [IsIntegral X] in
/-- Surjectivity of actual quadratic restriction implies surjectivity of the
six-generator map. The coefficients come from the homogeneous polynomial lift. -/
theorem sixQuadraticSectionsMap_surjective
    {H T : X.Modules} (ν : ModuleSheafPairing H H T)
    (e : Fin 3 → H.val.obj (op ⊤))
    (h2 : Function.Surjective (quadraticSectionMap (K := K) ν e)) :
    Function.Surjective (sixQuadraticSectionsMap (K := K) ν e) := by
  intro s
  obtain ⟨A, hA⟩ := h2 s
  refine ⟨![A.val.coeff (Finsupp.single 0 2),
    A.val.coeff (Finsupp.single 1 2), A.val.coeff (Finsupp.single 2 2),
    A.val.coeff (Finsupp.single 0 1 + Finsupp.single 1 1),
    A.val.coeff (Finsupp.single 0 1 + Finsupp.single 2 1),
    A.val.coeff (Finsupp.single 1 1 + Finsupp.single 2 1)], ?_⟩
  exact hA

omit [IsIntegral X] in
/-- The target of actual quadratic restriction is finite-dimensional when
that restriction is surjective. -/
theorem square_global_finiteDimensional_of_quadratic_surjective
    {H T : X.Modules} (ν : ModuleSheafPairing H H T)
    (e : Fin 3 → H.val.obj (op ⊤))
    (h2 : Function.Surjective (quadraticSectionMap (K := K) ν e)) :
    FiniteDimensional K (T.val.obj (op ⊤)) :=
  FiniteDimensional.of_surjective (sixQuadraticSectionsMap (K := K) ν e)
    (sixQuadraticSectionsMap_surjective ν e h2)

local instance : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩

/-- Pairing with a nonzero actual global section is injective when the sheaf
is locally framed and the pairing is tensor-perfect on one nonempty framed
open. This follows by cancellation in the actual function field. -/
theorem pairing_with_nonzero_global_section_injective
    {Θ T : X.Modules} (μ : ModuleSheafPairing Θ Θ T)
    {ι : Type*} (U : ι → X.Opens) [∀ i, Nonempty (U i)]
    (hcover : iSup U = ⊤) (θframes : ∀ i, ModuleSheafFrame Θ (U i))
    (i₀ : ι) (tframe : ModuleSheafFrame T (U i₀))
    (hμ : Function.Bijective (TensorProduct.lift (μ.app (U i₀))))
    (s : Θ.val.obj (op ⊤)) (hs : s ≠ 0) :
    Function.Injective (μ.app ⊤ s) := by
  let g := moduleGlobalGenericLinearMap Θ (U i₀) (θframes i₀)
  have hg : Function.Injective g :=
    moduleGlobalGenericLinearMap_injective Θ U hcover θframes (U i₀) (θframes i₀)
  have hsgen : g s ≠ 0 := by
    intro h
    exact hs (hg (h.trans g.map_zero.symm))
  have hc := modulePairingCoefficient_generic_ne_zero μ (U i₀) (θframes i₀) tframe hμ
  intro a b hab
  have heq := congrArg (moduleGlobalGenericLinearMap T (U i₀) tframe) hab
  rw [moduleGlobalGenericLinearMap_pairing μ, moduleGlobalGenericLinearMap_pairing μ] at heq
  apply hg
  exact mul_left_cancel₀ (mul_ne_zero hc hsgen) heq

/-- Finite-dimensionality of the actual theta section space is derived from
quadratic surjectivity and the actual locally perfect pairing. It is not an
extra assumption. Neither algebraic closure nor normality is needed here. -/
theorem theta_global_finiteDimensional_of_quadratic_surjective
    (Θ H T : X.Modules) (μ : ModuleSheafPairing Θ Θ T)
    (ν : ModuleSheafPairing H H T)
    {ι : Type*} (U : ι → X.Opens) [∀ i, Nonempty (U i)]
    (hcover : iSup U = ⊤) (θframes : ∀ i, ModuleSheafFrame Θ (U i))
    (i₀ : ι) (tframe : ModuleSheafFrame T (U i₀))
    (hμ : Function.Bijective (TensorProduct.lift (μ.app (U i₀))))
    (e : Fin 3 → H.val.obj (op ⊤))
    (h2 : Function.Surjective (quadraticSectionMap (K := K) ν e)) :
    FiniteDimensional K (Θ.val.obj (op ⊤)) := by
  letI : FiniteDimensional K (T.val.obj (op ⊤)) :=
    square_global_finiteDimensional_of_quadratic_surjective ν e h2
  by_cases hz : ∀ s : Θ.val.obj (op ⊤), s = 0
  · letI : Subsingleton (Θ.val.obj (op ⊤)) := ⟨fun s t ↦ (hz s).trans (hz t).symm⟩
    infer_instance
  · push_neg at hz
    obtain ⟨s, hs⟩ := hz
    let f : Θ.val.obj (op ⊤) →ₗ[K] T.val.obj (op ⊤) :=
      (μ.app ⊤ s).restrictScalars K
    exact FiniteDimensional.of_injective f
      (pairing_with_nonzero_global_section_injective μ U hcover θframes i₀ tframe hμ s hs)

end EvenQuinticConic
