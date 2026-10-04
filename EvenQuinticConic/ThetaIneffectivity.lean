import EvenQuinticConic.QuadraticSections
import EvenQuinticConic.GlobalSectionDimension
import EvenQuinticConic.ThetaFiniteDimension
import EvenQuinticConic.HyperplaneDimension

/-!
# A conditional theta ineffectivity theorem on actual module sheaves

This file completes the section-theoretic implication using actual sheaves,
actual global sections, actual bilinear pairings, and the base-field action
induced by the scheme structure morphism. The quadratic lifting hypothesis
is surjectivity of the explicitly constructed linear map `quadraticSectionMap`.

Geometric inputs are still explicit: a normal affine framed cover, locally
tensor-perfect square pairings, quadratic surjectivity, and quartic injectivity.
`PlaneThetaIneffectivity` constructs the hyperplane data and proves quartic
injectivity on the actual plane-quintic scheme. Quadratic surjectivity and
the required normal affine theta frames still need geometric proofs.

Finite-dimensionality is derived from actual quadratic surjectivity and the
pairing. This step is essential: `finrank = 0` alone does not mean that an
arbitrary vector space is zero. The strongest theorem also derives the
hyperplane dimension from the restriction maps; it does not assume it.
-/

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace MvPolynomial
open scoped EvenQuinticConic.SchemeScalars

universe u

namespace EvenQuinticConic

variable {K : Type u} [Field K] [IsAlgClosed K]
  {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
  (Θ H T : X.Modules)
  (μ : ModuleSheafPairing Θ Θ T) (ν : ModuleSheafPairing H H T)
  {ι : Type*} (U : ι → X.Opens) [∀ i, Nonempty (U i)]
  (hcover : iSup U = ⊤) (hU : ∀ i, IsAffineOpen (U i))
  [∀ i, IsIntegrallyClosed Γ(X, U i)]
  (θframes : ∀ i, ModuleSheafFrame Θ (U i))
  (hframes : ∀ i, ModuleSheafFrame H (U i))
  (tframes : ∀ i, ModuleSheafFrame T (U i))
  (hμ : ∀ i, Function.Bijective (TensorProduct.lift (μ.app (U i))))
  (hν : ∀ i, Function.Bijective (TensorProduct.lift (ν.app (U i))))
  (i₀ : ι) (e : Fin 3 → H.val.obj (op ⊤))
  (h2 : Function.Surjective (quadraticSectionMap (K := K) ν e))
  (h4 : ∀ P : MvPolynomial (Fin 3) K, P.IsHomogeneous 4 →
    aeval (fun j ↦ schemeGenericLinearMap (K := K) H (U i₀) (hframes i₀) (e j)) P = 0 →
    P = 0)

include hcover hU θframes tframes hμ hν h2 h4 in
/-- Two independent actual theta sections force an actual sheaf isomorphism
with the hyperplane sheaf, given the stated restriction and local hypotheses. -/
theorem theta_iso_hyperplane_of_independent_sections
    (s t : Θ.val.obj (op ⊤)) (hst : LinearIndependent K ![s, t]) :
    Nonempty (Θ ≅ H) := by
  obtain ⟨A, hA, hAs⟩ := exists_quadratic_lift_of_surjective ν e h2 (μ.app ⊤ s s)
  obtain ⟨B, hB, hBst⟩ := exists_quadratic_lift_of_surjective ν e h2 (μ.app ⊤ s t)
  obtain ⟨D, hD, hDt⟩ := exists_quadratic_lift_of_surjective ν e h2 (μ.app ⊤ t t)
  apply theta_iso_hyperplane_of_quadratic_lifts Θ H T μ ν U hcover hU
    θframes hframes tframes hμ hν i₀ e s t hst A B D hA hB hD h4
  · rw [← hAs]
    exact genericCoefficient_quadraticPolynomialSection ν (U i₀)
      (hframes i₀) (tframes i₀) e A hA
  · rw [← hBst]
    exact genericCoefficient_quadraticPolynomialSection ν (U i₀)
      (hframes i₀) (tframes i₀) e B hB
  · rw [← hDt]
    exact genericCoefficient_quadraticPolynomialSection ν (U i₀)
      (hframes i₀) (tframes i₀) e D hD

include hcover hU θframes tframes hμ hν h2 h4 in
/-- Dimension at least two gives the actual hyperplane-sheaf isomorphism. -/
theorem theta_iso_hyperplane_of_finrank_ge_two
    (hdim : 2 ≤ Module.finrank K (Θ.val.obj (op ⊤))) :
    Nonempty (Θ ≅ H) := by
  obtain ⟨s, t, hst⟩ := exists_independent_global_sections_of_finrank_ge_two Θ hdim
  exact theta_iso_hyperplane_of_independent_sections Θ H T μ ν U hcover hU
    θframes hframes tframes hμ hν i₀ e h2 h4 s t hst

include hcover hU θframes tframes hμ hν h2 h4 in
/-- Under the explicit geometric inputs, even finite rank must be zero when
the hyperplane section space has dimension three. This numerical statement
does not by itself assert that the section space is trivial. -/
theorem even_theta_global_finrank_eq_zero
    (hH : Module.finrank K (H.val.obj (op ⊤)) = 3)
    (heven : Even (Module.finrank K (Θ.val.obj (op ⊤)))) :
    Module.finrank K (Θ.val.obj (op ⊤)) = 0 := by
  by_contra hzero
  have hdim : 2 ≤ Module.finrank K (Θ.val.obj (op ⊤)) := by
    obtain ⟨n, hn⟩ := heven
    omega
  obtain ⟨iso⟩ := theta_iso_hyperplane_of_finrank_ge_two Θ H T μ ν U hcover hU
    θframes hframes tframes hμ hν i₀ e h2 h4 hdim
  have hthree : Module.finrank K (Θ.val.obj (op ⊤)) = 3 :=
    (schemeGlobalSections_finrank_eq (K := K) iso).trans hH
  obtain ⟨n, hn⟩ := heven
  omega

include hcover hU θframes tframes hμ hν h2 h4 in
/-- Conditional theta ineffectivity for actual sections. Finite-dimensionality
is proved from actual quadratic surjectivity and the pairing, rather than
silently inferred from zero finite rank. No desired vanishing, isomorphism,
or finite-dimensionality is included among its hypotheses. -/
theorem even_theta_global_sections_eq_zero
    (hH : Module.finrank K (H.val.obj (op ⊤)) = 3)
    (heven : Even (Module.finrank K (Θ.val.obj (op ⊤))))
    (s : Θ.val.obj (op ⊤)) : s = 0 := by
  letI : FiniteDimensional K (Θ.val.obj (op ⊤)) :=
    theta_global_finiteDimensional_of_quadratic_surjective Θ H T μ ν U hcover
      θframes i₀ (tframes i₀) (hμ i₀) e h2
  have hzero := even_theta_global_finrank_eq_zero Θ H T μ ν U hcover hU
    θframes hframes tframes hμ hν i₀ e h2 h4 hH heven
  letI : Subsingleton (Θ.val.obj (op ⊤)) := (Module.finrank_zero_iff.mp hzero)
  exact Subsingleton.elim _ _

include hcover hU θframes tframes hμ hν h2 h4 in
/-- Even theta ineffectivity from the actual restriction maps and local
line-sheaf data. Both finite-dimensional theta sections and the hyperplane
dimension three are proved internally. The remaining inputs are actual
geometric objects, local perfectness/normality, the two restriction facts,
and parity; there is no assumed vanishing, sheaf isomorphism, or dimension. -/
theorem even_theta_ineffective_of_restriction_maps
    (heven : Even (Module.finrank K (Θ.val.obj (op ⊤))))
    (s : Θ.val.obj (op ⊤)) : s = 0 := by
  have hH := hyperplane_finrank_eq_three_of_quadratic_surjective H T ν U hcover
    hframes tframes (U i₀) (hframes i₀) (tframes i₀) (hν i₀) e h2 h4
  exact even_theta_global_sections_eq_zero Θ H T μ ν U hcover hU
    θframes hframes tframes hμ hν i₀ e h2 h4 hH heven s

end EvenQuinticConic
