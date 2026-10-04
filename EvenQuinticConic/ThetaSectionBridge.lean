import EvenQuinticConic.GenericCoefficientModel
import EvenQuinticConic.SchemeScalarAction
import EvenQuinticConic.ModulePairing
import EvenQuinticConic.PairingComparison

/-!
# From genuine theta sections to a linear section of the hyperplane sheaf

The coefficient maps used here come from actual local frames on an integral
scheme over a field.  A homogeneous linear factor is interpreted as an actual
linear combination of the three specified global hyperplane sections.
The degree-four injectivity and the existence of quadratic lifts remain
explicit geometric inputs; no factor or constant-square section is assumed.
-/

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open MvPolynomial

universe u

namespace EvenQuinticConic

private theorem fin3_degree_one_cases (d : Fin 3 →₀ ℕ) (hd : d.degree = 1) :
    d = Finsupp.single 0 1 ∨ d = Finsupp.single 1 1 ∨ d = Finsupp.single 2 1 := by
  have hsum : d 0 + d 1 + d 2 = 1 := by
    simpa [Finsupp.degree_eq_sum, Fin.sum_univ_three, add_assoc] using hd
  have hcases : (d 0 = 1 ∧ d 1 = 0 ∧ d 2 = 0) ∨
      (d 0 = 0 ∧ d 1 = 1 ∧ d 2 = 0) ∨
      (d 0 = 0 ∧ d 1 = 0 ∧ d 2 = 1) := by omega
  rcases hcases with h | h | h
  · left
    ext i
    fin_cases i <;> simp [h.1, h.2.1, h.2.2]
  · right; left
    ext i
    fin_cases i <;> simp [h.1, h.2.1, h.2.2]
  · right; right
    ext i
    fin_cases i <;> simp [h.1, h.2.1, h.2.2]

/-- A degree-one homogeneous polynomial in the actual three projective
coordinates is the corresponding linear combination of those coordinates. -/
theorem homogeneous_linear_fin3_eq {K : Type*} [CommSemiring K]
    (a : MvPolynomial (Fin 3) K) (ha : a.IsHomogeneous 1) :
    a = ∑ i : Fin 3, a.coeff (Finsupp.single i 1) • X i := by
  classical
  ext d
  by_cases hd : d.degree = 1
  · rcases fin3_degree_one_cases d hd with rfl | rfl | rfl <;>
      simp [Fin.sum_univ_three, coeff_smul, coeff_X', Finsupp.single_eq_single_iff]
  · have hne (i : Fin 3) : d ≠ Finsupp.single i 1 := by
      intro heq
      apply hd
      simp [heq]
    simp [ha.coeff_eq_zero hd, coeff_smul, coeff_X',
      Ne.symm (hne 0), Ne.symm (hne 1), Ne.symm (hne 2), Fin.sum_univ_three]

/-- Evaluation of a linear homogeneous polynomial is its actual finite
linear combination of the coefficient values. -/
theorem homogeneous_linear_fin3_aeval {K L : Type*} [CommSemiring K]
    [CommSemiring L] [Algebra K L] (f : Fin 3 → L)
    (a : MvPolynomial (Fin 3) K) (ha : a.IsHomogeneous 1) :
    aeval f a = ∑ i : Fin 3, a.coeff (Finsupp.single i 1) • f i := by
  nth_rw 1 [homogeneous_linear_fin3_eq a ha]
  simp

open scoped SchemeScalars

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (CommRingCat.of K))]

/-- The actual global hyperplane section supplied by a linear polynomial in
three given global sections. It uses only the scheme-induced scalar action. -/
noncomputable def linearPolynomialSection (H : X.Modules)
    (e : Fin 3 → H.val.obj (op ⊤)) (a : MvPolynomial (Fin 3) K) :
    H.val.obj (op ⊤) :=
  ∑ i : Fin 3, a.coeff (Finsupp.single i 1) • e i

/-- Taking generic coefficients of the constructed section is the actual
polynomial evaluation at the generic coefficients of the coordinates. -/
theorem genericCoefficient_linearPolynomialSection (H : X.Modules)
    (V : X.Opens) [Nonempty V] (frame : ModuleSheafFrame H V)
    (e : Fin 3 → H.val.obj (op ⊤))
    (a : MvPolynomial (Fin 3) K) (ha : a.IsHomogeneous 1) :
    schemeGenericLinearMap (K := K) H V frame (linearPolynomialSection H e a) =
      aeval (fun i ↦ schemeGenericLinearMap (K := K) H V frame (e i)) a := by
  rw [homogeneous_linear_fin3_aeval _ a ha]
  simp [linearPolynomialSection]

/-- The generic restriction of a quadratic polynomial in three genuine
hyperplane sections, using the actual square pairing.  The pairing factor
is computed from local frames; it is not an independent scalar input. -/
noncomputable def quadraticGenericRestriction
    {H T : X.Modules} (ν : ModuleSheafPairing H H T)
    (V : X.Opens) [Nonempty V] (h : ModuleSheafFrame H V)
    (p : ModuleSheafFrame T V) (e : Fin 3 → H.val.obj (op ⊤))
    (A : MvPolynomial (Fin 3) K) : X.functionField :=
  X.germToFunctionField V (modulePairingCoefficient ν V h p) *
    aeval (fun i ↦ schemeGenericLinearMap (K := K) H V h (e i)) A

/-- Three quadratic lifts of the products of two independent genuine theta
sections produce a genuine hyperplane section whose square differs by a
nonzero base-field constant. The only remaining geometric polynomial inputs
are the quadratic lifts and injectivity in homogeneous degree four. In
particular, the linear section and its square relation are conclusions.

The lifts are stated at the actual generic stalk, with the restriction map
computed from the given hyperplane sections and the actual natural pairing.
No arbitrary coefficient map, multiplier, or rational square root is input.
-/
theorem exists_linear_section_of_quadratic_lifts [IsAlgClosed K]
    (Θ H T : X.Modules)
    (μ : ModuleSheafPairing Θ Θ T) (ν : ModuleSheafPairing H H T)
    {ι : Type*} (U : ι → X.Opens) [∀ i, Nonempty (U i)]
    (hcover : iSup U = ⊤)
    (θframes : ∀ i, ModuleSheafFrame Θ (U i))
    (tframes : ∀ i, ModuleSheafFrame T (U i))
    (V : X.Opens) [Nonempty V]
    (θframe : ModuleSheafFrame Θ V) (hframe : ModuleSheafFrame H V)
    (tframe : ModuleSheafFrame T V)
    (hμ : Function.Bijective (TensorProduct.lift (μ.app V)))
    (hν : Function.Bijective (TensorProduct.lift (ν.app V)))
    (e : Fin 3 → H.val.obj (op ⊤)) (s t : Θ.val.obj (op ⊤))
    (hst : LinearIndependent K ![s, t])
    (A B D : MvPolynomial (Fin 3) K)
    (hA : A.IsHomogeneous 2) (hB : B.IsHomogeneous 2) (hD : D.IsHomogeneous 2)
    (h4 : ∀ P : MvPolynomial (Fin 3) K, P.IsHomogeneous 4 →
      aeval (fun i ↦ schemeGenericLinearMap (K := K) H V hframe (e i)) P = 0 →
      P = 0)
    (hAs : schemeGenericLinearMap (K := K) T V tframe (μ.app ⊤ s s) =
      quadraticGenericRestriction ν V hframe tframe e A)
    (hBst : schemeGenericLinearMap (K := K) T V tframe (μ.app ⊤ s t) =
      quadraticGenericRestriction ν V hframe tframe e B)
    (hDt : schemeGenericLinearMap (K := K) T V tframe (μ.app ⊤ t t) =
      quadraticGenericRestriction ν V hframe tframe e D) :
    ∃ (c : K) (a : MvPolynomial (Fin 3) K),
      c ≠ 0 ∧ a.IsHomogeneous 1 ∧
      linearPolynomialSection H e a ≠ 0 ∧
      μ.app ⊤ s s = c • ν.app ⊤ (linearPolynomialSection H e a)
        (linearPolynomialSection H e a) := by
  let f : Fin 3 → X.functionField := fun i ↦
    schemeGenericLinearMap (K := K) H V hframe (e i)
  let α := schemeGenericLinearMap (K := K) Θ V θframe s
  let β := schemeGenericLinearMap (K := K) Θ V θframe t
  let vθ := X.germToFunctionField V (modulePairingCoefficient μ V θframe tframe)
  let vH := X.germToFunctionField V (modulePairingCoefficient ν V hframe tframe)
  have hvθ : vθ ≠ 0 :=
    ((modulePairingCoefficient_isUnit μ V θframe tframe hμ).map
      (X.germToFunctionField V).hom).ne_zero
  have hvH : vH ≠ 0 :=
    ((modulePairingCoefficient_isUnit ν V hframe tframe hν).map
      (X.germToFunctionField V).hom).ne_zero
  let u := vθ / vH
  have hu : u ≠ 0 := div_ne_zero hvθ hvH
  have hind : LinearIndependent K ![α, β] := by
    convert scheme_generic_coefficients_linearIndependent Θ U hcover θframes
      V θframe ![s, t] hst using 1
    funext i
    fin_cases i <;> rfl
  have hs2 : vθ * α * α = vH * aeval f A := by
    have hs := moduleGlobalGenericLinearMap_pairing μ V θframe tframe s s
    change schemeGenericLinearMap (K := K) T V tframe (μ.app ⊤ s s) =
      vθ * α * α at hs
    exact hs.symm.trans hAs
  have hst2 : vθ * α * β = vH * aeval f B := by
    have hs := moduleGlobalGenericLinearMap_pairing μ V θframe tframe s t
    change schemeGenericLinearMap (K := K) T V tframe (μ.app ⊤ s t) =
      vθ * α * β at hs
    exact hs.symm.trans hBst
  have ht2 : vθ * β * β = vH * aeval f D := by
    have hs := moduleGlobalGenericLinearMap_pairing μ V θframe tframe t t
    change schemeGenericLinearMap (K := K) T V tframe (μ.app ⊤ t t) =
      vθ * β * β at hs
    exact hs.symm.trans hDt
  have hα : aeval f A = u * α ^ 2 := by
    apply mul_left_cancel₀ hvH
    rw [← hs2]
    dsimp [u]
    field_simp
  have hαβ : aeval f B = u * α * β := by
    apply mul_left_cancel₀ hvH
    rw [← hst2]
    dsimp [u]
    field_simp
  have hβ : aeval f D = u * β ^ 2 := by
    apply mul_left_cancel₀ hvH
    rw [← ht2]
    dsimp [u]
    field_simp
  obtain ⟨c, a, b, hc, ha, hb, hAE, hBE, hDE, ha0, _, _⟩ :=
    generic_coefficient_ratio_of_quartic_injective f A B D u α β h4
      hA hB hD hu hind hα hαβ hβ
  have heval := genericCoefficient_linearPolynomialSection H V hframe e a ha
  have haH : linearPolynomialSection H e a ≠ 0 := by
    intro hzero
    apply ha0
    rw [← heval, hzero, map_zero]
  refine ⟨c, a, hc, ha, haH, ?_⟩
  apply schemeGenericLinearMap_injective (K := K) T U hcover tframes V tframe
  rw [map_smul, hAs]
  have hνa := moduleGlobalGenericLinearMap_pairing ν V hframe tframe
    (linearPolynomialSection H e a) (linearPolynomialSection H e a)
  change schemeGenericLinearMap (K := K) T V tframe
      (ν.app ⊤ (linearPolynomialSection H e a) (linearPolynomialSection H e a)) =
    vH * schemeGenericLinearMap (K := K) H V hframe (linearPolynomialSection H e a) *
      schemeGenericLinearMap (K := K) H V hframe (linearPolynomialSection H e a) at hνa
  rw [hνa, heval]
  change vH * aeval f A = algebraMap K X.functionField c *
    (vH * aeval f a * aeval f a)
  rw [hAE, map_mul, map_pow, aeval_C]
  ring

/-- Actual line-module sheaves are isomorphic once two independent theta
sections have the three specified quadratic lifts and homogeneous quartic
restriction is injective. Normality is used through the integrally closed
rings of the supplied affine cover. The isomorphism is constructed from the
linear section produced above; it is not a geometric input.

The two natural, locally tensor-perfect pairings represent the two square
bundles in one common target `T`. An actual theta-square isomorphism supplies
such pairings; no isomorphism `Θ ≅ H` is presumed.
-/
theorem theta_iso_hyperplane_of_quadratic_lifts [IsAlgClosed K]
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
    (i₀ : ι) (e : Fin 3 → H.val.obj (op ⊤)) (s t : Θ.val.obj (op ⊤))
    (hst : LinearIndependent K ![s, t])
    (A B D : MvPolynomial (Fin 3) K)
    (hA : A.IsHomogeneous 2) (hB : B.IsHomogeneous 2) (hD : D.IsHomogeneous 2)
    (h4 : ∀ P : MvPolynomial (Fin 3) K, P.IsHomogeneous 4 →
      aeval (fun j ↦ schemeGenericLinearMap (K := K) H (U i₀) (hframes i₀) (e j)) P = 0 →
      P = 0)
    (hAs : schemeGenericLinearMap (K := K) T (U i₀) (tframes i₀) (μ.app ⊤ s s) =
      quadraticGenericRestriction ν (U i₀) (hframes i₀) (tframes i₀) e A)
    (hBst : schemeGenericLinearMap (K := K) T (U i₀) (tframes i₀) (μ.app ⊤ s t) =
      quadraticGenericRestriction ν (U i₀) (hframes i₀) (tframes i₀) e B)
    (hDt : schemeGenericLinearMap (K := K) T (U i₀) (tframes i₀) (μ.app ⊤ t t) =
      quadraticGenericRestriction ν (U i₀) (hframes i₀) (tframes i₀) e D) :
    Nonempty (Θ ≅ H) := by
  obtain ⟨c, a, hc, _, haH, hsquare⟩ :=
    exists_linear_section_of_quadratic_lifts Θ H T μ ν U hcover θframes tframes
      (U i₀) (θframes i₀) (hframes i₀) (tframes i₀) (hμ i₀) (hν i₀)
      e s t hst A B D hA hB hD h4 hAs hBst hDt
  let cU : Γ(X, ⊤)ˣ := Units.map
    (schemeBaseScalarHom (X ↘ Spec (CommRingCat.of K))).toMonoidHom (Units.mk0 c hc)
  have hsquareU : μ.app ⊤ s s = (cU : Γ(X, ⊤)) •
      ν.app ⊤ (linearPolynomialSection H e a) (linearPolynomialSection H e a) := by
    change μ.app ⊤ s s = c • _
    exact hsquare
  obtain ⟨iso, _⟩ := exists_moduleSheafIso_of_pairing_square_eq X μ ν U hcover hU
    θframes hframes tframes s (linearPolynomialSection H e a) haH cU hsquareU hμ hν
  exact ⟨iso.symm⟩

end EvenQuinticConic
