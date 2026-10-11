import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Localization.Module
import EvenQuinticConic.PlaneDifferentialIdentities
import EvenQuinticConic.SchemeKaehlerSheaf

/-!
# The actual differential of affine regular functions

A regular function on an open subset of `Spec A` is locally a fraction.
Its differential is formed pointwise using the canonical localization
isomorphism for Kähler differentials. The quotient rule proves that these
pointwise differentials are sections of the actual module sheaf
`ModuleCat.tilde Ω[A/K]`.
-/

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace EvenQuinticConic

variable {K A : Type u} [CommRing K] [CommRing A] [Algebra K A]

/-- Localization of genuine ring differentials, with linearity over the
localized ring rather than only over the original ring. -/
noncomputable def affineKaehlerLocalizationEquiv (x : PrimeSpectrum A) :
    LocalizedModule x.asIdeal.primeCompl Ω[A⁄K] ≃ₗ[Localization.AtPrime x.asIdeal]
      Ω[Localization.AtPrime x.asIdeal⁄K] :=
  LinearEquiv.extendScalarsOfIsLocalization x.asIdeal.primeCompl
    (Localization.AtPrime x.asIdeal)
    (IsLocalizedModule.iso x.asIdeal.primeCompl
      (KaehlerDifferential.map K K A (Localization.AtPrime x.asIdeal)))

/-- The pointwise differential of a localized regular function. -/
noncomputable def affineKaehlerPointDifferential (x : PrimeSpectrum A)
    (a : Localization.AtPrime x.asIdeal) :
    LocalizedModule x.asIdeal.primeCompl Ω[A⁄K] :=
  (affineKaehlerLocalizationEquiv (K := K) x).symm
    (KaehlerDifferential.D K (Localization.AtPrime x.asIdeal) a)

theorem affineKaehlerLocalizationEquiv_mk (x : PrimeSpectrum A) (m : Ω[A⁄K]) :
    affineKaehlerLocalizationEquiv (K := K) x
      (LocalizedModule.mk m (1 : x.asIdeal.primeCompl)) =
        KaehlerDifferential.map K K A (Localization.AtPrime x.asIdeal) m := by
  change IsLocalizedModule.iso x.asIdeal.primeCompl
    (KaehlerDifferential.map K K A (Localization.AtPrime x.asIdeal))
      (LocalizedModule.mk m 1) = _
  exact IsLocalizedModule.iso_mk_one _ _ _

theorem affineKaehlerPointDifferential_algebraMap (x : PrimeSpectrum A) (a : A) :
    affineKaehlerPointDifferential (K := K) x
      (algebraMap A (Localization.AtPrime x.asIdeal) a) =
        LocalizedModule.mkLinearMap x.asIdeal.primeCompl Ω[A⁄K]
          (KaehlerDifferential.D K A a) := by
  apply (affineKaehlerLocalizationEquiv (K := K) x).injective
  simp [affineKaehlerPointDifferential, affineKaehlerLocalizationEquiv_mk]

theorem affineKaehlerPointDifferential_zero (x : PrimeSpectrum A) :
    affineKaehlerPointDifferential (K := K) x 0 = 0 := by
  simp [affineKaehlerPointDifferential]

theorem affineKaehlerPointDifferential_add (x : PrimeSpectrum A)
    (a b : Localization.AtPrime x.asIdeal) :
    affineKaehlerPointDifferential (K := K) x (a + b) =
      affineKaehlerPointDifferential (K := K) x a +
        affineKaehlerPointDifferential (K := K) x b := by
  simp [affineKaehlerPointDifferential]

theorem affineKaehlerPointDifferential_mul (x : PrimeSpectrum A)
    (a b : Localization.AtPrime x.asIdeal) :
    affineKaehlerPointDifferential (K := K) x (a * b) =
      a • affineKaehlerPointDifferential (K := K) x b +
        b • affineKaehlerPointDifferential (K := K) x a := by
  simp [affineKaehlerPointDifferential, Derivation.leibniz]

/-- The quotient rule expressed without a chosen inverse or denominator
notation; it applies directly to the witnesses defining regular sections. -/
theorem affineKaehlerPointDifferential_fraction (x : PrimeSpectrum A)
    (a b : A) (c : Localization.AtPrime x.asIdeal)
    (hc : c * algebraMap A (Localization.AtPrime x.asIdeal) b =
      algebraMap A (Localization.AtPrime x.asIdeal) a) :
    (b ^ 2) • affineKaehlerPointDifferential (K := K) x c =
      LocalizedModule.mkLinearMap x.asIdeal.primeCompl Ω[A⁄K]
        (b • KaehlerDifferential.D K A a - a • KaehlerDifferential.D K A b) := by
  have hs (r : A) (m : LocalizedModule x.asIdeal.primeCompl Ω[A⁄K]) :
      affineKaehlerLocalizationEquiv (K := K) x (r • m) =
        r • affineKaehlerLocalizationEquiv (K := K) x m :=
    (IsLocalizedModule.iso x.asIdeal.primeCompl
      (KaehlerDifferential.map K K A (Localization.AtPrime x.asIdeal))).map_smul r m
  apply (affineKaehlerLocalizationEquiv (K := K) x).injective
  rw [← algebraMap_smul (Localization.AtPrime x.asIdeal) (b ^ 2)]
  simpa only [affineKaehlerPointDifferential, map_smul, hs,
    LinearEquiv.apply_symm_apply, map_pow,
    LocalizedModule.mkLinearMap_apply, affineKaehlerLocalizationEquiv_mk, map_sub, map_smul,
    KaehlerDifferential.map_D, algebraMap_smul] using
      derivation_fraction_identity
        (KaehlerDifferential.D K (Localization.AtPrime x.asIdeal))
        (algebraMap A (Localization.AtPrime x.asIdeal) a)
        (algebraMap A (Localization.AtPrime x.asIdeal) b) c hc

/-- Differentiating actual regular functions produces locally fractional
sections of the actual associated module sheaf. -/
theorem affineKaehlerDifferential_isLocallyFraction
    (U : Opens (PrimeSpectrum A)) (s : (Spec.structureSheaf A).val.obj (op U)) :
    (ModuleCat.Tilde.isLocallyFraction (ModuleCat.of A Ω[A⁄K])).pred
      (fun x : U ↦ affineKaehlerPointDifferential (K := K) x.1 (s.1 x)) := by
  intro x
  obtain ⟨V, hx, i, a, b, h⟩ := s.2 x
  refine ⟨V, hx, i, b • KaehlerDifferential.D K A a -
    a • KaehlerDifferential.D K A b, b ^ 2, ?_⟩
  intro y
  exact ⟨fun hb ↦ (h y).1 (y.1.isPrime.mem_of_pow_mem 2 hb),
    affineKaehlerPointDifferential_fraction y.1 a b (s.1 (i y)) (h y).2⟩

/-- The additive differential on an actual open of `Spec A`. -/
noncomputable def affineKaehlerDifferential
    (U : Opens (PrimeSpectrum A)) :
    (Spec.structureSheaf A).val.obj (op U) →+
      (ModuleCat.tilde (ModuleCat.of A Ω[A⁄K])).val.obj (op U) where
  toFun s := ⟨fun x ↦ affineKaehlerPointDifferential (K := K) x.1 (s.1 x),
    affineKaehlerDifferential_isLocallyFraction U s⟩
  map_zero' := by
    apply Subtype.ext
    funext x
    exact affineKaehlerPointDifferential_zero x.1
  map_add' s t := by
    apply Subtype.ext
    funext x
    exact affineKaehlerPointDifferential_add x.1 _ _

theorem affineKaehlerDifferential_mul (U : Opens (PrimeSpectrum A))
    (s t : (Spec.structureSheaf A).val.obj (op U)) :
    affineKaehlerDifferential (K := K) U (s * t) =
      s • affineKaehlerDifferential (K := K) U t +
        t • affineKaehlerDifferential (K := K) U s := by
  apply Subtype.ext
  funext x
  exact affineKaehlerPointDifferential_mul x.1 _ _

theorem affineKaehlerDifferential_restrict {U V : Opens (PrimeSpectrum A)}
    (i : V ⟶ U) (s : (Spec.structureSheaf A).val.obj (op U)) :
    affineKaehlerDifferential (K := K) V ((Spec.structureSheaf A).val.map i.op s) =
      (ModuleCat.tilde (ModuleCat.of A Ω[A⁄K])).val.map i.op
        (affineKaehlerDifferential (K := K) U s) := rfl

/-- Differentiating a regular function from the affine coordinate ring
agrees with the canonical section of its actual ring differential. -/
theorem affineKaehlerDifferential_toOpen (U : Opens (PrimeSpectrum A)) (a : A) :
    affineKaehlerDifferential (K := K) U (StructureSheaf.toOpen A U a) =
      ModuleCat.Tilde.toOpen (ModuleCat.of A Ω[A⁄K]) U
        (KaehlerDifferential.D K A a) := by
  apply Subtype.ext
  funext x
  exact affineKaehlerPointDifferential_algebraMap x.1 a

/-- For the actual affine structure morphism, pulled-back base constants
are the usual constant regular functions. -/
theorem affineSchemeConstantsPresheafHom_app
    (U : Opens (PrimeSpectrum A)) :
    (schemeConstantsPresheafHom
      (Spec.map (CommRingCat.ofHom (algebraMap K A)))).app (op U) =
      CommRingCat.ofHom (algebraMap K A) ≫ StructureSheaf.toOpen A U := by
  change (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
    (Spec.map (CommRingCat.ofHom (algebraMap K A))).appTop ≫ _ = _
  rw [← Scheme.ΓSpecIso_inv_naturality_assoc]
  rfl

/-- Differentiating a pulled-back base-ring constant gives the zero section. -/
theorem affineKaehlerDifferential_constant (U : Opens (PrimeSpectrum A)) (a : K) :
    affineKaehlerDifferential (K := K) U
      ((schemeConstantsPresheafHom
        (Spec.map (CommRingCat.ofHom (algebraMap K A)))).app (op U) a) = 0 := by
  rw [affineSchemeConstantsPresheafHom_app]
  apply Subtype.ext
  funext x
  change affineKaehlerPointDifferential (K := K) x.1
    (algebraMap A (Localization.AtPrime x.1.asIdeal) (algebraMap K A a)) = 0
  rw [affineKaehlerPointDifferential_algebraMap]
  simp

/-- The genuine relative derivation of the affine structure sheaf into
the associated sheaf of the ring's Kähler differential module. -/
noncomputable def affineKaehlerTildeDerivation :
    (ModuleCat.tilde (ModuleCat.of A Ω[A⁄K])).val.Derivation'
      (schemeConstantsPresheafHom
        (Spec.map (CommRingCat.ofHom (algebraMap K A)))) where
  d {U} := affineKaehlerDifferential U.unop
  d_mul {U} := affineKaehlerDifferential_mul U.unop
  d_map i := affineKaehlerDifferential_restrict i.unop
  d_app {U} a := affineKaehlerDifferential_constant (K := K) (A := A) U.unop a

/-- The canonical comparison from the actual sheafified differential
presheaf to the associated module sheaf on an affine scheme. This definition
does not yet assert that the comparison is an isomorphism. -/
noncomputable def affineKaehlerComparison :
    schemeKaehlerSheaf (Spec.map (CommRingCat.ofHom (algebraMap K A))) ⟶
      ModuleCat.tilde (ModuleCat.of A Ω[A⁄K]) :=
  schemeKaehlerDesc _ _ affineKaehlerTildeDerivation

/-- The comparison sends the actual sheaf differential of a regular
function to the locally fractional section constructed above. -/
theorem affineKaehlerComparison_apply (U : Opens (PrimeSpectrum A))
    (s : (Spec.structureSheaf A).val.obj (op U)) :
    (affineKaehlerComparison (K := K) (A := A)).val.app (op U)
      ((schemeKaehlerDerivation
        (Spec.map (CommRingCat.ofHom (algebraMap K A)))).d s) =
      affineKaehlerDifferential (K := K) U s :=
  schemeKaehlerDesc_apply _ _ _ _ _

end EvenQuinticConic
