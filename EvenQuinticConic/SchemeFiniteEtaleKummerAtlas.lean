import EvenQuinticConic.SchemeAffinePresentation
import EvenQuinticConic.SchemePushforwardIsoChart
import EvenQuinticConic.SchemePushforwardKummerCover
import EvenQuinticConic.SchemePushforwardTrace

/-!
# Covering Kummer atlases on the original base scheme

The local models are first obtained for the actual affine section algebra.
Multiplicative chart transport through the canonical affine presentations
then places them on the actual restricted scheme morphism. Open-image
transport and a dependent covering family assemble the original pushforward
atlas. No local chart, section comparison or overlap map is an input.

Geometric flatness, Noetherian affine section rings, invertibility of two,
and the actual section algebras' local rank two remain explicit hypotheses.
-/

noncomputable section
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
universe u
namespace EvenQuinticConic
variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The actual restricted morphism has covering multiplicative Kummer charts
on an affine base open, constructed from the geometric and rank hypotheses. -/
theorem exists_restrictedAffinePushforwardKummerCharts
    [IsFinite f] [IsEtale f] [AlgebraicGeometry.Flat f]
    (U : Y.Opens) (hU : IsAffineOpen U)
    [IsNoetherianRing Γ(Y, U)] [Invertible (2 : Γ(Y, U))]
    (hrank : letI : Algebra Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
      ∀ p : PrimeSpectrum Γ(Y, U), Module.finrank (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime p.asIdeal ⊗[Γ(Y, U)] Γ(X, f ⁻¹ᵁ U)) = 2) :
    ∃ V : PrimeSpectrum Γ(Y, U) → U.toScheme.Opens, iSup V = ⊤ ∧
      ∃ v : ∀ p, Γ(U.toScheme, V p)ˣ,
        Nonempty (∀ p, PushforwardKummerChart (f ∣_ U) (V p) (v p)) := by
  classical
  letI : Algebra Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
  obtain ⟨g, hg, hm⟩ := exists_affinePreimageKummerModels f U hU hrank
  choose v e using hm
  let V : PrimeSpectrum Γ(Y, U) → U.toScheme.Opens :=
    fun p ↦ hU.isoSpec.hom ⁻¹ᵁ PrimeSpectrum.basicOpen (g p)
  let a : ∀ p, Γ(Spec (CommRingCat.of Γ(Y, U)), PrimeSpectrum.basicOpen (g p))ˣ :=
    fun p ↦ Units.map (StructureSheaf.toBasicOpen Γ(Y, U) (g p)).toMonoidHom (v p)
  refine ⟨V, hU.isoSpec.hom.preimage_iSup_eq_top hg,
    (fun p ↦ Units.map (hU.isoSpec.hom.app (PrimeSpectrum.basicOpen (g p))).hom.toMonoidHom
      (a p)), ⟨?_⟩⟩
  intro p
  exact (affinePushforwardRingChart (v p) (Classical.choice (e p))).isoTransport
    (hU.preimage f).isoSpec hU.isoSpec
    (affinePreimage_isoSpec_hom_naturality f U hU).symm

/-- Finite étale, explicitly flat rank-two data on an affine cover construct
covering multiplicative charts of the original morphism over its original base. -/
theorem exists_schemePushforwardKummerCharts_of_affine_cover
    [IsFinite f] [IsEtale f] [AlgebraicGeometry.Flat f]
    {ι : Type u} (U : ι → Y.Opens) (hU : iSup U = ⊤)
    (hAffine : ∀ i, IsAffineOpen (U i))
    [∀ i, IsNoetherianRing Γ(Y, U i)] [∀ i, Invertible (2 : Γ(Y, U i))]
    (hrank : ∀ i, letI : Algebra Γ(Y, U i) Γ(X, f ⁻¹ᵁ U i) := (f.app (U i)).hom.toAlgebra
      ∀ p : PrimeSpectrum Γ(Y, U i), Module.finrank (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime p.asIdeal ⊗[Γ(Y, U i)] Γ(X, f ⁻¹ᵁ U i)) = 2) :
    ∃ W : (Σ i, PrimeSpectrum Γ(Y, U i)) → Y.Opens, iSup W = ⊤ ∧
      ∃ w : ∀ j, Γ(Y, W j)ˣ,
        Nonempty (∀ j, PushforwardKummerChart f (W j) (w j)) := by
  apply exists_schemePushforwardKummerCharts_of_local_existence f U hU
  intro i
  exact exists_restrictedAffinePushforwardKummerCharts f (U i) (hAffine i) (hrank i)

/-- Finite étale, explicitly flat rank-two data on an affine cover construct
a covering atlas on the actual pushforward over the original base scheme. -/
theorem exists_schemePushforwardKummerAtlas_of_affine_cover
    [IsFinite f] [IsEtale f] [AlgebraicGeometry.Flat f]
    {ι : Type u} (U : ι → Y.Opens) (hU : iSup U = ⊤)
    (hAffine : ∀ i, IsAffineOpen (U i))
    [∀ i, IsNoetherianRing Γ(Y, U i)] [∀ i, Invertible (2 : Γ(Y, U i))]
    (hrank : ∀ i, letI : Algebra Γ(Y, U i) Γ(X, f ⁻¹ᵁ U i) := (f.app (U i)).hom.toAlgebra
      ∀ p : PrimeSpectrum Γ(Y, U i), Module.finrank (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime p.asIdeal ⊗[Γ(Y, U i)] Γ(X, f ⁻¹ᵁ U i)) = 2) :
    ∃ W : (Σ i, PrimeSpectrum Γ(Y, U i)) → Y.Opens, iSup W = ⊤ ∧
      Nonempty (KummerModuleAtlas (schemePushforwardStructureModule f) W) := by
  obtain ⟨W, hW, w, ⟨c⟩⟩ :=
    exists_schemePushforwardKummerCharts_of_affine_cover f U hU hAffine hrank
  exact ⟨W, hW, ⟨pushforwardKummerAtlas W w c⟩⟩

end EvenQuinticConic
