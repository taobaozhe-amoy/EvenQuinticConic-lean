import EvenQuinticConic.RankTwoUnimodularBasis
import EvenQuinticConic.LocalRankTwoKummer
import Mathlib.RingTheory.Localization.Free
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-! # Spreading a rank-two algebra model to a principal localization -/
noncomputable section
open scoped TensorProduct
namespace EvenQuinticConic
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- A rank-two basis after localization spreads to a principal localization.
The conclusion concerns the actual base-change algebra, not a chosen model. -/
theorem exists_principal_rankTwo_basis (S : Submonoid R)
    [Module.FinitePresentation R A]
    (v : Module.Basis (Fin 2) (Localization S) (Localization S ⊗[R] A)) :
    ∃ r : R, r ∈ S ∧ Nonempty (Module.Basis (Fin 2) (Localization.Away r)
      (Localization.Away r ⊗[R] A)) := by
  obtain ⟨r, hr, b, _⟩ := Module.FinitePresentation.exists_basis_localizedModule_powers
    S (TensorProduct.mk R (Localization S) A 1) (Localization S) v
  exact ⟨r, hr, ⟨b.map (LocalizedModule.equivTensorProduct (Submonoid.powers r) A)⟩⟩

/-- Formal unramifiedness and invertibility of two give a unit Kummer model
on some principal localization whenever the localized algebra has rank two. -/
theorem exists_principal_unit_kummer_model (S : Submonoid R)
    [Module.FinitePresentation R A] [Invertible (2 : R)]
    [Algebra.FormallyUnramified R A]
    (v : Module.Basis (Fin 2) (Localization S) (Localization S ⊗[R] A)) :
    ∃ r : R, r ∈ S ∧ ∃ u : (Localization.Away r)ˣ,
      Nonempty ((Localization.Away r ⊗[R] A) ≃ₐ[Localization.Away r]
        KummerAlgebra (u : Localization.Away r)) := by
  obtain ⟨r, hr, ⟨b⟩⟩ := exists_principal_rankTwo_basis S v
  have htwo : IsUnit (2 : Localization.Away r) := by
    simpa only [map_ofNat] using (isUnit_of_invertible (2 : R)).map (algebraMap R (Localization.Away r))
  letI : Invertible (2 : Localization.Away r) := htwo.invertible
  obtain ⟨u, hu⟩ := exists_unit_kummer_model_of_rankTwo_basis b
  exact ⟨r, hr, u, hu⟩

/-- At a prime where the finite flat algebra has rank two, there is a
principal neighborhood with an actual unit Kummer algebra model. -/
theorem exists_principal_unit_kummer_model_atPrime (p : Ideal R) [p.IsPrime]
    [Module.FinitePresentation R A] [Module.Flat R A] [Invertible (2 : R)]
    [Algebra.FormallyUnramified R A]
    (hrank : Module.finrank (Localization.AtPrime p)
      (Localization.AtPrime p ⊗[R] A) = 2) :
    ∃ r : R, r ∉ p ∧ ∃ u : (Localization.Away r)ˣ,
      Nonempty ((Localization.Away r ⊗[R] A) ≃ₐ[Localization.Away r]
        KummerAlgebra (u : Localization.Away r)) := by
  letI : Module.Free (Localization.AtPrime p) (Localization.AtPrime p ⊗[R] A) :=
    Module.free_of_flat_of_isLocalRing
  exact exists_principal_unit_kummer_model p.primeCompl
    (Module.finBasisOfFinrankEq _ _ hrank)

/-- Pointwise rank two produces a principal-open cover by unit Kummer models.
This does not yet assert compatibility of chosen models on overlaps. -/
theorem exists_principal_unit_kummer_cover
    [Module.FinitePresentation R A] [Module.Flat R A] [Invertible (2 : R)]
    [Algebra.FormallyUnramified R A]
    (hrank : ∀ p : PrimeSpectrum R, Module.finrank (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime p.asIdeal ⊗[R] A) = 2) :
    ∃ f : PrimeSpectrum R → R,
      (⨆ p, PrimeSpectrum.basicOpen (f p)) = ⊤ ∧
      ∀ p, ∃ u : (Localization.Away (f p))ˣ,
        Nonempty ((Localization.Away (f p) ⊗[R] A) ≃ₐ[Localization.Away (f p)]
          KummerAlgebra (u : Localization.Away (f p))) := by
  classical
  have h := fun p : PrimeSpectrum R =>
    exists_principal_unit_kummer_model_atPrime p.asIdeal (hrank p)
  choose f hf u hu using h
  refine ⟨f, ?_, fun p => ⟨u p, hu p⟩⟩
  apply top_unique
  intro p _
  exact TopologicalSpace.Opens.mem_iSup.mpr
    ⟨p, (PrimeSpectrum.mem_basicOpen (f p) p).mpr (hf p)⟩

end EvenQuinticConic
