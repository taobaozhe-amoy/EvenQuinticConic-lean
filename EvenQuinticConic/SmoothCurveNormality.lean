import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
# Normality from one-dimensional smooth differential data

The local cotangent-space bound is derived from the actual conormal map for
`A → κ(A)`.  No normality or regularity conclusion is assumed as an input.

The global endpoint `standardSmoothCurve_isIntegrallyClosed` proves that an
integral standard smooth algebra of relative dimension one over a perfect field
is integrally closed.  Its proof includes finiteness and separability of maximal
residue fields, localization of the differential module, and globalization from
maximal localizations.  A geometric application still has to supply actual
standard-smooth charts of relative dimension one; this file does not identify
the plane quintic's smoothness condition with that chart data.
-/

namespace EvenQuinticConic

open IsLocalRing Module
open scoped TensorProduct

universe u

variable (K A : Type u) [Field K] [CommRing A] [Algebra K A]
  [IsLocalRing A]

/-- For a formally smooth local algebra with formally smooth residue field,
the cotangent space injects into the residue-fibre of its module of differentials. -/
noncomputable def smoothLocalCotangentInjection
    [Algebra.FormallySmooth K A] [Algebra.FormallySmooth K (ResidueField A)] :
    CotangentSpace A →ₗ[ResidueField A]
      (ResidueField A) ⊗[A] Ω[A⁄K] := by
  let e : CotangentSpace A ≃ₗ[A]
      (RingHom.ker (algebraMap A (ResidueField A))).Cotangent :=
    by
      rw [ResidueField.algebraMap_eq, ker_residue]
  exact ((KaehlerDifferential.kerCotangentToTensor K A (ResidueField A)).comp
    e.toLinearMap).extendScalarsOfSurjective (residue_surjective (R := A))

/-- The preceding map is injective by the formal-smoothness splitting theorem. -/
theorem smoothLocalCotangentInjection_injective
    [Algebra.FormallySmooth K A] [Algebra.FormallySmooth K (ResidueField A)] :
    Function.Injective (smoothLocalCotangentInjection K A) := by
  have hinj := ((Algebra.FormallySmooth.iff_injective_and_split
    (R := K) (P := A) (S := ResidueField A)
    (residue_surjective (R := A))).mp inferInstance).1
  unfold smoothLocalCotangentInjection
  exact hinj.comp (LinearEquiv.injective _)

variable [IsNoetherianRing A] [IsDomain A]

/-- A noetherian local domain with formally smooth algebra and residue field
is integrally closed when its free differential module has rank at most one. -/
theorem smoothLocal_isIntegrallyClosed_of_differential_rank
    [Algebra.FormallySmooth K A] [Algebra.FormallySmooth K (ResidueField A)]
    [Module.Free A Ω[A⁄K]] [Module.Finite A Ω[A⁄K]]
    (hrank : Module.finrank A Ω[A⁄K] ≤ 1) : IsIntegrallyClosed A := by
  have hcot : Module.finrank (ResidueField A) (CotangentSpace A) ≤ 1 := by
    calc
      _ ≤ Module.finrank (ResidueField A) ((ResidueField A) ⊗[A] Ω[A⁄K]) :=
        LinearMap.finrank_le_finrank_of_injective
          (smoothLocalCotangentInjection_injective K A)
      _ = Module.finrank A Ω[A⁄K] := Module.finrank_baseChange
      _ ≤ 1 := hrank
  exact (((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain A).out 5 3 rfl rfl).mp hcot).1

/-- Standard smooth relative dimension one supplies the differential-rank hypothesis
in the preceding local theorem. -/
theorem standardSmoothLocal_isIntegrallyClosed
    [Algebra.IsStandardSmoothOfRelativeDimension 1 K A]
    [Algebra.IsSeparable K (ResidueField A)] : IsIntegrallyClosed A := by
  letI : Algebra.IsStandardSmooth K A :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth 1
  letI : Algebra.FormallyEtale K (ResidueField A) :=
    Algebra.FormallyEtale.of_isSeparable K (ResidueField A)
  apply smoothLocal_isIntegrallyClosed_of_differential_rank K A
  rw [Module.finrank, Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential 1]
  simp

section Global

variable (B : Type u) [CommRing B] [Algebra K B] [IsDomain B]

/-- A standard smooth curve algebra over a perfect field is integrally closed.
The proof localizes at maximal ideals, uses separability of the finite residue
extensions, and derives the local cotangent bound from differential base change. -/
theorem standardSmoothCurve_isIntegrallyClosed [PerfectField K]
    [Algebra.IsStandardSmoothOfRelativeDimension 1 K B] : IsIntegrallyClosed B := by
  letI : Algebra.IsStandardSmooth K B :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth 1
  letI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing K B
  apply IsIntegrallyClosed.of_localization_maximal
  intro p _ hp
  let L := Localization.AtPrime p
  letI : Algebra.FormallyEtale B L := Algebra.FormallyEtale.of_isLocalization p.primeCompl
  letI : Algebra.FormallySmooth K L := Algebra.FormallySmooth.comp K B L
  let e := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K B L
  letI : Module.Free L Ω[L⁄K] := Module.Free.of_equiv e
  letI : Module.Finite L Ω[L⁄K] := Module.Finite.equiv e
  letI : Field (B ⧸ p) := Ideal.Quotient.field p
  letI : IsScalarTower K (B ⧸ p) p.ResidueField :=
    IsScalarTower.of_algebraMap_eq fun k => by
      change algebraMap K p.ResidueField k =
        algebraMap B p.ResidueField (algebraMap K B k)
      exact IsScalarTower.algebraMap_apply K B p.ResidueField k
  letI : Module.Finite K (B ⧸ p) := finite_of_finite_type_of_isJacobsonRing K (B ⧸ p)
  letI : Module.Finite K (ResidueField L) :=
    Module.Finite.of_surjective
      (IsScalarTower.toAlgHom K (B ⧸ p) p.ResidueField).toLinearMap
      p.bijective_algebraMap_quotient_residueField.2
  letI : Algebra.FormallyEtale K (ResidueField L) :=
    Algebra.FormallyEtale.of_isSeparable K (ResidueField L)
  apply smoothLocal_isIntegrallyClosed_of_differential_rank K L
  rw [← e.finrank_eq, Module.finrank_baseChange, Module.finrank,
    Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential 1]
  simp

end Global

end EvenQuinticConic
