import EvenQuinticConic.GenericPullback
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-!
# Nonvanishing of homogeneous fractions under actual scheme pullback

A homogeneous fraction is a unit at a projective point if its numerator
avoids that point's homogeneous prime. Its actual pullback to an integral
scheme is therefore nonzero in the function field whenever the image of
the generic point satisfies that condition. This does not identify the
cone fraction field with the projective scheme's function field.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace EvenQuinticConic

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]

/-- A same-degree fraction at a homogeneous prime is a unit when its
numerator avoids the prime. -/
theorem homogeneous_fraction_isUnit_of_num_notMem
    (𝔭 : Ideal A) [𝔭.IsPrime]
    (z : HomogeneousLocalization.NumDenSameDeg 𝒜 𝔭.primeCompl)
    (hz : z.num.1 ∉ 𝔭) : IsUnit (HomogeneousLocalization.mk z) := by
  apply (HomogeneousLocalization.isUnit_iff_isUnit_val 𝒜 𝔭 _).mp
  rw [HomogeneousLocalization.val_mk, Localization.mk_eq_mk']
  exact (IsLocalization.AtPrime.isUnit_mk'_iff (Localization.AtPrime 𝔭) 𝔭
    z.num.1 ⟨z.den.1, z.den_mem⟩).mpr hz

/-- The actual stalk germ of a chart fraction is a unit under the expected
numerator condition at the actual projective point. -/
theorem projective_chart_fraction_germ_isUnit
    (f : A) (x : Proj 𝒜) (hx : x ∈ Proj.basicOpen 𝒜 f)
    (z : HomogeneousLocalization.NumDenSameDeg 𝒜 (Submonoid.powers f))
    (hz : z.num.1 ∉ x.asHomogeneousIdeal.toIdeal) :
    IsUnit ((Proj 𝒜).presheaf.germ (Proj.basicOpen 𝒜 f) x hx
      (Proj.awayToSection 𝒜 f (HomogeneousLocalization.mk z))) := by
  apply (isUnit_map_iff (AlgebraicGeometry.Proj.stalkIso' 𝒜 x) _).mp
  change IsUnit ((Proj.stalkIso' 𝒜 x)
    ((ProjectiveSpectrum.Proj.structureSheaf 𝒜).presheaf.germ
      (ProjectiveSpectrum.basicOpen 𝒜 f) x hx
      (ProjectiveSpectrum.Proj.awayToSection 𝒜 f (HomogeneousLocalization.mk z))))
  rw [AlgebraicGeometry.Proj.stalkIso'_germ]
  exact homogeneous_fraction_isUnit_of_num_notMem 𝒜 x.asHomogeneousIdeal.toIdeal
    ⟨z.deg, z.num, z.den, (Submonoid.powers_le.mpr hx) z.den_mem⟩ hz

/-- Restricting an ambient projective chart fraction along an actual scheme
morphism gives a nonzero element of the source function field when its
numerator avoids the image of the generic point. -/
theorem projective_chart_fraction_generic_pullback_ne_zero
    {X : Scheme} [IsIntegral X] (p : X ⟶ Proj 𝒜) (f : A)
    [Nonempty (p ⁻¹ᵁ Proj.basicOpen 𝒜 f)]
    (z : HomogeneousLocalization.NumDenSameDeg 𝒜 (Submonoid.powers f))
    (hz : z.num.1 ∉ (p.base (genericPoint X)).asHomogeneousIdeal.toIdeal) :
    X.germToFunctionField (p ⁻¹ᵁ Proj.basicOpen 𝒜 f)
      (p.app (Proj.basicOpen 𝒜 f)
        (Proj.awayToSection 𝒜 f (HomogeneousLocalization.mk z))) ≠ 0 := by
  apply (generic_pullback_ne_zero_iff_germ_isUnit p _ _).mpr
  exact projective_chart_fraction_germ_isUnit 𝒜 f (p.base (genericPoint X))
    (genericPoint_image_mem_of_nonempty_preimage p _) z hz

end EvenQuinticConic
