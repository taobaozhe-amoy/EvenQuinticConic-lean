import Mathlib.AlgebraicGeometry.FunctionField
import EvenQuinticConic.LocalSquareUnit

/-!
# Regular functions and the actual generic stalk of an integral scheme

These lemmas use mathlib's structure sheaf, its restriction maps, and its
function field (the stalk at the scheme's generic point).  Injectivity is
proved from `IsIntegral X`; it is not an input assumption.  The affine-open
extension results assume that the actual coordinate ring is integrally
closed.  They do not assert that a particular plane curve is normal.
-/

open AlgebraicGeometry CategoryTheory Opposite

namespace EvenQuinticConic

variable (X : Scheme) [IsIntegral X]

/-- Equality of regular functions on a nonempty open can be checked in the
actual function field of an integral scheme. -/
theorem regular_eq_iff_generic_eq (U : X.Opens) [Nonempty U]
    (s t : Γ(X, U)) :
    s = t ↔ X.germToFunctionField U s = X.germToFunctionField U t :=
  (X.germToFunctionField_injective U).eq_iff.symm

/-- The canonical embedding of regular functions into the function field
commutes with restriction to a nonempty open. -/
theorem generic_germ_restrict {U V : X.Opens} [Nonempty U] [Nonempty V]
    (i : U ⟶ V) (s : Γ(X, V)) :
    X.germToFunctionField U (X.presheaf.map i.op s) =
      X.germToFunctionField V s := by
  exact X.presheaf.germ_res_apply i _ _ s

/-- Two local regular representatives of the same rational function agree
on every common nonempty subopen. -/
theorem regular_restrict_eq_of_generic_eq {U V W : X.Opens}
    [Nonempty U] [Nonempty V] [Nonempty W]
    (i : W ⟶ U) (j : W ⟶ V) (s : Γ(X, U)) (t : Γ(X, V))
    (h : X.germToFunctionField U s = X.germToFunctionField V t) :
    X.presheaf.map i.op s = X.presheaf.map j.op t := by
  apply X.germToFunctionField_injective W
  simpa only [generic_germ_restrict] using h

/-- Unit representatives in different coordinate rings agree as units on
common nonempty subopens whenever they represent the same rational function. -/
theorem unit_restrict_eq_of_generic_eq {U V W : X.Opens}
    [Nonempty U] [Nonempty V] [Nonempty W]
    (i : W ⟶ U) (j : W ⟶ V) (s : Γ(X, U)ˣ) (t : Γ(X, V)ˣ)
    (h : X.germToFunctionField U (s : Γ(X, U)) =
      X.germToFunctionField V (t : Γ(X, V))) :
    Units.map (X.presheaf.map i.op).hom.toMonoidHom s =
      Units.map (X.presheaf.map j.op).hom.toMonoidHom t := by
  apply Units.ext
  exact regular_restrict_eq_of_generic_eq X i j _ _ h

/-- A rational function whose positive power is an invertible regular
function extends uniquely to an invertible regular function on an affine
open whose coordinate ring is integrally closed. -/
theorem existsUnique_regular_unit_of_generic_pow_eq
    (U : X.Opens) [Nonempty U] (hU : IsAffineOpen U)
    [IsIntegrallyClosed Γ(X, U)] (r : X.functionField) (u : Γ(X, U)ˣ)
    {n : ℕ} (hn : 0 < n)
    (hr : r ^ n = X.germToFunctionField U (u : Γ(X, U))) :
    ∃! v : Γ(X, U)ˣ,
      X.germToFunctionField U (v : Γ(X, U)) = r ∧ v ^ n = u := by
  letI : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  obtain ⟨v, hv, hvn⟩ := exists_unit_of_fraction_pow_eq_unit r u hn hr
  refine ⟨v, ⟨hv, hvn⟩, ?_⟩
  intro w hw
  apply Units.ext
  apply X.germToFunctionField_injective U
  exact hw.1.trans hv.symm

/-- The local quotient lemma is now applied to actual sections of the
structure sheaf and their images in the scheme's actual function field. -/
theorem existsUnique_regular_unit_of_generic_sq_ratio
    (U : X.Opens) [Nonempty U] (hU : IsAffineOpen U)
    [IsIntegrallyClosed Γ(X, U)] (r q : X.functionField) (hq : q ≠ 0)
    (u v : Γ(X, U)ˣ)
    (h : X.germToFunctionField U (u : Γ(X, U)) * r ^ 2 =
      X.germToFunctionField U (v : Γ(X, U)) * q ^ 2) :
    ∃! w : Γ(X, U)ˣ,
      X.germToFunctionField U (w : Γ(X, U)) = r / q ∧ u * w ^ 2 = v := by
  letI : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  obtain ⟨w, hw, hw2⟩ :=
    exists_unit_of_unit_mul_fraction_sq_eq_unit_mul_sq r q hq u v h
  refine ⟨w, ⟨hw, hw2⟩, ?_⟩
  intro z hz
  apply Units.ext
  apply X.germToFunctionField_injective U
  exact hz.1.trans hw.symm

end EvenQuinticConic
