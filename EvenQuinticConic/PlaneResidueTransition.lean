import EvenQuinticConic.PlaneDifferentialIdentities
import EvenQuinticConic.GradedRestriction
import Mathlib.RingTheory.MvPolynomial.EulerIdentity

/-!
# The degree-two transition of actual quintic residue differentials

Rescaling homogeneous coordinates by an inverse unit rescales a quintic
partial derivative by its fourth power. The derivative of the inverse
coordinate supplies the remaining inverse square. These statements are
identities in the actual Kähler module, including rings with zero divisors.

The common-derivative case of projective chart changes is established here.
The radial-derivative case is proved in `PlaneResidueCrossTransition`.
Instantiating all overlaps and gluing frames inside the actual differential
sheaf still requires transporting the affine comparison to chart restrictions.
-/

noncomputable section

namespace EvenQuinticConic

open MvPolynomial

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- The rescaled unit is the actual derivative evaluated at the normalized
homogeneous coordinates, not an independently chosen transition factor. -/
theorem quintic_scaled_derivative_unit
    (F : MvPolynomial (Fin 3) R) (hF : F.IsHomogeneous 5)
    (v : Fin 3 → S) (j : Fin 3) (u t : Sˣ)
    (ht : (t : S) = aeval v (pderiv j F)) :
    (↑(t * (u⁻¹) ^ 4) : S) =
      aeval (fun a => v a * (↑u⁻¹ : S)) (pderiv j F) := by
  rw [aeval_def, homogeneous_eval₂_scale _ _ _ _ 4
    (by simpa using hF.pderiv (i := j))]
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, ht, aeval_def]

/-- The two signed inverse-coordinate residue expressions differ by the
square of the coordinate unit. -/
theorem kaehler_unit_residue_transition (u t : Sˣ) :
    -((↑(t * (u⁻¹) ^ 4)⁻¹ : S) • KaehlerDifferential.D R S (↑u⁻¹ : S)) =
      (u : S) ^ 2 • ((↑t⁻¹ : S) • KaehlerDifferential.D R S (u : S)) := by
  rw [derivation_unit_inverse, smul_neg, neg_neg, smul_smul, smul_smul]
  have hpow : u ^ 4 * (u⁻¹) ^ 2 = u ^ 2 := by
    calc
      u ^ 4 * (u⁻¹) ^ 2 = u ^ 2 * (u ^ 2 * (u⁻¹) ^ 2) := by
        rw [← mul_assoc, ← pow_add]
      _ = u ^ 2 := by rw [← mul_pow, mul_inv_cancel, one_pow, mul_one]
  have h : (t * (u⁻¹) ^ 4)⁻¹ * (u⁻¹) ^ 2 = u ^ 2 * t⁻¹ := by
    rw [mul_inv_rev, inv_pow, inv_inv, mul_right_comm, hpow]
  have hc := congrArg (fun a : Sˣ => (a : S)) h
  simpa only [Units.val_mul, Units.val_pow_eq_pow_val] using
    congrArg (fun a : S => a • KaehlerDifferential.D R S (u : S)) hc

/-- For two actual normalized coordinate systems, the chosen rescaled unit
is their common partial derivative and the actual residue differential has
exactly the degree-two transition expected for a plane quintic. -/
theorem quintic_residue_transition_common_derivative
    (F : MvPolynomial (Fin 3) R) (hF : F.IsHomogeneous 5)
    (v : Fin 3 → S) (i l j : Fin 3) (hvi : v i = 1)
    (u t : Sˣ) (hu : (u : S) = v l)
    (ht : (t : S) = aeval v (pderiv j F)) :
    (↑(t * (u⁻¹) ^ 4) : S) =
        aeval (fun a => v a * (↑u⁻¹ : S)) (pderiv j F) ∧
      -((↑(t * (u⁻¹) ^ 4)⁻¹ : S) •
          KaehlerDifferential.D R S (v i * (↑u⁻¹ : S))) =
        (v l) ^ 2 • ((↑t⁻¹ : S) • KaehlerDifferential.D R S (v l)) := by
  refine ⟨quintic_scaled_derivative_unit F hF v j u t ht, ?_⟩
  simpa only [hvi, one_mul, hu] using kaehler_unit_residue_transition (R := R) u t

end EvenQuinticConic
