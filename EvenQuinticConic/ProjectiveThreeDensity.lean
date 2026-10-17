import EvenQuinticConic.IncidenceProjectiveChart
import Mathlib.Topology.Irreducible

/-!
# Density of the actual projective incidence open

The zero homogeneous prime is an actual point of projective three-space:
the irrelevant ideal is not contained in it, since a degree-one coordinate
is nonzero. Its closure is the whole projective spectrum. This proves
irreducibility of the actual ambient scheme and hence density of every
nonempty open constructed from the incidence equations.

Density here is in projective three-space. Identification with an open of a
global projective incidence scheme, and dominance over the parameter plane,
are not asserted by these statements.
-/

noncomputable section

namespace EvenQuinticConic.Incidence

open MvPolynomial AlgebraicGeometry

variable {K : Type*} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The zero ideal is a relevant homogeneous prime of the actual
homogeneous coordinate ring of projective three-space. -/
def projectiveThreeZeroPrime :
    ProjectiveSpectrum (homogeneousSubmodule (Fin 4) K) where
  asHomogeneousIdeal := ⊥
  isPrime := by simpa only [HomogeneousIdeal.toIdeal_bot] using
    (Ideal.bot_prime : (⊥ : Ideal (MvPolynomial (Fin 4) K)).IsPrime)
  not_irrelevant_le := by
    intro hle
    have hx : (X (0 : Fin 4) : MvPolynomial (Fin 4) K) ∈
        HomogeneousIdeal.irrelevant (homogeneousSubmodule (Fin 4) K) := by
      rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply]
      exact DirectSum.decompose_of_mem_ne (homogeneousSubmodule (Fin 4) K)
        (isHomogeneous_X K 0) (by decide : (1 : ℕ) ≠ 0)
    have hz : (X (0 : Fin 4) : MvPolynomial (Fin 4) K) ∈
        (⊥ : Ideal (MvPolynomial (Fin 4) K)) := hle hx
    exact X_ne_zero (0 : Fin 4) (Ideal.mem_bot.mp hz)

/-- The actual homogeneous zero prime is a generic point of projective
three-space, as witnessed by its closure rather than assumed generically. -/
theorem closure_projectiveThreeZeroPrime :
    closure ({projectiveThreeZeroPrime (K := K)} :
      Set (ProjectiveSpectrum (homogeneousSubmodule (Fin 4) K))) = Set.univ := by
  rw [← ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure,
    ProjectiveSpectrum.vanishingIdeal_singleton]
  change ProjectiveSpectrum.zeroLocus (homogeneousSubmodule (Fin 4) K)
    ((⊥ : Ideal (MvPolynomial (Fin 4) K)) : Set (MvPolynomial (Fin 4) K)) = _
  exact ProjectiveSpectrum.zeroLocus_bot _

/-- The actual projective three-space scheme is irreducible. -/
theorem projectiveThreeScheme_irreducibleSpace :
    IrreducibleSpace (ProjectiveThreeScheme K) := by
  apply (irreducibleSpace_def _).mpr
  change IsIrreducible
    (Set.univ : Set (ProjectiveSpectrum (homogeneousSubmodule (Fin 4) K)))
  rw [← closure_projectiveThreeZeroPrime]
  exact isIrreducible_singleton.closure

/-- A nonempty actual projective open is dense; the ambient irreducibility
is proved above and is not supplied as a hypothesis. -/
theorem projectiveThreeOpen_dense (U : (ProjectiveThreeScheme K).Opens)
    (hU : Nonempty U) : Dense (U : Set (ProjectiveThreeScheme K)) := by
  letI := projectiveThreeScheme_irreducibleSpace (K := K)
  obtain ⟨x⟩ := hU
  exact U.isOpen.dense ⟨x.1, x.2⟩

/-- The actual open given by the incidence minor is dense whenever it is
nonempty. This concerns the explicitly identified projective open. -/
theorem netProjectiveIncidenceOpen_dense_of_nonempty
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (p : Fin 4) (i j k : Fin 3)
    (h : Nonempty (netProjectiveIncidenceOpen M p i j k)) :
    Dense (netProjectiveIncidenceOpen M p i j k : Set (ProjectiveThreeScheme K)) :=
  projectiveThreeOpen_dense _ h

/-- A nonzero evaluation of the original homogeneous minor proves density
of its actual projective open, not only nonemptiness of a polynomial chart. -/
theorem netProjectiveIncidenceOpen_dense_of_eval
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (p : Fin 4) (i j k : Fin 3)
    (y : Fin 4 → K) (hyp : y p ≠ 0) (hy : eval y (netIncidenceMinor M i j) ≠ 0) :
    Dense (netProjectiveIncidenceOpen M p i j k : Set (ProjectiveThreeScheme K)) :=
  netProjectiveIncidenceOpen_dense_of_nonempty M p i j k
    (netProjectiveIncidenceOpen_nonempty_of_eval M p i j k y hyp hy)

end EvenQuinticConic.Incidence
