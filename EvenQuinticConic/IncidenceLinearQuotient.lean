import EvenQuinticConic.IncidenceLinearElimination

/-!
# The actual quotient after eliminating an affine linear equation

A nonzero selected linear coefficient lets us solve for that variable.
The resulting isomorphism of the two-equation quotient with the residual
one-equation quotient is constructed from the literal substitutions in
both directions. The second equation may be zero or otherwise degenerate.
-/

noncomputable section
namespace EvenQuinticConic.Incidence
open MvPolynomial

variable {F : Type*} [Field F] {n : ℕ}

/-- The actual ideal of the affine linear equation and the second equation. -/
def affineLinearEquationIdeal (a : Fin (n + 1) → F) (c : F)
    (Q : MvPolynomial (Fin (n + 1)) F) : Ideal (MvPolynomial (Fin (n + 1)) F) :=
  Ideal.span {affineLinearPolynomial a c, Q}

/-- The actual remaining equation after solving for the selected variable. -/
def affineResidualEquationIdeal (a : Fin (n + 1) → F) (c : F)
    (r : Fin (n + 1)) (Q : MvPolynomial (Fin (n + 1)) F) :
    Ideal (MvPolynomial (Fin n) F) :=
  Ideal.span {affineEliminationSubstitution a c r Q}

/-- Solving the linear equation and then restoring all retained variables
has the original quotient class, for every polynomial. -/
theorem affineLinearEquationIdeal_mk_restore
    (a : Fin (n + 1) → F) (c : F) (r : Fin (n + 1)) (ha : a r ≠ 0)
    (Q P : MvPolynomial (Fin (n + 1)) F) :
    Ideal.Quotient.mk (affineLinearEquationIdeal a c Q)
      (rename r.succAbove (affineEliminationSubstitution a c r P)) =
      Ideal.Quotient.mk (affineLinearEquationIdeal a c Q) P := by
  symm
  apply Ideal.Quotient.eq.mpr
  obtain ⟨U, hU⟩ := affineLinearPolynomial_dvd_sub_elimination a c r ha P
  rw [hU]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))

/-- Eliminating an already restored polynomial is the identity on the
retained-coordinate polynomial algebra. -/
@[simp] theorem affineEliminationSubstitution_rename
    (a : Fin (n + 1) → F) (c : F) (r : Fin (n + 1))
    (P : MvPolynomial (Fin n) F) :
    affineEliminationSubstitution a c r (rename r.succAbove P) = P := by
  have he : (affineEliminationSubstitution a c r).comp (rename r.succAbove) =
      AlgHom.id F (MvPolynomial (Fin n) F) := by
    ext j
    simp
  exact AlgHom.congr_fun he P

/-- The forward literal substitution factors through the two actual ideals. -/
def affineLinearQuotientForward
    (a : Fin (n + 1) → F) (c : F) (r : Fin (n + 1)) (ha : a r ≠ 0)
    (Q : MvPolynomial (Fin (n + 1)) F) :
    (MvPolynomial (Fin (n + 1)) F ⧸ affineLinearEquationIdeal a c Q) →ₐ[F]
      (MvPolynomial (Fin n) F ⧸ affineResidualEquationIdeal a c r Q) :=
  Ideal.Quotient.liftₐ _
    ((Ideal.Quotient.mkₐ F _).comp (affineEliminationSubstitution a c r)) (by
      have hker : affineLinearEquationIdeal a c Q ≤
          RingHom.ker (((Ideal.Quotient.mkₐ F (affineResidualEquationIdeal a c r Q)).comp
            (affineEliminationSubstitution a c r)).toRingHom) := by
        rw [affineLinearEquationIdeal, Ideal.span_le]
        intro P hP
        rcases Set.mem_insert_iff.mp hP with rfl | hP
        · change Ideal.Quotient.mk _
            (affineEliminationSubstitution a c r (affineLinearPolynomial a c)) = 0
          rw [affineEliminationSubstitution_linear a c r ha, map_zero]
        · rcases Set.mem_singleton_iff.mp hP with rfl
          exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
      intro P hP
      exact RingHom.mem_ker.mp (hker hP))

/-- Restoring retained variables factors through the residual equation,
because its restored value differs from the original equation by the linear one. -/
def affineLinearQuotientBackward
    (a : Fin (n + 1) → F) (c : F) (r : Fin (n + 1)) (ha : a r ≠ 0)
    (Q : MvPolynomial (Fin (n + 1)) F) :
    (MvPolynomial (Fin n) F ⧸ affineResidualEquationIdeal a c r Q) →ₐ[F]
      (MvPolynomial (Fin (n + 1)) F ⧸ affineLinearEquationIdeal a c Q) :=
  Ideal.Quotient.liftₐ _
    ((Ideal.Quotient.mkₐ F _).comp (rename r.succAbove)) (by
      have hker : affineResidualEquationIdeal a c r Q ≤
          RingHom.ker (((Ideal.Quotient.mkₐ F (affineLinearEquationIdeal a c Q)).comp
            (rename r.succAbove)).toRingHom) := by
        rw [affineResidualEquationIdeal, Ideal.span_le]
        intro P hP
        rcases Set.mem_singleton_iff.mp hP with rfl
        change Ideal.Quotient.mk _
          (rename r.succAbove (affineEliminationSubstitution a c r Q)) = 0
        rw [affineLinearEquationIdeal_mk_restore a c r ha Q Q]
        exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
      intro P hP
      exact RingHom.mem_ker.mp (hker hP))

@[simp] theorem affineLinearQuotientForward_mk
    (a : Fin (n + 1) → F) (c : F) (r : Fin (n + 1)) (ha : a r ≠ 0)
    (Q P : MvPolynomial (Fin (n + 1)) F) :
    affineLinearQuotientForward a c r ha Q (Ideal.Quotient.mk _ P) =
      Ideal.Quotient.mk _ (affineEliminationSubstitution a c r P) := rfl

@[simp] theorem affineLinearQuotientBackward_mk
    (a : Fin (n + 1) → F) (c : F) (r : Fin (n + 1)) (ha : a r ≠ 0)
    (Q : MvPolynomial (Fin (n + 1)) F) (P : MvPolynomial (Fin n) F) :
    affineLinearQuotientBackward a c r ha Q (Ideal.Quotient.mk _ P) =
      Ideal.Quotient.mk _ (rename r.succAbove P) := rfl

/-- Eliminating a genuine nonzero affine linear coefficient identifies the
actual two-equation quotient with the actual residual hypersurface quotient.
No nonvanishing, irreducibility, radicality or domain property of `Q` is needed. -/
def affineLinearQuotientAlgEquiv
    (a : Fin (n + 1) → F) (c : F) (r : Fin (n + 1)) (ha : a r ≠ 0)
    (Q : MvPolynomial (Fin (n + 1)) F) :
    (MvPolynomial (Fin (n + 1)) F ⧸ affineLinearEquationIdeal a c Q) ≃ₐ[F]
      (MvPolynomial (Fin n) F ⧸ affineResidualEquationIdeal a c r Q) :=
  AlgEquiv.ofAlgHom (affineLinearQuotientForward a c r ha Q)
    (affineLinearQuotientBackward a c r ha Q)
    (by
      apply Ideal.Quotient.algHom_ext
      apply AlgHom.ext
      intro P
      simp)
    (by
      apply Ideal.Quotient.algHom_ext
      apply AlgHom.ext
      intro P
      exact affineLinearEquationIdeal_mk_restore a c r ha Q P)

/-- On every original polynomial, the quotient equivalence is exactly the
already defined elimination substitution. -/
@[simp] theorem affineLinearQuotientAlgEquiv_mk
    (a : Fin (n + 1) → F) (c : F) (r : Fin (n + 1)) (ha : a r ≠ 0)
    (Q P : MvPolynomial (Fin (n + 1)) F) :
    affineLinearQuotientAlgEquiv a c r ha Q (Ideal.Quotient.mk _ P) =
      Ideal.Quotient.mk _ (affineEliminationSubstitution a c r P) := rfl

@[simp] theorem affineLinearQuotientAlgEquiv_symm_mk
    (a : Fin (n + 1) → F) (c : F) (r : Fin (n + 1)) (ha : a r ≠ 0)
    (Q : MvPolynomial (Fin (n + 1)) F) (P : MvPolynomial (Fin n) F) :
    (affineLinearQuotientAlgEquiv a c r ha Q).symm (Ideal.Quotient.mk _ P) =
      Ideal.Quotient.mk _ (rename r.succAbove P) := rfl

@[simp] theorem affineLinearQuotientAlgEquiv_coordinate
    (a : Fin (n + 1) → F) (c : F) (r : Fin (n + 1)) (ha : a r ≠ 0)
    (Q : MvPolynomial (Fin (n + 1)) F) (j : Fin n) :
    affineLinearQuotientAlgEquiv a c r ha Q (Ideal.Quotient.mk _ (X (r.succAbove j))) =
      Ideal.Quotient.mk _ (X j) := by simp

@[simp] theorem affineLinearQuotientAlgEquiv_pivot
    (a : Fin (n + 1) → F) (c : F) (r : Fin (n + 1)) (ha : a r ≠ 0)
    (Q : MvPolynomial (Fin (n + 1)) F) :
    affineLinearQuotientAlgEquiv a c r ha Q (Ideal.Quotient.mk _ (X r)) =
      Ideal.Quotient.mk _ (affineEliminatedCoordinate a c r) := by simp

end EvenQuinticConic.Incidence
