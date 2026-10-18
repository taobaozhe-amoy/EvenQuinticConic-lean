import EvenQuinticConic.IncidenceGenericFiberElimination

/-!
# Coefficient extension of the actual affine plane equation

The algebra compared here is the literal quotient by the dehomogenized
equation.  The equivalence preserves both coefficients and affine coordinate
classes; it requires no field, reducedness, or primality hypothesis.
-/

noncomputable section

namespace EvenQuinticConic

open MvPolynomial TensorProduct Incidence

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- The actual equation algebra on a standard projective plane chart. -/
abbrev PlaneEquationAlgebra (Q : MvPolynomial (Fin 3) R) (p : Fin 3) :=
  MvPolynomial (Fin 2) R ⧸ Ideal.span {dehomogenizeAt p Q}

/-- Extension of the literal affine defining ideal is the literal defining
ideal of the coefficient-extended homogeneous equation. -/
theorem planeEquationIdeal_map (Q : MvPolynomial (Fin 3) R) (p : Fin 3) :
    (Ideal.span {dehomogenizeAt p Q}).map (MvPolynomial.map (algebraMap R S)) =
      Ideal.span {dehomogenizeAt p (MvPolynomial.map (algebraMap R S) Q)} := by
  rw [Ideal.map_span, Set.image_singleton, map_dehomogenizeAt]

/-- The literal coefficient map between the two equation algebras. -/
def planeEquationCoefficientMap (Q : MvPolynomial (Fin 3) R) (p : Fin 3) :
    PlaneEquationAlgebra Q p →ₐ[R]
      PlaneEquationAlgebra (MvPolynomial.map (algebraMap R S) Q) p :=
  ((Ideal.quotientEquivAlgOfEq S (planeEquationIdeal_map Q p)).toAlgHom.restrictScalars R).comp
    (polynomialQuotientCoefficientMap (Ideal.span {dehomogenizeAt p Q}))

@[simp] theorem planeEquationCoefficientMap_mk
    (Q : MvPolynomial (Fin 3) R) (p : Fin 3) (P : MvPolynomial (Fin 2) R) :
    planeEquationCoefficientMap (S := S) Q p (Ideal.Quotient.mk _ P) =
      Ideal.Quotient.mk _ (MvPolynomial.map (algebraMap R S) P) := rfl

/-- Actual coefficient extension of a plane equation's affine chart. -/
def planeEquationBaseChangeEquiv (Q : MvPolynomial (Fin 3) R) (p : Fin 3) :
    S ⊗[R] PlaneEquationAlgebra Q p ≃ₐ[S]
      PlaneEquationAlgebra (MvPolynomial.map (algebraMap R S) Q) p :=
  (polynomialQuotientBaseChangeEquiv (Ideal.span {dehomogenizeAt p Q})).trans
    (Ideal.quotientEquivAlgOfEq S (planeEquationIdeal_map Q p))

/-- The original chart-algebra map is the right tensor inclusion under
the base-change comparison. -/
theorem planeEquationBaseChangeEquiv_includeRight
    (Q : MvPolynomial (Fin 3) R) (p : Fin 3) :
    ((planeEquationBaseChangeEquiv (S := S) Q p).toAlgHom.restrictScalars R).comp
        Algebra.TensorProduct.includeRight =
      planeEquationCoefficientMap Q p := by
  apply Ideal.Quotient.algHom_ext
  ext j
  simp [planeEquationBaseChangeEquiv, planeEquationCoefficientMap]

@[simp] theorem planeEquationBaseChangeEquiv_tmul_mk
    (Q : MvPolynomial (Fin 3) R) (p : Fin 3) (s : S)
    (P : MvPolynomial (Fin 2) R) :
    planeEquationBaseChangeEquiv Q p (s ⊗ₜ[R] Ideal.Quotient.mk _ P) =
      algebraMap S _ s * Ideal.Quotient.mk _ (MvPolynomial.map (algebraMap R S) P) := by
  simp [planeEquationBaseChangeEquiv]

@[simp] theorem planeEquationBaseChangeEquiv_coordinate
    (Q : MvPolynomial (Fin 3) R) (p : Fin 3) (j : Fin 2) :
    planeEquationBaseChangeEquiv (S := S) Q p
        (1 ⊗ₜ[R] Ideal.Quotient.mk _ (X j)) =
      Ideal.Quotient.mk _ (X j) := by
  simp

@[simp] theorem planeEquationBaseChangeEquiv_coefficient
    (Q : MvPolynomial (Fin 3) R) (p : Fin 3) (s : S) :
    planeEquationBaseChangeEquiv Q p
        (s ⊗ₜ[R] (1 : PlaneEquationAlgebra Q p)) =
      algebraMap S _ s := by
  simpa using planeEquationBaseChangeEquiv_tmul_mk Q p s 1

/-- The inverse comparison retains every displayed affine polynomial. -/
@[simp] theorem planeEquationBaseChangeEquiv_symm_mk_map
    (Q : MvPolynomial (Fin 3) R) (p : Fin 3)
    (P : MvPolynomial (Fin 2) R) :
    (planeEquationBaseChangeEquiv (S := S) Q p).symm
        (Ideal.Quotient.mk _ (MvPolynomial.map (algebraMap R S) P)) =
      1 ⊗ₜ[R] Ideal.Quotient.mk _ P := by
  apply (planeEquationBaseChangeEquiv Q p).injective
  simp

@[simp] theorem planeEquationBaseChangeEquiv_symm_coordinate
    (Q : MvPolynomial (Fin 3) R) (p : Fin 3) (j : Fin 2) :
    (planeEquationBaseChangeEquiv (S := S) Q p).symm
        (Ideal.Quotient.mk _ (X j)) =
      1 ⊗ₜ[R] Ideal.Quotient.mk _ (X j) := by
  apply (planeEquationBaseChangeEquiv Q p).injective
  simp

end EvenQuinticConic
