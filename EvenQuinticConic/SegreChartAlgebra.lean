import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Tactic.Ring

/-!
# The genuine standard affine chart of the Segre equations

The quotient by all two-by-two Segre minors and the equation setting one
Segre coordinate equal to one is explicitly a polynomial algebra in the
remaining coordinates of the two factors. Both maps and both inverse
identities are proved over an arbitrary commutative coefficient ring.
-/

noncomputable section

open MvPolynomial

namespace EvenQuinticConic.SegreChart

variable (R : Type*) [CommRing R]
variable {I J : Type*} [DecidableEq I] [DecidableEq J]

/-- The genuine homogeneous two-by-two minor in Segre coordinates. -/
def segreMinor (i i' : I) (j j' : J) : MvPolynomial (I × J) R :=
  X (i, j) * X (i', j') - X (i, j') * X (i', j)

/-- All Segre minors, together with the equation normalizing the chosen pivot. -/
def segreChartIdeal (k : I) (p : J) : Ideal (MvPolynomial (I × J) R) :=
  Ideal.span (Set.range (fun q : (I × I) × (J × J) =>
    segreMinor R q.1.1 q.1.2 q.2.1 q.2.2) ∪ {X (k, p) - 1})

/-- The coordinate algebra defined by the actual normalized Segre equations. -/
abbrev SegreChartAlgebra (k : I) (p : J) :=
  MvPolynomial (I × J) R ⧸ segreChartIdeal R k p

/-- Nonpivot affine coordinates on the two projective factors. -/
abbrev SegreChartVariables (k : I) (p : J) :=
  {i : I // i ≠ k} ⊕ {j : J // j ≠ p}

/-- Left factor coordinate, with the pivot normalized to one. -/
def segreChartLeftCoordinate (k : I) (p : J) (i : I) :
    MvPolynomial (SegreChartVariables k p) R :=
  if hi : i = k then 1 else X (Sum.inl ⟨i, hi⟩)

/-- Right factor coordinate, with the pivot normalized to one. -/
def segreChartRightCoordinate (k : I) (p : J) (j : J) :
    MvPolynomial (SegreChartVariables k p) R :=
  if hj : j = p then 1 else X (Sum.inr ⟨j, hj⟩)

omit [DecidableEq J] in
@[simp] theorem segreChartLeftCoordinate_pivot (k : I) (p : J) :
    segreChartLeftCoordinate R k p k = 1 := by
  simp [segreChartLeftCoordinate]

omit [DecidableEq I] in
@[simp] theorem segreChartRightCoordinate_pivot (k : I) (p : J) :
    segreChartRightCoordinate R k p p = 1 := by
  simp [segreChartRightCoordinate]

/-- The explicit factorization of a normalized Segre coordinate. -/
def segreChartEval (k : I) (p : J) :
    MvPolynomial (I × J) R →ₐ[R] MvPolynomial (SegreChartVariables k p) R :=
  aeval (fun q => segreChartLeftCoordinate R k p q.1 *
    segreChartRightCoordinate R k p q.2)

@[simp] theorem segreChartEval_X (k : I) (p : J) (i : I) (j : J) :
    segreChartEval R k p (X (i, j)) =
      segreChartLeftCoordinate R k p i * segreChartRightCoordinate R k p j := by
  simp [segreChartEval]

@[simp] theorem segreChartEval_minor (k : I) (p : J) (i i' : I) (j j' : J) :
    segreChartEval R k p (segreMinor R i i' j j') = 0 := by
  simp only [segreMinor, map_sub, map_mul, segreChartEval_X]
  ring

/-- The actual Segre equations vanish under the coordinate factorization. -/
theorem segreChartIdeal_le_ker (k : I) (p : J) :
    segreChartIdeal R k p ≤ RingHom.ker (segreChartEval R k p).toRingHom := by
  rw [segreChartIdeal, Ideal.span_le]
  intro f hf
  rcases hf with ⟨⟨⟨i, i'⟩, j, j'⟩, rfl⟩ | hf
  · exact segreChartEval_minor R k p i i' j j'
  · rcases Set.mem_singleton_iff.mp hf with rfl
    simp [RingHom.mem_ker]

/-- Factorization descends through the actual defining ideal. -/
def segreChartToPolynomial (k : I) (p : J) :
    SegreChartAlgebra R k p →ₐ[R] MvPolynomial (SegreChartVariables k p) R :=
  Ideal.Quotient.liftₐ (segreChartIdeal R k p) (segreChartEval R k p)
    (fun _ hf => segreChartIdeal_le_ker R k p hf)

@[simp] theorem segreChartToPolynomial_mk (k : I) (p : J)
    (f : MvPolynomial (I × J) R) :
    segreChartToPolynomial R k p (Ideal.Quotient.mk _ f) =
      segreChartEval R k p f := rfl

/-- Coordinates on the factors are read from the pivot row and pivot column. -/
def polynomialToSegreChart (k : I) (p : J) :
    MvPolynomial (SegreChartVariables k p) R →ₐ[R] SegreChartAlgebra R k p :=
  aeval (Sum.elim (fun i => Ideal.Quotient.mk _ (X (i.1, p)))
    (fun j => Ideal.Quotient.mk _ (X (k, j.1))))

omit [DecidableEq I] [DecidableEq J] in
@[simp] theorem segreChart_pivot_eq_one (k : I) (p : J) :
    Ideal.Quotient.mk (segreChartIdeal R k p) (X (k, p)) = 1 := by
  apply sub_eq_zero.mp
  rw [← map_one (Ideal.Quotient.mk _), ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (Or.inr (Set.mem_singleton _))

omit [DecidableEq I] [DecidableEq J] in
/-- The universal Segre matrix factors as its pivot column times its pivot row. -/
theorem segreChart_coordinate_factorization (k : I) (p : J) (i : I) (j : J) :
    Ideal.Quotient.mk (segreChartIdeal R k p) (X (i, j)) =
      Ideal.Quotient.mk (segreChartIdeal R k p) (X (i, p)) *
      Ideal.Quotient.mk (segreChartIdeal R k p) (X (k, j)) := by
  have hm : segreMinor R i k j p ∈ segreChartIdeal R k p :=
    Ideal.subset_span (Or.inl ⟨((i, k), (j, p)), rfl⟩)
  have hz := (Ideal.Quotient.eq_zero_iff_mem).mpr hm
  simpa [segreMinor, map_sub, map_mul, sub_eq_zero] using hz

omit [DecidableEq J] in
@[simp] theorem polynomialToSegreChart_left (k : I) (p : J) (i : I) :
    polynomialToSegreChart R k p (segreChartLeftCoordinate R k p i) =
      Ideal.Quotient.mk (segreChartIdeal R k p) (X (i, p)) := by
  by_cases hi : i = k
  · subst i
    simp
  · simp [segreChartLeftCoordinate, hi, polynomialToSegreChart]

omit [DecidableEq I] in
@[simp] theorem polynomialToSegreChart_right (k : I) (p : J) (j : J) :
    polynomialToSegreChart R k p (segreChartRightCoordinate R k p j) =
      Ideal.Quotient.mk (segreChartIdeal R k p) (X (k, j)) := by
  by_cases hj : j = p
  · subst j
    simp
  · simp [segreChartRightCoordinate, hj, polynomialToSegreChart]

/-- Substitution and quotient projection are inverse on the Segre chart. -/
theorem polynomialToSegreChart_comp (k : I) (p : J) :
    (polynomialToSegreChart R k p).comp (segreChartToPolynomial R k p) =
      AlgHom.id R (SegreChartAlgebra R k p) := by
  apply Ideal.Quotient.algHom_ext
  ext q
  rcases q with ⟨i, j⟩
  simpa using (segreChart_coordinate_factorization R k p i j).symm

/-- Quotient projection and substitution are inverse on both factors' coordinates. -/
theorem segreChartToPolynomial_comp (k : I) (p : J) :
    (segreChartToPolynomial R k p).comp (polynomialToSegreChart R k p) =
      AlgHom.id R (MvPolynomial (SegreChartVariables k p) R) := by
  ext q
  rcases q with i | j
  · simp [polynomialToSegreChart, segreChartLeftCoordinate, i.property]
  · simp [polynomialToSegreChart, segreChartRightCoordinate, j.property]

/-- Explicit algebra isomorphism for the actual standard Segre chart. -/
def segreChartAlgEquiv (k : I) (p : J) :
    SegreChartAlgebra R k p ≃ₐ[R] MvPolynomial (SegreChartVariables k p) R where
  toFun := segreChartToPolynomial R k p
  invFun := polynomialToSegreChart R k p
  left_inv x := AlgHom.congr_fun (polynomialToSegreChart_comp R k p) x
  right_inv x := AlgHom.congr_fun (segreChartToPolynomial_comp R k p) x
  map_mul' := (segreChartToPolynomial R k p).map_mul
  map_add' := (segreChartToPolynomial R k p).map_add
  commutes' := (segreChartToPolynomial R k p).commutes

@[simp] theorem segreChartAlgEquiv_mk (k : I) (p : J)
    (f : MvPolynomial (I × J) R) :
    segreChartAlgEquiv R k p (Ideal.Quotient.mk _ f) = segreChartEval R k p f := rfl

/-- The equations used above are the entire kernel of normalized substitution. -/
theorem segreChartEval_ker (k : I) (p : J) :
    RingHom.ker (segreChartEval R k p).toRingHom = segreChartIdeal R k p := by
  ext f
  rw [RingHom.mem_ker, ← Ideal.Quotient.eq_zero_iff_mem]
  change segreChartAlgEquiv R k p (Ideal.Quotient.mk _ f) = 0 ↔ _
  exact (segreChartAlgEquiv R k p).map_eq_zero_iff

/-- Every polynomial in the factor coordinates comes from a Segre polynomial. -/
theorem segreChartEval_surjective (k : I) (p : J) :
    Function.Surjective (segreChartEval R k p) := by
  intro f
  obtain ⟨g, hg⟩ := (segreChartAlgEquiv R k p).surjective f
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective g
  exact ⟨g, hg⟩

/-- Additional equations transport to exactly their normalized substitutions. -/
theorem segreChart_extraIdeal_map (k : I) (p : J)
    (E : Set (MvPolynomial (I × J) R)) :
    Ideal.span (segreChartEval R k p '' E) =
      ((Ideal.span E).map (Ideal.Quotient.mk (segreChartIdeal R k p))).map
        (segreChartAlgEquiv R k p).toRingHom := by
  rw [Ideal.map_map]
  change Ideal.span (segreChartEval R k p '' E) =
    (Ideal.span E).map (segreChartEval R k p).toRingHom
  rw [Ideal.map_span]
  rfl

/-- The standard Segre chart with any added equations is the quotient by their
actual substitutions. No equality of kernels or coordinate isomorphism is an
input to this construction. -/
def segreChartWithEquationsAlgEquiv (k : I) (p : J)
    (E : Set (MvPolynomial (I × J) R)) :
    (MvPolynomial (I × J) R ⧸ (segreChartIdeal R k p ⊔ Ideal.span E)) ≃ₐ[R]
      (MvPolynomial (SegreChartVariables k p) R ⧸
        Ideal.span (segreChartEval R k p '' E)) :=
  (DoubleQuot.quotQuotEquivQuotSupₐ R (segreChartIdeal R k p) (Ideal.span E)).symm.trans
    (Ideal.quotientEquivAlg _ _ (segreChartAlgEquiv R k p)
      (segreChart_extraIdeal_map R k p E))

/-- The isomorphism on an arbitrary polynomial is precisely normalized substitution. -/
@[simp] theorem segreChartWithEquationsAlgEquiv_mk (k : I) (p : J)
    (E : Set (MvPolynomial (I × J) R)) (f : MvPolynomial (I × J) R) :
    segreChartWithEquationsAlgEquiv R k p E (Ideal.Quotient.mk _ f) =
      Ideal.Quotient.mk _ (segreChartEval R k p f) := rfl

end EvenQuinticConic.SegreChart
