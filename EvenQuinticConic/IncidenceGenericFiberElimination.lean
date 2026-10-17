import EvenQuinticConic.IncidenceGenericFiberPresentation
import EvenQuinticConic.IncidenceLinearQuotient
import EvenQuinticConic.IncidenceConicDehomogenization

/-!
# Actual elimination in the generic incidence-fiber presentation

The base-changed incidence equations are identified coefficient by coefficient
with the polar linear equation and the spatial quadratic of the actual generic
matrix. Eliminating a nonzero affine polar coefficient therefore gives an
explicit quotient in two variables over the actual parameter field.
-/

noncomputable section
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
namespace EvenQuinticConic.Incidence
open MvPolynomial

variable {K : Type*} [Field K]

/-- Extension of coefficients commutes with setting the chosen homogeneous
coordinate to one. -/
theorem map_dehomogenizeAt {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) {n : ℕ} (p : Fin (n + 1)) (P : MvPolynomial (Fin (n + 1)) R) :
    MvPolynomial.map f (dehomogenizeAt p P) =
      dehomogenizeAt p (MvPolynomial.map f P) := by
  have he : (MvPolynomial.map f).comp (dehomogenizeAt p).toRingHom =
      (dehomogenizeAt p).toRingHom.comp (MvPolynomial.map f) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp
    · intro i
      obtain rfl | ⟨j, rfl⟩ := Fin.eq_self_or_eq_succAbove p i
      · simp
      · simp
  exact RingHom.congr_fun he P

/-- The three actual affine coefficients of the generic polar equation. -/
def incidenceGenericAffineLinearCoefficients
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4)
    (h : (cross (segreChartRow (netLinearRow M) k p)
      (segreChartRow (netQuadraticRow M) k p)).z ≠ 0) :
    Fin 3 → incidenceParameterSubfield M k p h :=
  fun j => incidenceGenericMatrix M k p h (p.succAbove j).succ 0

/-- The actual constant coefficient of the affine polar equation. -/
def incidenceGenericAffineLinearConstant
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4)
    (h : (cross (segreChartRow (netLinearRow M) k p)
      (segreChartRow (netQuadraticRow M) k p)).z ≠ 0) :
    incidenceParameterSubfield M k p h :=
  incidenceGenericMatrix M k p h p.succ 0

/-- The actual spatial quadratic in the original chosen affine chart. -/
def incidenceGenericAffineQuadratic
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4)
    (h : (cross (segreChartRow (netLinearRow M) k p)
      (segreChartRow (netQuadraticRow M) k p)).z ≠ 0) :
    MvPolynomial (Fin 3) (incidenceParameterSubfield M k p h) :=
  dehomogenizeAt p (matrixQuadraticPolynomial (fun i j : Fin 4 =>
    incidenceGenericMatrix M k p h i.succ j.succ))

/-- The homogeneous polar row of the actual generic matrix is the actual
parameter combination of the original net rows. -/
theorem incidenceGenericMatrix_linearPolynomial
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4)
    (h : (cross (segreChartRow (netLinearRow M) k p)
      (segreChartRow (netQuadraticRow M) k p)).z ≠ 0) :
    coefficientLinearPolynomial (fun j : Fin 4 => incidenceGenericMatrix M k p h j.succ 0) =
      ∑ i : Fin 3, C (incidenceGenericParameter M k p h i) *
        MvPolynomial.map (algebraMap K (incidenceParameterSubfield M k p h)) (netLinearRow M i) := by
  simp only [coefficientLinearPolynomial, incidenceGenericMatrix_entry, map_sum, map_mul,
    netLinearRow, coefficientLinearPolynomial, MvPolynomial.map_C, MvPolynomial.map_X,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The corresponding homogeneous quadratic identity is also an exact
polynomial identity, not just a relation at the generic spatial point. -/
theorem incidenceGenericMatrix_spatialQuadraticPolynomial
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4)
    (h : (cross (segreChartRow (netLinearRow M) k p)
      (segreChartRow (netQuadraticRow M) k p)).z ≠ 0) :
    matrixQuadraticPolynomial (fun i j : Fin 4 => incidenceGenericMatrix M k p h i.succ j.succ) =
      ∑ i : Fin 3, C (incidenceGenericParameter M k p h i) *
        MvPolynomial.map (algebraMap K (incidenceParameterSubfield M k p h)) (netQuadraticRow M i) := by
  simp only [matrixQuadraticPolynomial, incidenceGenericMatrix_entry, map_sum, map_mul,
    netQuadraticRow, matrixQuadraticPolynomial, MvPolynomial.map_C, MvPolynomial.map_X,
    Finset.sum_mul, Finset.mul_sum]
  conv_lhs =>
    arg 2
    ext i
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro l _
  ring

/-- The first actual base-changed equation is precisely the affine linear
polynomial with the displayed actual generic-matrix coefficients. -/
theorem incidenceBaseChangedLinear_eq_genericAffine
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4)
    (h : (cross (segreChartRow (netLinearRow M) k p)
      (segreChartRow (netQuadraticRow M) k p)).z ≠ 0) :
    letI := incidenceParameterSubfieldPolynomialAlgebra M k p h
    incidenceBaseChangedRow (incidenceParameterSubfield M k p h)
        (segreChartRow (netLinearRow M) k p) =
      affineLinearPolynomial (incidenceGenericAffineLinearCoefficients M k p h)
        (incidenceGenericAffineLinearConstant M k p h) := by
  letI := incidenceParameterSubfieldPolynomialAlgebra M k p h
  rw [incidenceBaseChangedRow_actualParameter]
  simp_rw [map_dehomogenizeAt]
  have he := congrArg (dehomogenizeAt (K := incidenceParameterSubfield M k p h) p)
    (incidenceGenericMatrix_linearPolynomial M k p h)
  simp only [map_sum, map_mul, dehomogenizeAt_C] at he
  rw [← he]
  simp only [coefficientLinearPolynomial, map_sum, map_mul, dehomogenizeAt_C]
  rw [Fin.sum_univ_succAbove _ p]
  simp only [dehomogenizeAt_X_pivot, mul_one, dehomogenizeAt_X_succAbove,
    affineLinearPolynomial, incidenceGenericAffineLinearCoefficients,
    incidenceGenericAffineLinearConstant]
  ring

/-- The second actual base-changed equation is precisely the dehomogenized
spatial quadratic polynomial of the actual generic matrix. -/
theorem incidenceBaseChangedQuadratic_eq_genericAffine
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4)
    (h : (cross (segreChartRow (netLinearRow M) k p)
      (segreChartRow (netQuadraticRow M) k p)).z ≠ 0) :
    letI := incidenceParameterSubfieldPolynomialAlgebra M k p h
    incidenceBaseChangedRow (incidenceParameterSubfield M k p h)
        (segreChartRow (netQuadraticRow M) k p) =
      incidenceGenericAffineQuadratic M k p h := by
  letI := incidenceParameterSubfieldPolynomialAlgebra M k p h
  rw [incidenceBaseChangedRow_actualParameter, incidenceGenericAffineQuadratic,
    incidenceGenericMatrix_spatialQuadraticPolynomial]
  simp only [map_sum, map_mul, dehomogenizeAt_C, map_dehomogenizeAt]

/-- The explicit residual polynomial after eliminating the selected actual
nonpivot spatial coordinate. -/
def incidenceGenericResidualPolynomial
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4)
    (h : (cross (segreChartRow (netLinearRow M) k p)
      (segreChartRow (netQuadraticRow M) k p)).z ≠ 0) (q : Fin 3) :
    MvPolynomial (Fin 2) (incidenceParameterSubfield M k p h) :=
  affineEliminationSubstitution (incidenceGenericAffineLinearCoefficients M k p h)
    (incidenceGenericAffineLinearConstant M k p h) q (incidenceGenericAffineQuadratic M k p h)

/-- The actual residual affine hypersurface coordinate algebra. -/
abbrev IncidenceGenericResidualAlgebra
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4)
    (h : (cross (segreChartRow (netLinearRow M) k p)
      (segreChartRow (netQuadraticRow M) k p)).z ≠ 0) (q : Fin 3) :=
  MvPolynomial (Fin 2) (incidenceParameterSubfield M k p h) ⧸
    Ideal.span {incidenceGenericResidualPolynomial M k p h q}

/-- The actual two-equation generic-fiber presentation is the actual
residual hypersurface quotient, by the specified elimination substitution. -/
def incidenceGenericFiberEliminationEquiv
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4)
    (h : (cross (segreChartRow (netLinearRow M) k p)
      (segreChartRow (netQuadraticRow M) k p)).z ≠ 0)
    (q : Fin 3) (hq : incidenceGenericMatrix M k p h (p.succAbove q).succ 0 ≠ 0) :
    letI := incidenceParameterSubfieldPolynomialAlgebra M k p h
    IncidenceBaseChangedAlgebra (incidenceParameterSubfield M k p h) M k p
      ≃ₐ[incidenceParameterSubfield M k p h] IncidenceGenericResidualAlgebra M k p h q := by
  letI := incidenceParameterSubfieldPolynomialAlgebra M k p h
  have hid : Ideal.span
      {incidenceBaseChangedRow (incidenceParameterSubfield M k p h)
          (segreChartRow (netLinearRow M) k p),
        incidenceBaseChangedRow (incidenceParameterSubfield M k p h)
          (segreChartRow (netQuadraticRow M) k p)} =
      affineLinearEquationIdeal (incidenceGenericAffineLinearCoefficients M k p h)
        (incidenceGenericAffineLinearConstant M k p h) (incidenceGenericAffineQuadratic M k p h) := by
    rw [incidenceBaseChangedLinear_eq_genericAffine, incidenceBaseChangedQuadratic_eq_genericAffine]
    rfl
  exact (Ideal.quotientEquivAlgOfEq (incidenceParameterSubfield M k p h) hid).trans
    (affineLinearQuotientAlgEquiv (incidenceGenericAffineLinearCoefficients M k p h)
      (incidenceGenericAffineLinearConstant M k p h) q hq (incidenceGenericAffineQuadratic M k p h))

/-- Formula on every original spatial polynomial: the comparison is the
literal solved-coordinate substitution. -/
@[simp] theorem incidenceGenericFiberEliminationEquiv_mk
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4)
    (h : (cross (segreChartRow (netLinearRow M) k p)
      (segreChartRow (netQuadraticRow M) k p)).z ≠ 0)
    (q : Fin 3) (hq : incidenceGenericMatrix M k p h (p.succAbove q).succ 0 ≠ 0)
    (P : MvPolynomial (Fin 3) (incidenceParameterSubfield M k p h)) :
    letI := incidenceParameterSubfieldPolynomialAlgebra M k p h
    incidenceGenericFiberEliminationEquiv M k p h q hq (Ideal.Quotient.mk _ P) =
      Ideal.Quotient.mk _
        (affineEliminationSubstitution (incidenceGenericAffineLinearCoefficients M k p h)
          (incidenceGenericAffineLinearConstant M k p h) q P) := by
  letI := incidenceParameterSubfieldPolynomialAlgebra M k p h
  simp only [incidenceGenericFiberEliminationEquiv, AlgEquiv.trans_apply,
    Ideal.quotientEquivAlgOfEq_mk]
  rfl

/-- Every retained affine coordinate keeps its original order. -/
@[simp] theorem incidenceGenericFiberEliminationEquiv_coordinate
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4)
    (h : (cross (segreChartRow (netLinearRow M) k p)
      (segreChartRow (netQuadraticRow M) k p)).z ≠ 0)
    (q : Fin 3) (hq : incidenceGenericMatrix M k p h (p.succAbove q).succ 0 ≠ 0) (j : Fin 2) :
    letI := incidenceParameterSubfieldPolynomialAlgebra M k p h
    incidenceGenericFiberEliminationEquiv M k p h q hq (Ideal.Quotient.mk _ (X (q.succAbove j))) =
      Ideal.Quotient.mk _ (X j) := by
  letI := incidenceParameterSubfieldPolynomialAlgebra M k p h
  simp

/-- The eliminated coordinate has exactly the actual solved affine value. -/
@[simp] theorem incidenceGenericFiberEliminationEquiv_pivot
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4)
    (h : (cross (segreChartRow (netLinearRow M) k p)
      (segreChartRow (netQuadraticRow M) k p)).z ≠ 0)
    (q : Fin 3) (hq : incidenceGenericMatrix M k p h (p.succAbove q).succ 0 ≠ 0) :
    letI := incidenceParameterSubfieldPolynomialAlgebra M k p h
    incidenceGenericFiberEliminationEquiv M k p h q hq (Ideal.Quotient.mk _ (X q)) =
      Ideal.Quotient.mk _
        (affineEliminatedCoordinate (incidenceGenericAffineLinearCoefficients M k p h)
          (incidenceGenericAffineLinearConstant M k p h) q) := by
  letI := incidenceParameterSubfieldPolynomialAlgebra M k p h
  simp

/-- The selected actual minor in the residual quotient. -/
def incidenceGenericResidualMinor
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4)
    (h : (cross (segreChartRow (netLinearRow M) k p)
      (segreChartRow (netQuadraticRow M) k p)).z ≠ 0) (q : Fin 3) :
    IncidenceGenericResidualAlgebra M k p h q :=
  Ideal.Quotient.mk _
    (affineEliminationSubstitution (incidenceGenericAffineLinearCoefficients M k p h)
      (incidenceGenericAffineLinearConstant M k p h) q
      (MvPolynomial.map (algebraMap K (incidenceParameterSubfield M k p h))
        (netDehomogenizedMinor M p (k.succAbove 0) (k.succAbove 1))))

/-- The same actual minor defines the open before and after elimination. -/
@[simp] theorem incidenceGenericFiberEliminationEquiv_minor
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4)
    (h : (cross (segreChartRow (netLinearRow M) k p)
      (segreChartRow (netQuadraticRow M) k p)).z ≠ 0)
    (q : Fin 3) (hq : incidenceGenericMatrix M k p h (p.succAbove q).succ 0 ≠ 0) :
    letI := incidenceParameterSubfieldPolynomialAlgebra M k p h
    incidenceGenericFiberEliminationEquiv M k p h q hq
      (incidenceBaseChangedMinor (incidenceParameterSubfield M k p h) M k p) =
      incidenceGenericResidualMinor M k p h q := by
  letI := incidenceParameterSubfieldPolynomialAlgebra M k p h
  have hc : (algebraMap (IncidenceParameterPolynomialRing K)
      (incidenceParameterSubfield M k p h)).comp C =
      algebraMap K (incidenceParameterSubfield M k p h) := by
    apply RingHom.ext
    intro c
    change aeval (fun i : Fin 2 => incidenceGenericParameter M k p h (k.succAbove i)) (C c) = _
    simp
  rw [incidenceBaseChangedMinor, hc, incidenceGenericFiberEliminationEquiv_mk]
  rfl

private def awayAlgEquivOfElementEq
    {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (e : A ≃ₐ[R] B) (a : A) (b : B) (he : e a = b) :
    Localization.Away a ≃ₐ[R] Localization.Away b :=
  IsLocalization.algEquivOfAlgEquiv
    (M := Submonoid.powers a) (T := Submonoid.powers b)
    (Localization.Away a) (Localization.Away b) e
    ((Submonoid.map_powers e a).trans (congrArg Submonoid.powers he))

private theorem awayAlgEquivOfElementEq_algebraMap
    {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (e : A ≃ₐ[R] B) (a : A) (b : B) (he : e a = b) (x : A) :
    awayAlgEquivOfElementEq e a b he (algebraMap A (Localization.Away a) x) =
      algebraMap B (Localization.Away b) (e x) :=
  IsLocalization.algEquivOfAlgEquiv_eq _ x

/-- The elimination comparison restricts to the actual selected minor open. -/
def incidenceGenericFiberEliminationMinorEquiv
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4)
    (h : (cross (segreChartRow (netLinearRow M) k p)
      (segreChartRow (netQuadraticRow M) k p)).z ≠ 0)
    (q : Fin 3) (hq : incidenceGenericMatrix M k p h (p.succAbove q).succ 0 ≠ 0) :
    letI := incidenceParameterSubfieldPolynomialAlgebra M k p h
    Localization.Away (incidenceBaseChangedMinor (incidenceParameterSubfield M k p h) M k p)
      ≃ₐ[incidenceParameterSubfield M k p h]
        Localization.Away (incidenceGenericResidualMinor M k p h q) := by
  letI := incidenceParameterSubfieldPolynomialAlgebra M k p h
  exact awayAlgEquivOfElementEq (incidenceGenericFiberEliminationEquiv M k p h q hq)
    (incidenceBaseChangedMinor (incidenceParameterSubfield M k p h) M k p)
    (incidenceGenericResidualMinor M k p h q)
    (incidenceGenericFiberEliminationEquiv_minor M k p h q hq)

/-- On the original quotient coordinates the localized comparison is exactly
the proved elimination equivalence followed by localization. -/
@[simp] theorem incidenceGenericFiberEliminationMinorEquiv_algebraMap
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4)
    (h : (cross (segreChartRow (netLinearRow M) k p)
      (segreChartRow (netQuadraticRow M) k p)).z ≠ 0)
    (q : Fin 3) (hq : incidenceGenericMatrix M k p h (p.succAbove q).succ 0 ≠ 0) :
    letI := incidenceParameterSubfieldPolynomialAlgebra M k p h
    ∀ b : IncidenceBaseChangedAlgebra (incidenceParameterSubfield M k p h) M k p,
      incidenceGenericFiberEliminationMinorEquiv M k p h q hq (algebraMap _ _ b) =
        algebraMap _ _ (incidenceGenericFiberEliminationEquiv M k p h q hq b) := by
  letI := incidenceParameterSubfieldPolynomialAlgebra M k p h
  intro b
  exact awayAlgEquivOfElementEq_algebraMap _ _ _ _ b

/-- The residual polynomial is the dehomogenization of the actual restricted
ternary conic matrix, with exactly the same two retained coordinates. -/
theorem incidenceGenericResidualPolynomial_eq_conicDehom
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4)
    (h : (cross (segreChartRow (netLinearRow M) k p)
      (segreChartRow (netQuadraticRow M) k p)).z ≠ 0) (q : Fin 3) :
    incidenceGenericResidualPolynomial M k p h q =
      dehomogenizeAt (q.predAbove p)
        (matrixQuadraticPolynomial (incidenceGenericConicMatrix M k p h (p.succAbove q))) :=
  incidenceGenericConicMatrix_dehomogenize M k p h q

/-- Under the actual geometric assumptions the residual equation is not
the zero polynomial. Its nonvanishing is derived from the original net. -/
theorem incidenceGenericResidualPolynomial_ne_zero [Infinite K]
    (h2 : (2 : K) ≠ 0)
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (hM : ∀ i, (M i).IsSymm)
    (hbase : ∀ i, M i 0 0 = 0)
    (hCert : ProjectiveJacobianCertificate (linearMatrixNet M).det)
    (k : Fin 3) (p : Fin 4)
    (h : (cross (segreChartRow (netLinearRow M) k p)
      (segreChartRow (netQuadraticRow M) k p)).z ≠ 0)
    (q : Fin 3) (hq : incidenceGenericMatrix M k p h (p.succAbove q).succ 0 ≠ 0) :
    incidenceGenericResidualPolynomial M k p h q ≠ 0 := by
  let F := incidenceParameterSubfield M k p h
  letI : Infinite F := Infinite.of_injective (algebraMap K F) (algebraMap K F).injective
  have h2F : (2 : F) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap K F)).mpr h2
  have ht : incidenceGenericParameter M k p h ≠ 0 := by
    intro hz
    have hk := congrFun hz k
    simp at hk
  have hadj : (incidenceGenericMatrix M k p h).adjugate ≠ 0 :=
    linearMatrixNet_adjugate_ne_zero_over_field M hCert (algebraMap K F)
      (incidenceGenericParameter M k p h) ht
  exact affineElimination_incidenceQuadratic_ne_zero h2F _
    (incidenceGenericMatrix_isSymm M hM k p h)
    (incidenceGenericMatrix_zero_zero M hbase k p h) hadj p q hq

/-- The geometric hypotheses choose a valid affine pivot and provide the
actual residual presentation, together with a nonsingular actual conic matrix.
The quotient isomorphism and all its input nonvanishing are constructed. -/
theorem exists_incidenceGenericFiberElimination [Infinite K]
    (h2 : (2 : K) ≠ 0)
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (hM : ∀ i, (M i).IsSymm)
    (hbase : ∀ i, M i 0 0 = 0)
    (hCert : ProjectiveJacobianCertificate (linearMatrixNet M).det)
    (k : Fin 3) (p : Fin 4)
    (h : (cross (segreChartRow (netLinearRow M) k p)
      (segreChartRow (netQuadraticRow M) k p)).z ≠ 0) :
    letI := incidenceParameterSubfieldPolynomialAlgebra M k p h
    ∃ q : Fin 3, incidenceGenericMatrix M k p h (p.succAbove q).succ 0 ≠ 0 ∧
      incidenceGenericResidualPolynomial M k p h q ≠ 0 ∧
      (incidenceGenericConicMatrix M k p h (p.succAbove q)).IsSymm ∧
      (incidenceGenericConicMatrix M k p h (p.succAbove q)).det ≠ 0 ∧
      Nonempty (IncidenceBaseChangedAlgebra (incidenceParameterSubfield M k p h) M k p
        ≃ₐ[incidenceParameterSubfield M k p h] IncidenceGenericResidualAlgebra M k p h q) := by
  letI := incidenceParameterSubfieldPolynomialAlgebra M k p h
  obtain ⟨q, hq, hs, hd⟩ :=
    exists_incidenceGenericConicMatrix_nondegenerate_affine h2 M hM hbase hCert k p h
  exact ⟨q, hq, incidenceGenericResidualPolynomial_ne_zero h2 M hM hbase hCert k p h q hq,
    hs, hd, ⟨incidenceGenericFiberEliminationEquiv M k p h q hq⟩⟩

end EvenQuinticConic.Incidence
