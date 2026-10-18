import EvenQuinticConic.HomogeneousFactors
import EvenQuinticConic.IncidenceDehomogenization
import EvenQuinticConic.ThetaSectionBridge

/-!
# Irreducibility of the actual nondegenerate ternary quadratic equation

Over any field of characteristic different from two, a symmetric three-by-three
matrix with nonzero determinant defines an irreducible quadratic polynomial.
A nontrivial factorization would have two homogeneous linear factors, whose
Hessian has rank at most two. The conclusion concerns the actual principal
ideal, not only its radical or its field-valued zero set.
-/

noncomputable section

namespace EvenQuinticConic.Incidence

open MvPolynomial

variable {K : Type*} [Field K]

/-- A sum of two outer products in three variables has zero determinant. -/
theorem ternary_det_outer_sum_eq_zero (a b : Fin 3 → K) :
    Matrix.det (fun i j => a i * b j + b i * a j : Matrix (Fin 3) (Fin 3) K) = 0 := by
  rw [Matrix.det_fin_three]
  ring

/-- The Hessian of a polynomial with a homogeneous linear factor is singular
in three variables, regardless of the degree of the other factor. -/
theorem ternary_det_hessianAtZero_linear_mul
    (a : Fin 3 → K) (g : MvPolynomial (Fin 3) K) :
    (hessianAtZero (linearPolynomial a * g)).det = 0 := by
  have heq : hessianAtZero (linearPolynomial a * g) =
      (fun i j => a i * eval (fun _ => 0) (pderiv j g) +
        eval (fun _ => 0) (pderiv i g) * a j) := by
    ext i j
    rw [hessianAtZero_linear_mul]
    ring
  rw [heq]
  exact ternary_det_outer_sum_eq_zero a (fun i => eval (fun _ => 0) (pderiv i g))

/-- In characteristic different from two, a linear factor of a symmetric
ternary quadratic equation forces its matrix determinant to vanish. -/
theorem ternary_det_eq_zero_of_matrixQuadraticPolynomial_factor
    (h2 : (2 : K) ≠ 0) (M : Matrix (Fin 3) (Fin 3) K)
    (hM : M.IsSymm) (a : Fin 3 → K) (g : MvPolynomial (Fin 3) K)
    (hfactor : matrixQuadraticPolynomial M = linearPolynomial a * g) : M.det = 0 := by
  have hh := ternary_det_hessianAtZero_linear_mul a g
  rw [← hfactor, hessianAtZero_matrixQuadraticPolynomial, hM] at hh
  have hdouble : M + M = (2 : K) • M := by ext i j; simp [two_mul]
  rw [hdouble, Matrix.det_smul] at hh
  exact (mul_eq_zero.mp hh).resolve_left (pow_ne_zero _ h2)

/-- Nondegeneracy rules out the zero polynomial; the characteristic condition
is essential because the Hessian is twice the symmetric matrix. -/
theorem ternary_matrixQuadraticPolynomial_ne_zero
    (h2 : (2 : K) ≠ 0) (M : Matrix (Fin 3) (Fin 3) K)
    (hM : M.IsSymm) (hdet : M.det ≠ 0) : matrixQuadraticPolynomial M ≠ 0 := by
  intro hz
  apply hdet
  exact ternary_det_eq_zero_of_matrixQuadraticPolynomial_factor h2 M hM 0 0
    (by simpa using hz)

/-- The actual nondegenerate ternary equation has total degree exactly two. -/
theorem ternary_matrixQuadraticPolynomial_totalDegree
    (h2 : (2 : K) ≠ 0) (M : Matrix (Fin 3) (Fin 3) K)
    (hM : M.IsSymm) (hdet : M.det ≠ 0) :
    (matrixQuadraticPolynomial M).totalDegree = 2 :=
  (matrixQuadraticPolynomial_homogeneous M).totalDegree
    (ternary_matrixQuadraticPolynomial_ne_zero h2 M hM hdet)

/-- The actual quadratic equation of a nondegenerate symmetric ternary matrix
is irreducible over every field of characteristic different from two. -/
theorem ternary_matrixQuadraticPolynomial_irreducible
    (h2 : (2 : K) ≠ 0) (M : Matrix (Fin 3) (Fin 3) K)
    (hM : M.IsSymm) (hdet : M.det ≠ 0) :
    Irreducible (matrixQuadraticPolynomial M) := by
  have hdeg := ternary_matrixQuadraticPolynomial_totalDegree h2 M hM hdet
  have hzero := ternary_matrixQuadraticPolynomial_ne_zero h2 M hM hdet
  refine ⟨?_, ?_⟩
  · intro hu
    have hc := (isUnit_iff_totalDegree_of_isReduced.mp hu).2
    omega
  · intro G H hfactor
    by_contra hu
    push_neg at hu
    obtain ⟨A, B, a, b, ha, hb, hA, hB, hAB⟩ :=
      homogeneous_positive_factorization_of_nontrivial
        (matrixQuadraticPolynomial M) G H 2
        (matrixQuadraticPolynomial_homogeneous M) hzero hfactor hu.1 hu.2
    have hA0 : A ≠ 0 := by intro hz; apply hzero; simp [hAB, hz]
    have hB0 : B ≠ 0 := by intro hz; apply hzero; simp [hAB, hz]
    have hab : a + b = 2 := by
      rw [← hA.totalDegree hA0, ← hB.totalDegree hB0,
        ← totalDegree_mul_of_isDomain hA0 hB0, ← hAB]
      exact hdeg
    have ha1 : a = 1 := by omega
    have hlinear : A = linearPolynomial (fun i => A.coeff (Finsupp.single i 1)) := by
      simpa [linearPolynomial, smul_eq_C_mul] using
        homogeneous_linear_fin3_eq A (ha1 ▸ hA)
    exact hdet (ternary_det_eq_zero_of_matrixQuadraticPolynomial_factor
      h2 M hM _ B (by rw [← hlinear]; exact hAB))

/-- The principal ideal of the actual ternary equation is prime, with
primality deduced from the determinant rather than added as a hypothesis. -/
theorem ternary_matrixQuadraticPolynomial_principal_isPrime
    (h2 : (2 : K) ≠ 0) (M : Matrix (Fin 3) (Fin 3) K)
    (hM : M.IsSymm) (hdet : M.det ≠ 0) :
    (Ideal.span {matrixQuadraticPolynomial M}).IsPrime :=
  plane_principal_isPrime_of_irreducible _
    (ternary_matrixQuadraticPolynomial_irreducible h2 M hM hdet)

/-- Coefficient extension commutes with the literal matrix quadratic equation. -/
theorem matrixQuadraticPolynomial_map_coefficients
    {L : Type*} [CommRing L] {ι : Type*} [Fintype ι]
    (M : Matrix ι ι K) (f : K →+* L) :
    matrixQuadraticPolynomial (M.map f) =
      MvPolynomial.map f (matrixQuadraticPolynomial M) := by
  simp [matrixQuadraticPolynomial, Matrix.map_apply, map_sum, map_mul]

/-- Absolute irreducibility in an explicit coefficient-extension form: every
field extension preserves irreducibility of the actual ternary equation. -/
theorem ternary_matrixQuadraticPolynomial_irreducible_over_field
    {L : Type*} [Field L] (h2 : (2 : K) ≠ 0)
    (M : Matrix (Fin 3) (Fin 3) K) (hM : M.IsSymm) (hdet : M.det ≠ 0)
    (f : K →+* L) : Irreducible (MvPolynomial.map f (matrixQuadraticPolynomial M)) := by
  have h2L : (2 : L) ≠ 0 := by
    intro hz
    apply h2
    apply f.injective
    simpa only [map_ofNat, map_zero] using hz
  have hdetL : (M.map f).det ≠ 0 := by
    intro hz
    apply hdet
    apply f.injective
    exact (f.map_det M).trans (hz.trans (map_zero f).symm)
  rw [← matrixQuadraticPolynomial_map_coefficients]
  exact ternary_matrixQuadraticPolynomial_irreducible h2L (M.map f) (hM.map f) hdetL

/-- The actual extended homogeneous principal ideal is prime over every
extension field, without assuming algebraic closedness of either field. -/
theorem ternary_matrixQuadraticPolynomial_principal_isPrime_over_field
    {L : Type*} [Field L] (h2 : (2 : K) ≠ 0)
    (M : Matrix (Fin 3) (Fin 3) K) (hM : M.IsSymm) (hdet : M.det ≠ 0)
    (f : K →+* L) :
    (Ideal.span {MvPolynomial.map f (matrixQuadraticPolynomial M)}).IsPrime :=
  plane_principal_isPrime_of_irreducible _
    (ternary_matrixQuadraticPolynomial_irreducible_over_field h2 M hM hdet f)

end EvenQuinticConic.Incidence
