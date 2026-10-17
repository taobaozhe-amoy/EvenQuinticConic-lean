import EvenQuinticConic.IncidenceDehomogenization

/-!
# Global Segre equations for the actual matrix-net incidence

The linear row has bidegree `(1,1)` and is a linear polynomial in Segre
coordinates. Multiplying the quadratic incidence equation of bidegree
`(1,2)` by each first-factor coordinate gives three quadratic Segre
polynomials. The pullback identities are polynomial identities over every
commutative coefficient algebra, not just equalities on rational points.
-/

noncomputable section
namespace EvenQuinticConic.Incidence
open MvPolynomial

/-- Coordinates of the Segre ambient projective eleven-space. -/
abbrev SegreIndex := Fin 3 × Fin 4

variable {K : Type*} [Field K]

/-- The actual polar incidence equation in Segre coordinates. -/
def segreIncidenceLinear (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) :
    MvPolynomial SegreIndex K :=
  ∑ i : Fin 3, ∑ a : Fin 4, C (M i a.succ 0) * X (i, a)

/-- The quadratic incidence equation multiplied by the `k`-th first-factor
coordinate, expressed as a homogeneous Segre polynomial. -/
def segreIncidenceQuadratic (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) :
    MvPolynomial SegreIndex K :=
  ∑ i : Fin 3, ∑ a : Fin 4, ∑ b : Fin 4,
    C (M i a.succ b.succ) * X (i, a) * X (k, b)

theorem segreIncidenceLinear_homogeneous
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) :
    (segreIncidenceLinear M).IsHomogeneous 1 := by
  apply IsHomogeneous.sum
  intro i _
  exact IsHomogeneous.sum _ _ _ (fun a _ => isHomogeneous_C_mul_X _ _)

theorem segreIncidenceQuadratic_homogeneous
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) :
    (segreIncidenceQuadratic M k).IsHomogeneous 2 := by
  apply IsHomogeneous.sum
  intro i _
  apply IsHomogeneous.sum
  intro a _
  apply IsHomogeneous.sum
  intro b _
  exact (isHomogeneous_C_mul_X _ _).mul (isHomogeneous_X K (k, b))

variable {A : Type*} [CommRing A]

/-- Pulling back the linear equation along the actual Segre substitution
is precisely the polar incidence equation. -/
theorem eval₂_segreIncidenceLinear
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (f : K →+* A)
    (t : Fin 3 → A) (y : Fin 4 → A) :
    eval₂ f (fun ij : SegreIndex => t ij.1 * y ij.2) (segreIncidenceLinear M) =
      ∑ i : Fin 3, t i * eval₂ f y (netLinearRow M i) := by
  simp only [segreIncidenceLinear, netLinearRow, coefficientLinearPolynomial,
    eval₂_sum, eval₂_mul, eval₂_C, eval₂_X, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- The three global quadratic equations pull back to the one quadratic
incidence equation multiplied by the three first-factor coordinates. -/
theorem eval₂_segreIncidenceQuadratic
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (f : K →+* A)
    (t : Fin 3 → A) (y : Fin 4 → A) (k : Fin 3) :
    eval₂ f (fun ij : SegreIndex => t ij.1 * y ij.2)
        (segreIncidenceQuadratic M k) =
      t k * ∑ i : Fin 3, t i * eval₂ f y (netQuadraticRow M i) := by
  simp only [segreIncidenceQuadratic, netQuadraticRow, matrixQuadraticPolynomial,
    eval₂_sum, eval₂_mul, eval₂_C, eval₂_X, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- In a chart where `t k = 1`, the selected global quadratic polynomial
is the original quadratic incidence equation. -/
theorem eval₂_segreIncidenceQuadratic_pivot
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (f : K →+* A)
    (t : Fin 3 → A) (y : Fin 4 → A) (k : Fin 3) (hk : t k = 1) :
    eval₂ f (fun ij : SegreIndex => t ij.1 * y ij.2)
        (segreIncidenceQuadratic M k) =
      ∑ i : Fin 3, t i * eval₂ f y (netQuadraticRow M i) := by
  rw [eval₂_segreIncidenceQuadratic, hk, one_mul]

/-- On that same chart the other global quadratic equations are explicit
multiples of the selected one, over arbitrary coefficient rings. -/
theorem eval₂_segreIncidenceQuadratic_eq_mul_pivot
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (f : K →+* A)
    (t : Fin 3 → A) (y : Fin 4 → A) (k : Fin 3) (hk : t k = 1) (a : Fin 3) :
    eval₂ f (fun ij : SegreIndex => t ij.1 * y ij.2)
        (segreIncidenceQuadratic M a) =
      t a * eval₂ f (fun ij : SegreIndex => t ij.1 * y ij.2)
        (segreIncidenceQuadratic M k) := by
  rw [eval₂_segreIncidenceQuadratic, eval₂_segreIncidenceQuadratic_pivot M f t y k hk]

/-- The actual incidence minor represented on the `k`-th Segre row. -/
def globalIncidenceMinor (M : Fin 3 → Matrix (Fin 5) (Fin 5) K)
    (i j k : Fin 3) : MvPolynomial SegreIndex K :=
  rename (fun a : Fin 4 => (k, a)) (netIncidenceMinor M i j)

theorem globalIncidenceMinor_homogeneous
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (i j k : Fin 3) :
    (globalIncidenceMinor M i j k).IsHomogeneous 3 :=
  (netIncidenceMinor_homogeneous M i j).rename_isHomogeneous

/-- The global minor is exactly the original minor multiplied by the
cube of the chosen first-factor coordinate. -/
theorem eval₂_globalIncidenceMinor
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (f : K →+* A)
    (t : Fin 3 → A) (y : Fin 4 → A) (i j k : Fin 3) :
    eval₂ f (fun ij : SegreIndex => t ij.1 * y ij.2)
        (globalIncidenceMinor M i j k) =
      t k ^ 3 * eval₂ f y (netIncidenceMinor M i j) := by
  rw [globalIncidenceMinor, eval₂_rename]
  have h := homogeneous_eval₂_scale f y (t k) (netIncidenceMinor M i j) 3
    (netIncidenceMinor_homogeneous M i j)
  simpa only [Function.comp_def, mul_comm] using h

/-- The two first-factor coordinates retained after setting `t k = 1`. -/
def segreChartT (k : Fin 3) :
    Fin 3 → MvPolynomial (Fin 2) (MvPolynomial (Fin 3) K) :=
  Fin.insertNth k 1 X

/-- The four second-factor coordinates, with the `p`-th set to one,
regarded as coefficients in the first-factor polynomial ring. -/
def segreChartY (p : Fin 4) :
    Fin 4 → MvPolynomial (Fin 2) (MvPolynomial (Fin 3) K) :=
  fun j => C (dehomogenizeAt p (X j))

/-- The literal Segre substitution on the product chart `t k = y p = 1`.
The target is a polynomial ring in two variables over the three-variable
coordinate ring of the second projective chart. -/
def segreIncidenceChartSubstitution (k : Fin 3) (p : Fin 4) :
    MvPolynomial SegreIndex K →ₐ[K]
      MvPolynomial (Fin 2) (MvPolynomial (Fin 3) K) :=
  aeval (fun ij => segreChartT (K := K) k ij.1 * segreChartY p ij.2)

@[simp] theorem segreChartT_pivot (k : Fin 3) : segreChartT (K := K) k k = 1 := by
  simp [segreChartT]

@[simp] theorem segreChartT_succAbove (k : Fin 3) (a : Fin 2) :
    segreChartT (K := K) k (k.succAbove a) = X a := by simp [segreChartT]

@[simp] theorem segreChartY_pivot (p : Fin 4) : segreChartY (K := K) p p = 1 := by
  simp [segreChartY]

@[simp] theorem segreChartY_succAbove (p : Fin 4) (a : Fin 3) :
    segreChartY (K := K) p (p.succAbove a) = C (X a) := by simp [segreChartY]

/-- Dehomogenized coefficients ordered by the two retained `t` coordinates
and then its pivot coordinate. -/
def segreChartRow (c : Fin 3 → MvPolynomial (Fin 4) K) (k : Fin 3) (p : Fin 4) :
    Vec3 (MvPolynomial (Fin 3) K) :=
  ⟨dehomogenizeAt p (c (k.succAbove 0)),
    dehomogenizeAt p (c (k.succAbove 1)), dehomogenizeAt p (c k)⟩

theorem sum_segreChartT_mul_C (c : Fin 3 → MvPolynomial (Fin 3) K) (k : Fin 3) :
    (∑ i : Fin 3, segreChartT (K := K) k i * C (c i)) =
      rowPolynomial ⟨c (k.succAbove 0), c (k.succAbove 1), c k⟩ := by
  rw [Fin.sum_univ_succAbove _ k]
  simp only [segreChartT_pivot, one_mul, Fin.sum_univ_two, segreChartT_succAbove,
    rowPolynomial]
  ring

/-- Substituting second-factor chart coordinates is precisely the existing
projective dehomogenization followed by the coefficient embedding. -/
theorem eval₂_segreChartY (p : Fin 4) (F : MvPolynomial (Fin 4) K) :
    eval₂ (algebraMap K (MvPolynomial (Fin 2) (MvPolynomial (Fin 3) K)))
        (segreChartY p) F = C (dehomogenizeAt p F) := by
  change eval₂ (C.comp C) (fun j => C (dehomogenizeAt p (X j))) F = _
  calc
    _ = C (eval₂ C (fun j => dehomogenizeAt p (X j)) F) := by
      simpa only [Function.comp_def] using
        (eval₂_comp_left (C : MvPolynomial (Fin 3) K →+*
          MvPolynomial (Fin 2) (MvPolynomial (Fin 3) K)) C
          (fun j => dehomogenizeAt p (X j)) F).symm
    _ = _ := ?_
  congr 1
  change eval₂ C (fun j => aeval (Fin.insertNth p 1 X) (X j)) F = _
  simp only [aeval_X]
  rfl

/-- The global linear Segre equation becomes the actual affine incidence
row polynomial on every product chart. -/
theorem segreIncidenceChartSubstitution_linear
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4) :
    segreIncidenceChartSubstitution (K := K) k p (segreIncidenceLinear M) =
      rowPolynomial (segreChartRow (netLinearRow M) k p) := by
  change eval₂ _ _ _ = _
  rw [eval₂_segreIncidenceLinear]
  simp only [eval₂_segreChartY]
  exact sum_segreChartT_mul_C _ k

/-- The selected global quadratic equation becomes the actual second
row polynomial of the affine incidence chart. -/
theorem segreIncidenceChartSubstitution_quadratic_pivot
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4) :
    segreIncidenceChartSubstitution (K := K) k p (segreIncidenceQuadratic M k) =
      rowPolynomial (segreChartRow (netQuadraticRow M) k p) := by
  change eval₂ _ _ _ = _
  rw [eval₂_segreIncidenceQuadratic_pivot M _ _ _ k (segreChartT_pivot k)]
  simp only [eval₂_segreChartY]
  exact sum_segreChartT_mul_C _ k

/-- Every other global quadratic equation contributes only a multiple of
the selected row polynomial, as an identity in the actual chart ring. -/
theorem segreIncidenceChartSubstitution_quadratic
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4) (a : Fin 3) :
    segreIncidenceChartSubstitution (K := K) k p (segreIncidenceQuadratic M a) =
      segreChartT k a * rowPolynomial (segreChartRow (netQuadraticRow M) k p) := by
  change eval₂ _ _ _ = _
  rw [eval₂_segreIncidenceQuadratic]
  simp only [eval₂_segreChartY]
  rw [sum_segreChartT_mul_C]
  rfl

/-- The global cubic minor is exactly the prior dehomogenized minor on
the product chart, with no nonvanishing assumptions. -/
theorem segreIncidenceChartSubstitution_minor
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (i j k : Fin 3) (p : Fin 4) :
    segreIncidenceChartSubstitution (K := K) k p (globalIncidenceMinor M i j k) =
      C (netDehomogenizedMinor M p i j) := by
  change eval₂ _ _ _ = _
  rw [eval₂_globalIncidenceMinor, segreChartT_pivot, one_pow, one_mul, eval₂_segreChartY]
  rfl

end EvenQuinticConic.Incidence
