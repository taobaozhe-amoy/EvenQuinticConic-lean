import EvenQuinticConic.SegreIncidenceEquations
import EvenQuinticConic.PlaneCurveScheme

/-!
# The global projective incidence scheme

The Segre coordinates `z_(i,a) = t_i y_a` place the incidence in projective
eleven-space.  Its equations are all Segre minors, the linear equation
`Σ t_i l_i(y)`, and three quadratic equations `t_k Σ t_i r_i(y)`.
The nonzero parameter vector removes the introduced factor, so these
equations have exactly the intended field-valued coordinate solutions.

The global scheme is the reduced closed subscheme of the actual polynomial
`Proj` on this locus.  This file does not identify its global structure with
a possibly nonreduced quotient, or with the original conic bundle.
-/

noncomputable section

namespace EvenQuinticConic.Incidence

open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial

variable {K : Type*} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual bilinear Segre coordinates. -/
def segreCoordinates (t : Fin 3 → K) (y : Fin 4 → K) : SegreIndex → K :=
  fun ia => t ia.1 * y ia.2

/-- A two-by-two minor, expressed in homogeneous Segre coordinates. -/
def segreIncidenceMinor (i j : Fin 3) (a b : Fin 4) : MvPolynomial SegreIndex K :=
  X (i, a) * X (j, b) - X (i, b) * X (j, a)

/-- The finite displayed list of homogeneous equations. -/
inductive SegreEquationIndex where
  | minor (i j : Fin 3) (a b : Fin 4)
  | linear
  | quad (k : Fin 3)

/-- Every equation of the global incidence, including all Segre relations. -/
def segreEquationPolynomial (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) :
    SegreEquationIndex → MvPolynomial SegreIndex K
  | .minor i j a b => segreIncidenceMinor i j a b
  | .linear => segreIncidenceLinear M
  | .quad k => segreIncidenceQuadratic M k

/-- The actual positive degree of each global equation. -/
def segreEquationDegree : SegreEquationIndex → ℕ
  | .minor _ _ _ _ => 2
  | .linear => 1
  | .quad _ => 2

theorem segreEquationPolynomial_homogeneous
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (e : SegreEquationIndex) :
    (segreEquationPolynomial M e).IsHomogeneous (segreEquationDegree e) := by
  cases e with
  | minor i j a b =>
      exact ((isHomogeneous_X K (i, a)).mul (isHomogeneous_X K (j, b))).sub
        ((isHomogeneous_X K (i, b)).mul (isHomogeneous_X K (j, a)))
  | linear => exact segreIncidenceLinear_homogeneous M
  | quad k => exact segreIncidenceQuadratic_homogeneous M k

theorem segreEquationDegree_pos (e : SegreEquationIndex) :
    0 < segreEquationDegree e := by cases e <;> simp [segreEquationDegree]

/-- The equation set used by the global projective closed subscheme. -/
def segreIncidenceEquationSet (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) :
    Set (MvPolynomial SegreIndex K) :=
  Set.range (segreEquationPolynomial M)

theorem segreIncidenceEquationSet_homogeneous
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K)
    (f : MvPolynomial SegreIndex K) (hf : f ∈ segreIncidenceEquationSet M) :
    ∃ d : ℕ, 0 < d ∧ f.IsHomogeneous d := by
  obtain ⟨e, rfl⟩ := hf
  exact ⟨segreEquationDegree e, segreEquationDegree_pos e,
    segreEquationPolynomial_homogeneous M e⟩

/-- Nonzero factors give a nonzero Segre coordinate vector. -/
theorem segreCoordinates_ne_zero (t : Fin 3 → K) (y : Fin 4 → K)
    (ht : t ≠ 0) (hy : y ≠ 0) : segreCoordinates t y ≠ 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp ht
  obtain ⟨a, ha⟩ := Function.ne_iff.mp hy
  intro h
  exact mul_ne_zero hi ha (congrFun h (i, a))

/-- All Segre minors vanish on the explicit bilinear coordinates. -/
theorem eval_segreIncidenceMinor (t : Fin 3 → K) (y : Fin 4 → K)
    (i j : Fin 3) (a b : Fin 4) :
    eval (segreCoordinates t y) (segreIncidenceMinor i j a b) = 0 := by
  simp only [segreIncidenceMinor, eval_sub, eval_mul, eval_X, segreCoordinates]
  ring

/-- Every nonzero field-valued solution of the Segre minors is a genuine
decomposable tensor; the factors are constructed from a nonzero pivot. -/
theorem segreCoordinates_of_minors (z : SegreIndex → K) (hz : z ≠ 0)
    (hm : ∀ i j a b, eval z (segreIncidenceMinor i j a b) = 0) :
    ∃ t : Fin 3 → K, ∃ y : Fin 4 → K,
      t ≠ 0 ∧ y ≠ 0 ∧ z = segreCoordinates t y := by
  obtain ⟨⟨i, a⟩, hp⟩ := Function.ne_iff.mp hz
  change z (i, a) ≠ 0 at hp
  let t : Fin 3 → K := fun j => z (j, a)
  let y : Fin 4 → K := fun b => z (i, b) / z (i, a)
  refine ⟨t, y, ?_, ?_, ?_⟩
  · intro ht
    exact hp (congrFun ht i)
  · intro hy
    have hy' := congrFun hy a
    simp [y, hp] at hy'
  · funext ⟨j, b⟩
    have h := hm j i b a
    simp only [segreIncidenceMinor, eval_sub, eval_mul, eval_X, sub_eq_zero] at h
    dsimp [segreCoordinates, t, y]
    apply mul_right_cancel₀ hp
    rw [mul_assoc, div_mul_cancel₀ _ hp]
    exact h

/-- The linear equation on Segre coordinates is the original polar row. -/
theorem eval_segreIncidenceLinear (M : Fin 3 → Matrix (Fin 5) (Fin 5) K)
    (t : Fin 3 → K) (y : Fin 4 → K) :
    eval (segreCoordinates t y) (segreIncidenceLinear M) =
      ∑ i : Fin 3, t i * eval y (netLinearRow M i) :=
  eval₂_segreIncidenceLinear M (RingHom.id K) t y

/-- The quadratic Segre equation includes exactly the stated parameter factor. -/
theorem eval_segreIncidenceQuadratic (M : Fin 3 → Matrix (Fin 5) (Fin 5) K)
    (t : Fin 3 → K) (y : Fin 4 → K) (k : Fin 3) :
    eval (segreCoordinates t y) (segreIncidenceQuadratic M k) =
      t k * ∑ i : Fin 3, t i * eval y (netQuadraticRow M i) :=
  eval₂_segreIncidenceQuadratic M (RingHom.id K) t y k

/-- The global homogeneous equations recover exactly the two incidence
equations. Nonzero parameter coordinates remove the factors in the quadratics. -/
theorem segreEquations_on_coordinates_iff
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K)
    (t : Fin 3 → K) (y : Fin 4 → K) (ht : t ≠ 0) :
    (∀ e, eval (segreCoordinates t y) (segreEquationPolynomial M e) = 0) ↔
      (∑ i : Fin 3, t i * eval y (netLinearRow M i)) = 0 ∧
      (∑ i : Fin 3, t i * eval y (netQuadraticRow M i)) = 0 := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := Function.ne_iff.mp ht
    change t k ≠ 0 at hk
    have hl := h .linear
    have hq := h (.quad k)
    rw [segreEquationPolynomial, eval_segreIncidenceLinear] at hl
    rw [segreEquationPolynomial, eval_segreIncidenceQuadratic] at hq
    exact ⟨hl, (mul_eq_zero.mp hq).resolve_left hk⟩
  · rintro ⟨hl, hq⟩ e
    cases e with
    | minor i j a b => exact eval_segreIncidenceMinor t y i j a b
    | linear => exact (eval_segreIncidenceLinear M t y).trans hl
    | quad k => rw [segreEquationPolynomial, eval_segreIncidenceQuadratic, hq, mul_zero]

/-- Every nonzero field-valued homogeneous solution comes from an actual
pair of nonzero projective coordinate vectors satisfying the two original
incidence equations, and conversely. In particular there is no extra
set-theoretic component from multiplying the quadratic equation by `t_k`. -/
theorem segreIncidence_zeroSet_exact
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (z : SegreIndex → K) (hz : z ≠ 0) :
    (∀ f ∈ segreIncidenceEquationSet M, eval z f = 0) ↔
      ∃ t : Fin 3 → K, ∃ y : Fin 4 → K,
        t ≠ 0 ∧ y ≠ 0 ∧ z = segreCoordinates t y ∧
        (∑ i : Fin 3, t i * eval y (netLinearRow M i)) = 0 ∧
        (∑ i : Fin 3, t i * eval y (netQuadraticRow M i)) = 0 := by
  simp only [segreIncidenceEquationSet, Set.forall_mem_range]
  constructor
  · intro h
    obtain ⟨t, y, ht, hy, rfl⟩ := segreCoordinates_of_minors z hz
      (fun i j a b => h (.minor i j a b))
    exact ⟨t, y, ht, hy, rfl, (segreEquations_on_coordinates_iff M t y ht).mp h⟩
  · rintro ⟨t, y, ht, hy, rfl, hl, hq⟩
    exact (segreEquations_on_coordinates_iff M t y ht).mpr ⟨hl, hq⟩

/-- The actual ambient projective eleven-space, in Segre coordinate indexing. -/
def SegreProjectiveScheme (K : Type*) [Field K] : Scheme :=
  Proj (homogeneousSubmodule SegreIndex K)

/-- The literal homogeneous zero locus of the complete incidence equation set. -/
def globalIncidenceClosedSet (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) :
    Closeds (SegreProjectiveScheme K) :=
  ⟨ProjectiveSpectrum.zeroLocus (homogeneousSubmodule SegreIndex K)
      (segreIncidenceEquationSet M), ProjectiveSpectrum.isClosed_zeroLocus _ _⟩

/-- The actual vanishing ideal sheaf of the global homogeneous locus. -/
def globalIncidenceIdealSheaf (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) :
    (SegreProjectiveScheme K).IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal (globalIncidenceClosedSet M)

/-- The global reduced projective incidence scheme, with its actual glued
structure sheaf, rather than a set of coordinate solutions. -/
def GlobalIncidenceScheme (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) : Scheme :=
  (globalIncidenceIdealSheaf M).subscheme

/-- The actual closed immersion into projective eleven-space. -/
def globalIncidenceInclusion (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) :
    GlobalIncidenceScheme M ⟶ SegreProjectiveScheme K :=
  (globalIncidenceIdealSheaf M).subschemeι

instance globalIncidenceInclusion_isClosedImmersion
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) :
    IsClosedImmersion (globalIncidenceInclusion M) := by
  unfold globalIncidenceInclusion
  infer_instance

/-- The canonical coefficient-field structure on the Segre ambient Proj. -/
def segreProjectiveStructure (K : Type*) [Field K] :
    SegreProjectiveScheme K ⟶ Spec (CommRingCat.of K) :=
  Proj.toSpecZero (homogeneousSubmodule SegreIndex K) ≫
    Spec.map (CommRingCat.ofHom (algebraMap K (homogeneousSubmodule SegreIndex K 0)))

/-- The global incidence is a scheme over its given coefficient field. -/
def globalIncidenceStructure (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) :
    GlobalIncidenceScheme M ⟶ Spec (CommRingCat.of K) :=
  globalIncidenceInclusion M ≫ segreProjectiveStructure K

instance segreProjectiveScheme_over (K : Type*) [Field K] :
    (SegreProjectiveScheme K).Over (Spec (CommRingCat.of K)) :=
  ⟨segreProjectiveStructure K⟩

instance globalIncidenceScheme_over (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) :
    (GlobalIncidenceScheme M).Over (Spec (CommRingCat.of K)) :=
  ⟨globalIncidenceStructure M⟩

instance globalIncidenceInclusion_isOver (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) :
    (globalIncidenceInclusion M).IsOver (Spec (CommRingCat.of K)) :=
  ⟨rfl⟩

/-- The closed immersion has exactly the prescribed underlying global locus. -/
theorem globalIncidenceInclusion_range (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) :
    Set.range (globalIncidenceInclusion M).base =
      ProjectiveSpectrum.zeroLocus (homogeneousSubmodule SegreIndex K)
        (segreIncidenceEquationSet M) := by
  exact Scheme.IdealSheafData.range_subschemeι (globalIncidenceIdealSheaf M)

instance globalIncidenceScheme_isReduced (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) :
    IsReduced (GlobalIncidenceScheme M) :=
  reduced_induced_scheme_isReduced _ _

/-- The standard Segre coordinate chart on the actual global incidence. -/
def globalIncidenceCoordinateOpen (M : Fin 3 → Matrix (Fin 5) (Fin 5) K)
    (q : SegreIndex) : (GlobalIncidenceScheme M).Opens :=
  globalIncidenceInclusion M ⁻¹ᵁ
    Proj.basicOpen (homogeneousSubmodule SegreIndex K) (X q)

theorem segreProjectiveCoordinateOpen_cover :
    (⨆ q : SegreIndex,
      Proj.basicOpen (homogeneousSubmodule SegreIndex K) (X q)) = ⊤ := by
  apply Proj.iSup_basicOpen_eq_top'
  · intro q
    exact ⟨1, isHomogeneous_X K q⟩
  · apply top_unique
    intro f htop
    clear htop
    induction f using MvPolynomial.induction_on with
    | C a =>
        exact Subalgebra.algebraMap_mem _
          (⟨C a, isHomogeneous_C SegreIndex a⟩ : homogeneousSubmodule SegreIndex K 0)
    | add f g hf hg => exact add_mem hf hg
    | mul_X f q hf => exact mul_mem hf (Algebra.subset_adjoin ⟨q, rfl⟩)

/-- The twelve actual affine coordinate opens cover the global incidence. -/
theorem globalIncidenceCoordinateOpen_cover
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) :
    (⨆ q : SegreIndex, globalIncidenceCoordinateOpen M q) = ⊤ :=
  (globalIncidenceInclusion M).preimage_iSup_eq_top segreProjectiveCoordinateOpen_cover

theorem globalIncidenceCoordinateOpen_isAffine
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (q : SegreIndex) :
    IsAffineOpen (globalIncidenceCoordinateOpen M q) := by
  apply IsAffineOpen.preimage
  exact Proj.isAffineOpen_basicOpen _ _ (isHomogeneous_X K q) (by decide)

/-- The selected minor open in the global scheme itself. Its ambient
equations are homogeneous of degrees one and three, respectively. -/
def globalIncidenceMinorOpen (M : Fin 3 → Matrix (Fin 5) (Fin 5) K)
    (p : Fin 4) (i j k : Fin 3) : (GlobalIncidenceScheme M).Opens :=
  globalIncidenceInclusion M ⁻¹ᵁ
    (Proj.basicOpen (homogeneousSubmodule SegreIndex K) (X (k, p)) ⊓
      Proj.basicOpen (homogeneousSubmodule SegreIndex K) (globalIncidenceMinor M i j k))

/-- The global minor open lies in the displayed genuine coordinate chart. -/
theorem globalIncidenceMinorOpen_le_coordinate
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (p : Fin 4) (i j k : Fin 3) :
    globalIncidenceMinorOpen M p i j k ≤ globalIncidenceCoordinateOpen M (k, p) :=
  fun _ h => h.1

/-- The global minor open is itself affine: in the ambient projective
space it is the basic open of the product of its two homogeneous equations. -/
theorem globalIncidenceMinorOpen_isAffine
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (p : Fin 4) (i j k : Fin 3) :
    IsAffineOpen (globalIncidenceMinorOpen M p i j k) := by
  unfold globalIncidenceMinorOpen
  apply IsAffineOpen.preimage
  rw [← Proj.basicOpen_mul]
  exact Proj.isAffineOpen_basicOpen _ _
    ((isHomogeneous_X K (k, p)).mul (globalIncidenceMinor_homogeneous M i j k))
    (by decide)

/-- The line through a Segre coordinate vector is represented by an actual
homogeneous kernel, using a polynomial parameter to retain degrees. -/
def segreVectorHomogeneousIdeal (z : SegreIndex → K) :
    HomogeneousIdeal (homogeneousSubmodule SegreIndex K) where
  toSubmodule := RingHom.ker (gradedRestriction z).toRingHom
  is_homogeneous' := by
    intro d f hf
    rw [← DirectSum.Decomposition.decompose'_eq,
      MvPolynomial.decomposition.decompose'_apply]
    change gradedRestriction z (homogeneousComponent d f) = 0
    exact gradedRestriction_homogeneousComponent_eq_zero z f hf d

theorem mem_segreVectorHomogeneousIdeal_iff (z : SegreIndex → K)
    (f : MvPolynomial SegreIndex K) (d : ℕ) (hf : f.IsHomogeneous d) :
    f ∈ (segreVectorHomogeneousIdeal z).toIdeal ↔ eval z f = 0 := by
  change gradedRestriction z f = 0 ↔ _
  rw [gradedRestriction_of_isHomogeneous z f d hf]
  simp [aeval_def]

/-- A nonzero homogeneous coordinate vector determines a genuine point
of the actual ambient projective spectrum. -/
def segreVectorProjectivePoint (z : SegreIndex → K) (hz : z ≠ 0) :
    SegreProjectiveScheme K where
  asHomogeneousIdeal := segreVectorHomogeneousIdeal z
  isPrime := RingHom.ker_isPrime (gradedRestriction z).toRingHom
  not_irrelevant_le := by
    intro hle
    apply hz
    funext q
    have hq : X q ∈ segreVectorHomogeneousIdeal z := hle (by
      rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply]
      exact DirectSum.decompose_of_mem_ne (homogeneousSubmodule SegreIndex K)
        (isHomogeneous_X K q) (by decide : (1 : ℕ) ≠ 0))
    simpa using (mem_segreVectorHomogeneousIdeal_iff z (X q) 1
      (isHomogeneous_X K q)).mp hq

/-- The nonzero vector belongs to the actual global closed locus exactly
when it satisfies the homogeneous equations. -/
theorem segreVectorProjectivePoint_mem_global_iff
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (z : SegreIndex → K) (hz : z ≠ 0) :
    segreVectorProjectivePoint z hz ∈ globalIncidenceClosedSet M ↔
      ∀ f ∈ segreIncidenceEquationSet M, eval z f = 0 := by
  change (∀ f ∈ segreIncidenceEquationSet M,
    f ∈ (segreVectorHomogeneousIdeal z).toIdeal) ↔ _
  apply forall_congr'
  intro f
  apply forall_congr'
  intro hf
  obtain ⟨d, _, hd⟩ := segreIncidenceEquationSet_homogeneous M f hf
  exact mem_segreVectorHomogeneousIdeal_iff z f d hd

/-- Coordinate incidence solutions give points on the actual global
scheme, via its proved closed-immersion image, not just on an auxiliary set. -/
theorem globalIncidenceScheme_nonempty_of_coordinates
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K)
    (t : Fin 3 → K) (y : Fin 4 → K) (ht : t ≠ 0) (hy : y ≠ 0)
    (hl : (∑ i : Fin 3, t i * eval y (netLinearRow M i)) = 0)
    (hq : (∑ i : Fin 3, t i * eval y (netQuadraticRow M i)) = 0) :
    Nonempty (GlobalIncidenceScheme M) := by
  let z := segreCoordinates t y
  have hz := segreCoordinates_ne_zero t y ht hy
  have hmem : segreVectorProjectivePoint z hz ∈ globalIncidenceClosedSet M :=
    (segreVectorProjectivePoint_mem_global_iff M z hz).mpr
      ((segreIncidence_zeroSet_exact M z hz).mpr ⟨t, y, ht, hy, rfl, hl, hq⟩)
  have hrange : segreVectorProjectivePoint z hz ∈
      Set.range (globalIncidenceInclusion M).base := by
    rw [globalIncidenceInclusion_range]
    exact hmem
  obtain ⟨x, _⟩ := hrange
  exact ⟨x⟩

/-- The actual global minor open contains the point constructed from any
incidence solution with the indicated nonzero coordinate and minor. -/
theorem globalIncidenceMinorOpen_nonempty_of_coordinates
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K)
    (t : Fin 3 → K) (y : Fin 4 → K) (p : Fin 4) (i j k : Fin 3)
    (htk : t k ≠ 0) (hyp : y p ≠ 0)
    (hl : (∑ a : Fin 3, t a * eval y (netLinearRow M a)) = 0)
    (hq : (∑ a : Fin 3, t a * eval y (netQuadraticRow M a)) = 0)
    (hminor : eval y (netIncidenceMinor M i j) ≠ 0) :
    Nonempty (globalIncidenceMinorOpen M p i j k) := by
  have ht : t ≠ 0 := fun h => htk (congrFun h k)
  have hy : y ≠ 0 := fun h => hyp (congrFun h p)
  let z := segreCoordinates t y
  have hz := segreCoordinates_ne_zero t y ht hy
  have hmem : segreVectorProjectivePoint z hz ∈ globalIncidenceClosedSet M :=
    (segreVectorProjectivePoint_mem_global_iff M z hz).mpr
      ((segreIncidence_zeroSet_exact M z hz).mpr ⟨t, y, ht, hy, rfl, hl, hq⟩)
  have hrange : segreVectorProjectivePoint z hz ∈
      Set.range (globalIncidenceInclusion M).base := by
    rw [globalIncidenceInclusion_range]
    exact hmem
  obtain ⟨x, hx⟩ := hrange
  refine ⟨⟨x, ?_⟩⟩
  change (globalIncidenceInclusion M).base x ∈
    Proj.basicOpen (homogeneousSubmodule SegreIndex K) (X (k, p)) ⊓
      Proj.basicOpen (homogeneousSubmodule SegreIndex K) (globalIncidenceMinor M i j k)
  rw [hx]
  constructor
  · change X (k, p) ∉ (segreVectorHomogeneousIdeal z).toIdeal
    rw [mem_segreVectorHomogeneousIdeal_iff z (X (k, p)) 1 (isHomogeneous_X K (k, p))]
    simpa [z, segreCoordinates] using mul_ne_zero htk hyp
  · change globalIncidenceMinor M i j k ∉ (segreVectorHomogeneousIdeal z).toIdeal
    rw [mem_segreVectorHomogeneousIdeal_iff z _ 3 (globalIncidenceMinor_homogeneous M i j k)]
    change eval₂ (RingHom.id K) (fun q : SegreIndex => t q.1 * y q.2)
      (globalIncidenceMinor M i j k) ≠ 0
    rw [eval₂_globalIncidenceMinor]
    exact mul_ne_zero (pow_ne_zero 3 htk) hminor

end EvenQuinticConic.Incidence
