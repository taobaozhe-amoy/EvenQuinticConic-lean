import EvenQuinticConic.IncidenceDominance
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-!
# Actual coefficient base change of the incidence chart equations

This file presents the parameter base change of the actual chart quotient,
retaining its defining equations and the literal parameter coefficient map.
-/

noncomputable section
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
namespace EvenQuinticConic.Incidence
open MvPolynomial TensorProduct

section PolynomialBaseChange
variable {R S σ : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- Coefficient base change on a polynomial quotient. -/
def polynomialQuotientCoefficientMap (I : Ideal (MvPolynomial σ R)) :
    (MvPolynomial σ R ⧸ I) →ₐ[R]
      (MvPolynomial σ S ⧸ I.map (MvPolynomial.map (algebraMap R S))) :=
  Ideal.Quotient.liftₐ I
    ((Ideal.Quotient.mkₐ R _).comp (mapAlgHom (Algebra.ofId R S))) (by
      intro P hP
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hP))

@[simp] theorem polynomialQuotientCoefficientMap_mk
    (I : Ideal (MvPolynomial σ R)) (P : MvPolynomial σ R) :
    polynomialQuotientCoefficientMap (S := S) I (Ideal.Quotient.mk I P) =
      Ideal.Quotient.mk _ (MvPolynomial.map (algebraMap R S) P) := rfl

/-- Evaluation of base-changed variables in the actual tensor product. -/
def polynomialTensorQuotientEval (I : Ideal (MvPolynomial σ R)) :
    MvPolynomial σ S →ₐ[S] S ⊗[R] (MvPolynomial σ R ⧸ I) :=
  aeval (fun i => (1 : S) ⊗ₜ[R] (Ideal.Quotient.mk I (X i)))

theorem polynomialTensorQuotientEval_map
    (I : Ideal (MvPolynomial σ R)) (P : MvPolynomial σ R) :
    polynomialTensorQuotientEval (S := S) I (MvPolynomial.map (algebraMap R S) P) =
      1 ⊗ₜ[R] (Ideal.Quotient.mk I P) := by
  have he : ((polynomialTensorQuotientEval (S := S) I).restrictScalars R).comp
      (mapAlgHom (Algebra.ofId R S)) =
      Algebra.TensorProduct.includeRight.comp (Ideal.Quotient.mkₐ R I) := by
    ext i
    simp [polynomialTensorQuotientEval]
  exact AlgHom.congr_fun he P

/-- The tensor evaluation annihilates the entire extended defining ideal. -/
theorem polynomialTensorQuotientEval_ideal
    (I : Ideal (MvPolynomial σ R)) :
    I.map (MvPolynomial.map (algebraMap R S)) ≤
      RingHom.ker (polynomialTensorQuotientEval (S := S) I).toRingHom := by
  rw [Ideal.map_le_iff_le_comap]
  intro P hP
  change polynomialTensorQuotientEval (S := S) I
    (MvPolynomial.map (algebraMap R S) P) = 0
  rw [polynomialTensorQuotientEval_map, Ideal.Quotient.eq_zero_iff_mem.mpr hP,
    tmul_zero]

/-- Coefficient extension commutes with this actual polynomial quotient,
without flatness or reducedness assumptions. -/
def polynomialQuotientBaseChangeEquiv (I : Ideal (MvPolynomial σ R)) :
    S ⊗[R] (MvPolynomial σ R ⧸ I) ≃ₐ[S]
      (MvPolynomial σ S ⧸ I.map (MvPolynomial.map (algebraMap R S))) := by
  let f : S ⊗[R] (MvPolynomial σ R ⧸ I) →ₐ[S]
      (MvPolynomial σ S ⧸ I.map (MvPolynomial.map (algebraMap R S))) :=
    Algebra.TensorProduct.lift (Algebra.ofId S _) (polynomialQuotientCoefficientMap I)
      (fun _ _ => Commute.all _ _)
  let g : (MvPolynomial σ S ⧸ I.map (MvPolynomial.map (algebraMap R S))) →ₐ[S]
      S ⊗[R] (MvPolynomial σ R ⧸ I) :=
    Ideal.Quotient.liftₐ _ (polynomialTensorQuotientEval I)
      (fun P hP => polynomialTensorQuotientEval_ideal I hP)
  apply AlgEquiv.ofAlgHom f g
  · apply Ideal.Quotient.algHom_ext
    ext i
    simp [f, g, polynomialTensorQuotientEval]
  · apply Algebra.TensorProduct.ext
    · ext
    · apply Ideal.Quotient.algHom_ext
      ext i
      simp [f, g, polynomialTensorQuotientEval]

@[simp] theorem polynomialQuotientBaseChangeEquiv_tmul_mk
    (I : Ideal (MvPolynomial σ R)) (s : S) (P : MvPolynomial σ R) :
    polynomialQuotientBaseChangeEquiv I (s ⊗ₜ[R] Ideal.Quotient.mk I P) =
      algebraMap S _ s * Ideal.Quotient.mk _ (MvPolynomial.map (algebraMap R S) P) := by
  simp [polynomialQuotientBaseChangeEquiv]

end PolynomialBaseChange

section ActualChart
variable {K : Type*} [Field K]

/-- Polynomial coordinates on the actual normalized parameter plane. -/
abbrev IncidenceParameterPolynomialRing (K : Type*) [Field K] :=
  MvPolynomial (Fin 2) K

/-- The actual incidence ideal after placing parameter variables among
coefficients and spatial variables outside. -/
def incidenceParameterPresentationIdeal
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4) :
    Ideal (MvPolynomial (Fin 3) (IncidenceParameterPolynomialRing K)) :=
  (affineIncidenceIdeal (segreChartRow (netLinearRow M) k p)
    (segreChartRow (netQuadraticRow M) k p)).map
      (MvPolynomial.commAlgEquiv K (Fin 2) (Fin 3)).toRingHom

/-- This presentation is the actual two-equation chart, with the parameter
polynomial ring as coefficient ring. -/
abbrev IncidenceParameterPresentationAlgebra
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4) :=
  MvPolynomial (Fin 3) (IncidenceParameterPolynomialRing K) ⧸
    incidenceParameterPresentationIdeal M k p

/-- Swapping the order of the independent variables identifies the actual
Segre chart quotient with the parameter-coefficient presentation. -/
def incidenceParameterPresentationEquiv
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4) :
    SegreIncidenceChartAlgebra M k p ≃ₐ[K]
      IncidenceParameterPresentationAlgebra M k p :=
  (segreIncidenceChartAlgEquiv M k p).trans
    (Ideal.quotientEquivAlg _ _ (MvPolynomial.commAlgEquiv K (Fin 2) (Fin 3)) rfl)

/-- The original unlocalized parameter-coordinate pullback. -/
def incidenceParameterUnlocalizedPolynomialMap
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4) :
    IncidenceParameterPolynomialRing K →ₐ[K] SegreIncidenceChartAlgebra M k p :=
  aeval (fun i => Ideal.Quotient.mk _ (X (k.succAbove i, p)))

@[simp] theorem incidenceParameterPresentationEquiv_parameter
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4) (i : Fin 2) :
    incidenceParameterPresentationEquiv M k p
      (Ideal.Quotient.mk _ (X (k.succAbove i, p))) =
      algebraMap (IncidenceParameterPolynomialRing K)
        (IncidenceParameterPresentationAlgebra M k p) (X i) := by
  change (Ideal.quotientEquivAlg _ _
    (MvPolynomial.commAlgEquiv K (Fin 2) (Fin 3)) rfl)
      (segreIncidenceChartAlgEquiv M k p (Ideal.Quotient.mk _ (X (k.succAbove i, p)))) = _
  rw [segreIncidenceChartAlgEquiv_pivotColumn]
  change Ideal.Quotient.mk _
    (MvPolynomial.commAlgEquiv K (Fin 2) (Fin 3) (X i)) = _
  rw [MvPolynomial.commAlgEquiv_X]
  rfl

theorem incidenceParameterPresentationEquiv_coefficient
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4)
    (f : IncidenceParameterPolynomialRing K) :
    incidenceParameterPresentationEquiv M k p
      (incidenceParameterUnlocalizedPolynomialMap M k p f) =
      algebraMap (IncidenceParameterPolynomialRing K)
        (IncidenceParameterPresentationAlgebra M k p) f := by
  have he : (incidenceParameterPresentationEquiv M k p).toAlgHom.comp
      (incidenceParameterUnlocalizedPolynomialMap M k p) =
      IsScalarTower.toAlgHom K (IncidenceParameterPolynomialRing K)
        (IncidenceParameterPresentationAlgebra M k p) := by
    ext i
    simp [incidenceParameterUnlocalizedPolynomialMap]
  exact AlgHom.congr_fun he f

/-- The coefficient structure on the actual Segre chart comes from its
literal parameter-coordinate pullback. -/
def incidenceUnlocalizedParameterAlgebra
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4) :
    Algebra (IncidenceParameterPolynomialRing K) (SegreIncidenceChartAlgebra M k p) :=
  (incidenceParameterUnlocalizedPolynomialMap M k p).toRingHom.toAlgebra

/-- The chart presentation is also an isomorphism over its actual parameter
ring, not merely an isomorphism over the ground field. -/
def incidenceParameterPresentationEquivOverParameters
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4) :
    letI := incidenceUnlocalizedParameterAlgebra M k p
    SegreIncidenceChartAlgebra M k p ≃ₐ[IncidenceParameterPolynomialRing K]
      IncidenceParameterPresentationAlgebra M k p := by
  letI := incidenceUnlocalizedParameterAlgebra M k p
  exact { (incidenceParameterPresentationEquiv M k p).toRingEquiv with
    commutes' := incidenceParameterPresentationEquiv_coefficient M k p }

/-- Localizing the unlocalized coefficient map recovers the exact existing
parameter pullback used to define the scheme projection. -/
theorem incidenceParameterUnlocalizedPolynomialMap_localization
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4)
    (f : IncidenceParameterPolynomialRing K) :
    algebraMap (SegreIncidenceChartAlgebra M k p) (SegreIncidenceMinorLocalization M k p)
        (incidenceParameterUnlocalizedPolynomialMap M k p f) =
      incidenceParameterChartMap M k p (incidenceParameterPolynomialChartMap k f) := by
  have he : (IsScalarTower.toAlgHom K (SegreIncidenceChartAlgebra M k p)
      (SegreIncidenceMinorLocalization M k p)).comp
      (incidenceParameterUnlocalizedPolynomialMap M k p) =
      (incidenceParameterChartMap M k p).comp (incidenceParameterPolynomialChartMap k) := by
    ext i
    simp [incidenceParameterUnlocalizedPolynomialMap, incidenceParameterCoordinate]
  exact AlgHom.congr_fun he f

/-- The two incidence equations after actual parameter coefficient change. -/
def incidenceBaseChangedRow (S : Type*) [CommRing S]
    [Algebra (IncidenceParameterPolynomialRing K) S]
    (a : Vec3 (MvPolynomial (Fin 3) K)) : MvPolynomial (Fin 3) S :=
  MvPolynomial.map (algebraMap (IncidenceParameterPolynomialRing K) S)
    (MvPolynomial.commAlgEquiv K (Fin 2) (Fin 3) (rowPolynomial a))

/-- The extended ideal consists exactly of the displayed linear and quadratic
incidence equations; this is an equality, not a kernel hypothesis. -/
theorem incidenceParameterPresentationIdeal_baseChange
    (S : Type*) [CommRing S] [Algebra (IncidenceParameterPolynomialRing K) S]
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4) :
    (incidenceParameterPresentationIdeal M k p).map
      (MvPolynomial.map (algebraMap (IncidenceParameterPolynomialRing K) S)) =
      Ideal.span {incidenceBaseChangedRow S (segreChartRow (netLinearRow M) k p),
        incidenceBaseChangedRow S (segreChartRow (netQuadraticRow M) k p)} := by
  simp only [incidenceParameterPresentationIdeal, affineIncidenceIdeal, Ideal.map_span,
    Set.image_insert_eq, Set.image_singleton, incidenceBaseChangedRow]
  rfl

/-- The actual linear-plus-quadratic quotient over a chosen parameter algebra. -/
abbrev IncidenceBaseChangedAlgebra
    (S : Type*) [CommRing S] [Algebra (IncidenceParameterPolynomialRing K) S]
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4) :=
  MvPolynomial (Fin 3) S ⧸
    Ideal.span {incidenceBaseChangedRow S (segreChartRow (netLinearRow M) k p),
      incidenceBaseChangedRow S (segreChartRow (netQuadraticRow M) k p)}

/-- Tensoring the actual Segre chart over its actual parameter pullback gives
precisely the displayed two-equation quotient in the three spatial variables. -/
def incidenceChartBaseChangeEquiv
    (S : Type*) [CommRing S] [Algebra (IncidenceParameterPolynomialRing K) S]
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4) :
    letI := incidenceUnlocalizedParameterAlgebra M k p
    S ⊗[IncidenceParameterPolynomialRing K] SegreIncidenceChartAlgebra M k p ≃ₐ[S]
      IncidenceBaseChangedAlgebra S M k p := by
  letI := incidenceUnlocalizedParameterAlgebra M k p
  exact (Algebra.TensorProduct.congr (AlgEquiv.refl : S ≃ₐ[S] S)
    (incidenceParameterPresentationEquivOverParameters M k p)).trans
    ((polynomialQuotientBaseChangeEquiv (incidenceParameterPresentationIdeal M k p)).trans
      (Ideal.quotientEquivAlgOfEq S (incidenceParameterPresentationIdeal_baseChange S M k p)))

/-- The chosen parameter algebra acts on the chart tensor product exactly
as coefficients in the displayed quotient. -/
@[simp] theorem incidenceChartBaseChangeEquiv_coefficient
    (S : Type*) [CommRing S] [Algebra (IncidenceParameterPolynomialRing K) S]
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4) (s : S) :
    letI := incidenceUnlocalizedParameterAlgebra M k p
    incidenceChartBaseChangeEquiv S M k p
      (s ⊗ₜ[IncidenceParameterPolynomialRing K] (1 : SegreIncidenceChartAlgebra M k p)) =
      algebraMap S (IncidenceBaseChangedAlgebra S M k p) s := by
  letI := incidenceUnlocalizedParameterAlgebra M k p
  exact (incidenceChartBaseChangeEquiv S M k p).commutes s

/-- The field of actual pulled-back parameters has the literal parameter
polynomial coefficient structure. -/
def incidenceParameterSubfieldPolynomialAlgebra
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4)
    (h : (cross (segreChartRow (netLinearRow M) k p)
      (segreChartRow (netQuadraticRow M) k p)).z ≠ 0) :
    Algebra (IncidenceParameterPolynomialRing K) (incidenceParameterSubfield M k p h) :=
  (aeval (fun i => incidenceGenericParameter M k p h (k.succAbove i))).toRingHom.toAlgebra

/-- Specializing the preceding honest tensor-product presentation to the
actual generated parameter field uses the same actual parameter ratios. -/
def incidenceGenericFiberPresentationEquiv
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4)
    (h : (cross (segreChartRow (netLinearRow M) k p)
      (segreChartRow (netQuadraticRow M) k p)).z ≠ 0) :
    letI := incidenceUnlocalizedParameterAlgebra M k p
    letI := incidenceParameterSubfieldPolynomialAlgebra M k p h
    (incidenceParameterSubfield M k p h) ⊗[IncidenceParameterPolynomialRing K]
        SegreIncidenceChartAlgebra M k p ≃ₐ[incidenceParameterSubfield M k p h]
      IncidenceBaseChangedAlgebra (incidenceParameterSubfield M k p h) M k p := by
  letI := incidenceUnlocalizedParameterAlgebra M k p
  letI := incidenceParameterSubfieldPolynomialAlgebra M k p h
  exact incidenceChartBaseChangeEquiv _ M k p

/-- Composing the actual parameter-field coefficient map with its embedding
in the spatial function field recovers the existing geometric pullback. -/
theorem incidenceParameterSubfieldPolynomialAlgebra_compatibility
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4)
    (h : (cross (segreChartRow (netLinearRow M) k p)
      (segreChartRow (netQuadraticRow M) k p)).z ≠ 0)
    (f : IncidenceParameterPolynomialRing K) :
    letI := incidenceParameterSubfieldPolynomialAlgebra M k p h
    algebraMap (incidenceParameterSubfield M k p h) (IncidenceSpatialFunctionField K)
      (algebraMap (IncidenceParameterPolynomialRing K) (incidenceParameterSubfield M k p h) f) =
      incidenceParameterFunctionFieldMap M k p h (incidenceParameterPolynomialChartMap k f) := by
  letI := incidenceParameterSubfieldPolynomialAlgebra M k p h
  have he : (incidenceParameterSubfield M k p h).val.comp
      (aeval (fun i => incidenceGenericParameter M k p h (k.succAbove i))) =
      (incidenceParameterFunctionFieldMap M k p h).comp (incidenceParameterPolynomialChartMap k) := by
    rw [incidenceParameterFunctionFieldMap_comp_polynomial]
    ext i
    simpa only [AlgHom.comp_apply, aeval_X] using incidenceGenericParameter_succAbove M k p h i
  exact AlgHom.congr_fun he f

/-- The presentation applies the literal normalized Segre substitution. -/
@[simp] theorem incidenceParameterPresentationEquiv_mk
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4)
    (G : MvPolynomial SegreIndex K) :
    incidenceParameterPresentationEquiv M k p (Ideal.Quotient.mk _ G) =
      Ideal.Quotient.mk _ (MvPolynomial.commAlgEquiv K (Fin 2) (Fin 3)
        (segreIncidenceChartSubstitution k p G)) := by
  change (Ideal.quotientEquivAlg _ _
    (MvPolynomial.commAlgEquiv K (Fin 2) (Fin 3)) rfl)
      (segreIncidenceChartAlgEquiv M k p (Ideal.Quotient.mk _ G)) = _
  rw [segreIncidenceChartAlgEquiv_mk]
  rfl

/-- Formula on every tensor generator; hence the base-change isomorphism
retains the actual homogeneous-coordinate quotient map. -/
@[simp] theorem incidenceChartBaseChangeEquiv_tmul_mk
    (S : Type*) [CommRing S] [Algebra (IncidenceParameterPolynomialRing K) S]
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4)
    (s : S) (G : MvPolynomial SegreIndex K) :
    letI := incidenceUnlocalizedParameterAlgebra M k p
    incidenceChartBaseChangeEquiv S M k p
      (s ⊗ₜ[IncidenceParameterPolynomialRing K] (Ideal.Quotient.mk _ G)) =
      algebraMap S _ s * Ideal.Quotient.mk _
        (MvPolynomial.map (algebraMap (IncidenceParameterPolynomialRing K) S)
          (MvPolynomial.commAlgEquiv K (Fin 2) (Fin 3)
            (segreIncidenceChartSubstitution k p G))) := by
  letI := incidenceUnlocalizedParameterAlgebra M k p
  simp only [incidenceChartBaseChangeEquiv, AlgEquiv.trans_apply,
    Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
  change Ideal.quotientEquivAlgOfEq S _
    (polynomialQuotientBaseChangeEquiv (R := IncidenceParameterPolynomialRing K) (S := S)
      (incidenceParameterPresentationIdeal M k p) (s ⊗ₜ[IncidenceParameterPolynomialRing K]
      (incidenceParameterPresentationEquiv M k p (Ideal.Quotient.mk _ G)))) = _
  rw [incidenceParameterPresentationEquiv_mk, polynomialQuotientBaseChangeEquiv_tmul_mk]
  rw [map_mul, AlgEquiv.commutes, Ideal.quotientEquivAlgOfEq_mk]

/-- Reading a nonpivot spatial coordinate after the true parameter base
change gives its corresponding spatial variable. -/
@[simp] theorem incidenceChartBaseChangeEquiv_spatialCoordinate
    (S : Type*) [CommRing S] [Algebra (IncidenceParameterPolynomialRing K) S]
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4) (j : Fin 3) :
    letI := incidenceUnlocalizedParameterAlgebra M k p
    incidenceChartBaseChangeEquiv S M k p
      ((1 : S) ⊗ₜ[IncidenceParameterPolynomialRing K]
        (Ideal.Quotient.mk _ (X (k, p.succAbove j)))) = Ideal.Quotient.mk _ (X j) := by
  letI := incidenceUnlocalizedParameterAlgebra M k p
  rw [incidenceChartBaseChangeEquiv_tmul_mk]
  simp [segreIncidenceChartSubstitution, segreChartY]

/-- The extended row polynomial has the expected two parameter coefficients
and constant parameter-pivot term. -/
theorem incidenceBaseChangedRow_eq
    (S : Type*) [CommRing S] [Algebra (IncidenceParameterPolynomialRing K) S]
    (a : Vec3 (MvPolynomial (Fin 3) K)) :
    incidenceBaseChangedRow S a =
      MvPolynomial.map ((algebraMap (IncidenceParameterPolynomialRing K) S).comp C) a.x *
        C (algebraMap (IncidenceParameterPolynomialRing K) S (X 0)) +
      MvPolynomial.map ((algebraMap (IncidenceParameterPolynomialRing K) S).comp C) a.y *
        C (algebraMap (IncidenceParameterPolynomialRing K) S (X 1)) +
      MvPolynomial.map ((algebraMap (IncidenceParameterPolynomialRing K) S).comp C) a.z := by
  simp only [incidenceBaseChangedRow, rowPolynomial, map_add, map_mul,
    MvPolynomial.commAlgEquiv_C, MvPolynomial.commAlgEquiv_X,
    MvPolynomial.map_C, MvPolynomial.map_map]

/-- Over the actual parameter field the base-changed rows are literally the
normalized linear combination with the actual generic parameter vector. -/
theorem incidenceBaseChangedRow_actualParameter
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4)
    (h : (cross (segreChartRow (netLinearRow M) k p)
      (segreChartRow (netQuadraticRow M) k p)).z ≠ 0)
    (row : Fin 3 → MvPolynomial (Fin 4) K) :
    letI := incidenceParameterSubfieldPolynomialAlgebra M k p h
    incidenceBaseChangedRow (incidenceParameterSubfield M k p h) (segreChartRow row k p) =
      ∑ i : Fin 3, C (incidenceGenericParameter M k p h i) *
        MvPolynomial.map (algebraMap K (incidenceParameterSubfield M k p h))
          (dehomogenizeAt p (row i)) := by
  letI := incidenceParameterSubfieldPolynomialAlgebra M k p h
  have hc : (algebraMap (IncidenceParameterPolynomialRing K)
      (incidenceParameterSubfield M k p h)).comp C =
      algebraMap K (incidenceParameterSubfield M k p h) := by
    apply RingHom.ext
    intro c
    change aeval (fun i : Fin 2 => incidenceGenericParameter M k p h (k.succAbove i)) (C c) = _
    simp
  have ht (i : Fin 2) : algebraMap (IncidenceParameterPolynomialRing K)
      (incidenceParameterSubfield M k p h) (X i) =
      incidenceGenericParameter M k p h (k.succAbove i) := aeval_X _ i
  rw [incidenceBaseChangedRow_eq, hc, ht, ht, Fin.sum_univ_succAbove _ k]
  simp only [segreChartRow, incidenceGenericParameter_pivot, map_one, one_mul,
    Fin.sum_univ_two]
  ring

/-- Inverting the actual homogeneous minor after this presentation inverts
its exact spatial dehomogenization, without changing the selected minor. -/
@[simp] theorem incidenceChartBaseChangeEquiv_minor
    (S : Type*) [CommRing S] [Algebra (IncidenceParameterPolynomialRing K) S]
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4) (i j : Fin 3) :
    letI := incidenceUnlocalizedParameterAlgebra M k p
    incidenceChartBaseChangeEquiv S M k p
      ((1 : S) ⊗ₜ[IncidenceParameterPolynomialRing K]
        (Ideal.Quotient.mk _ (globalIncidenceMinor M i j k))) =
      Ideal.Quotient.mk _
        (MvPolynomial.map ((algebraMap (IncidenceParameterPolynomialRing K) S).comp C)
          (netDehomogenizedMinor M p i j)) := by
  letI := incidenceUnlocalizedParameterAlgebra M k p
  rw [incidenceChartBaseChangeEquiv_tmul_mk,
    segreIncidenceChartSubstitution_minor, MvPolynomial.commAlgEquiv_C,
    MvPolynomial.map_map]
  simp only [map_one, one_mul]

/-- The precise image of the selected minor in the displayed quotient. -/
def incidenceBaseChangedMinor
    (S : Type*) [CommRing S] [Algebra (IncidenceParameterPolynomialRing K) S]
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4) :
    IncidenceBaseChangedAlgebra S M k p :=
  Ideal.Quotient.mk _
    (MvPolynomial.map ((algebraMap (IncidenceParameterPolynomialRing K) S).comp C)
      (netDehomogenizedMinor M p (k.succAbove 0) (k.succAbove 1)))

/-- The actual tensor-product presentation remains an isomorphism after
inverting the selected actual incidence minor. -/
def incidenceChartBaseChangeMinorLocalizationEquiv
    (S : Type*) [CommRing S] [Algebra (IncidenceParameterPolynomialRing K) S]
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4) :
    letI := incidenceUnlocalizedParameterAlgebra M k p
    Localization.Away
      ((1 : S) ⊗ₜ[IncidenceParameterPolynomialRing K] segreIncidenceChartMinor M k p)
      ≃ₐ[S] Localization.Away (incidenceBaseChangedMinor S M k p) := by
  letI := incidenceUnlocalizedParameterAlgebra M k p
  letI : CommRing (S ⊗[IncidenceParameterPolynomialRing K] SegreIncidenceChartAlgebra M k p) :=
    inferInstance
  refine IsLocalization.algEquivOfAlgEquiv
    (M := Submonoid.powers
      ((1 : S) ⊗ₜ[IncidenceParameterPolynomialRing K] segreIncidenceChartMinor M k p))
    (T := Submonoid.powers (incidenceBaseChangedMinor S M k p))
    (Localization.Away
      ((1 : S) ⊗ₜ[IncidenceParameterPolynomialRing K] segreIncidenceChartMinor M k p))
    (Localization.Away (incidenceBaseChangedMinor S M k p))
    (incidenceChartBaseChangeEquiv S M k p) ?_
  rw [Submonoid.map_powers]
  congr 1
  exact incidenceChartBaseChangeEquiv_minor S M k p (k.succAbove 0) (k.succAbove 1)

/-- On the underlying tensor coordinate ring, the localized equivalence is
exactly the preceding coordinate presentation followed by localization. -/
@[simp] theorem incidenceChartBaseChangeMinorLocalizationEquiv_algebraMap
    (S : Type*) [CommRing S] [Algebra (IncidenceParameterPolynomialRing K) S]
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4) :
    letI := incidenceUnlocalizedParameterAlgebra M k p
    ∀ b : S ⊗[IncidenceParameterPolynomialRing K] SegreIncidenceChartAlgebra M k p,
      incidenceChartBaseChangeMinorLocalizationEquiv S M k p (algebraMap _ _ b) =
        algebraMap _ _ (incidenceChartBaseChangeEquiv S M k p b) := by
  letI := incidenceUnlocalizedParameterAlgebra M k p
  intro b
  letI : CommRing (S ⊗[IncidenceParameterPolynomialRing K] SegreIncidenceChartAlgebra M k p) :=
    inferInstance
  unfold incidenceChartBaseChangeMinorLocalizationEquiv
  exact IsLocalization.algEquivOfAlgEquiv_eq _ b

/-- Nonpivot parameter coordinates really become coefficients in the
base-changed presentation, preserving the selected parameter labels. -/
@[simp] theorem incidenceChartBaseChangeEquiv_parameterCoordinate
    (S : Type*) [CommRing S] [Algebra (IncidenceParameterPolynomialRing K) S]
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4) (i : Fin 2) :
    letI := incidenceUnlocalizedParameterAlgebra M k p
    incidenceChartBaseChangeEquiv S M k p
      ((1 : S) ⊗ₜ[IncidenceParameterPolynomialRing K]
        (Ideal.Quotient.mk _ (X (k.succAbove i, p)))) =
      algebraMap S _ (algebraMap (IncidenceParameterPolynomialRing K) S (X i)) := by
  letI := incidenceUnlocalizedParameterAlgebra M k p
  rw [incidenceChartBaseChangeEquiv_tmul_mk]
  simp [segreIncidenceChartSubstitution, segreChartY]
  rfl

end ActualChart

end EvenQuinticConic.Incidence
