import EvenQuinticConic.IncidenceMinorFromDeterminant
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.CliffordAlgebra.Even

/-!
# Matrix quadratic spaces and their actual even Clifford algebras

The quadratic form here evaluates the existing incidence polynomial. An
invertible matrix congruence gives an actual quadratic-space isometry and
an algebra equivalence between the actual even Clifford subalgebras.
The equivalence preserves the ground field and the products of embedded
vectors. This does not assert a matrix-algebra description after hyperbolic
reduction or a Brauer-class comparison.
-/

noncomputable section

namespace EvenQuinticConic

open Matrix

section EvenFunctor

variable {R V W : Type*} [CommRing R]
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
  {Q : QuadraticForm R V} {Q' : QuadraticForm R W}

/-- The actual map on even Clifford algebras induced by a quadratic isometry. -/
def evenCliffordMap (e : Q →qᵢ Q') :
    CliffordAlgebra.even Q →ₐ[R] CliffordAlgebra.even Q' :=
  CliffordAlgebra.even.lift Q
    { bilin := (CliffordAlgebra.even.ι Q').bilin.compl₁₂ e.toLinearMap e.toLinearMap
      contract := fun v => by
        change (CliffordAlgebra.even.ι Q').bilin (e v) (e v) = _
        rw [CliffordAlgebra.EvenHom.contract, e.map_app]
      contract_mid := fun u v w => by
        change (CliffordAlgebra.even.ι Q').bilin (e u) (e v) *
          (CliffordAlgebra.even.ι Q').bilin (e v) (e w) = _
        rw [CliffordAlgebra.EvenHom.contract_mid, e.map_app]
        rfl }

@[simp] theorem evenCliffordMap_ι (e : Q →qᵢ Q') (u v : V) :
    evenCliffordMap e ((CliffordAlgebra.even.ι Q).bilin u v) =
      (CliffordAlgebra.even.ι Q').bilin (e u) (e v) :=
  CliffordAlgebra.even.lift_ι Q _ u v

/-- The map is the restriction of mathlib's actual map on the full Clifford algebra. -/
theorem evenCliffordMap_coe (e : Q →qᵢ Q') (x : CliffordAlgebra.even Q) :
    (evenCliffordMap e x : CliffordAlgebra Q') =
      CliffordAlgebra.map e (x : CliffordAlgebra Q) := by
  have h : (CliffordAlgebra.even Q').val.comp (evenCliffordMap e) =
      (CliffordAlgebra.map e).comp (CliffordAlgebra.even Q).val := by
    apply CliffordAlgebra.even.algHom_ext
    apply CliffordAlgebra.EvenHom.ext
    apply LinearMap.ext₂
    intro u v
    change (evenCliffordMap e ((CliffordAlgebra.even.ι Q).bilin u v) :
      CliffordAlgebra Q') =
      CliffordAlgebra.map e ((CliffordAlgebra.even.ι Q).bilin u v : CliffordAlgebra Q)
    rw [evenCliffordMap_ι]
    change CliffordAlgebra.ι Q' (e u) * CliffordAlgebra.ι Q' (e v) =
      CliffordAlgebra.map e (CliffordAlgebra.ι Q u * CliffordAlgebra.ι Q v)
    simp only [map_mul, CliffordAlgebra.map_apply_ι]
  exact AlgHom.congr_fun h x

/-- Quadratic-space equivalence induces equivalence of the actual even algebras. -/
def evenCliffordEquivOfIsometry (e : Q.IsometryEquiv Q') :
    CliffordAlgebra.even Q ≃ₐ[R] CliffordAlgebra.even Q' :=
  AlgEquiv.ofAlgHom (evenCliffordMap e.toIsometry)
    (evenCliffordMap e.symm.toIsometry)
    (by
      apply CliffordAlgebra.even.algHom_ext
      apply CliffordAlgebra.EvenHom.ext
      apply LinearMap.ext₂
      intro u v
      simp only [CliffordAlgebra.EvenHom.compr₂_bilin,
        LinearMap.compr₂_apply, AlgHom.toLinearMap_apply,
        AlgHom.comp_apply, evenCliffordMap_ι, AlgHom.id_apply]
      exact congrArg₂ (fun x y => (CliffordAlgebra.even.ι Q').bilin x y)
        (e.toLinearEquiv.apply_symm_apply u) (e.toLinearEquiv.apply_symm_apply v))
    (by
      apply CliffordAlgebra.even.algHom_ext
      apply CliffordAlgebra.EvenHom.ext
      apply LinearMap.ext₂
      intro u v
      simp only [CliffordAlgebra.EvenHom.compr₂_bilin,
        LinearMap.compr₂_apply, AlgHom.toLinearMap_apply,
        AlgHom.comp_apply, evenCliffordMap_ι, AlgHom.id_apply]
      exact congrArg₂ (fun x y => (CliffordAlgebra.even.ι Q).bilin x y)
        (e.toLinearEquiv.symm_apply_apply u) (e.toLinearEquiv.symm_apply_apply v))

@[simp] theorem evenCliffordEquivOfIsometry_ι (e : Q.IsometryEquiv Q') (u v : V) :
    evenCliffordEquivOfIsometry e ((CliffordAlgebra.even.ι Q).bilin u v) =
      (CliffordAlgebra.even.ι Q').bilin (e u) (e v) :=
  evenCliffordMap_ι e.toIsometry u v

end EvenFunctor

namespace Incidence

section MatrixForm

variable {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]

/-- The quadratic form of the actual matrix, with both off-diagonal entries. -/
def matrixQuadraticForm (A : Matrix n n R) : QuadraticForm R (n → R) :=
  A.toBilin'.toQuadraticMap

theorem matrixQuadraticForm_apply (A : Matrix n n R) (x : n → R) :
    matrixQuadraticForm A x = ∑ i, ∑ j, x i * A i j * x j :=
  Matrix.toBilin'_apply A x x

/-- The bundled quadratic form evaluates the previously defined polynomial. -/
theorem matrixQuadraticForm_eq_eval (A : Matrix n n R) (x : n → R) :
    matrixQuadraticForm A x = MvPolynomial.eval x (matrixQuadraticPolynomial A) := by
  simp only [matrixQuadraticForm_apply, matrixQuadraticPolynomial,
    map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
  congr 1
  ext i
  congr 1
  ext j
  ring

/-- Congruence is exactly pullback of the actual quadratic form. -/
theorem matrixQuadraticForm_congruence (A B : Matrix n n R) (x : n → R) :
    matrixQuadraticForm A (B *ᵥ x) = matrixQuadraticForm (Bᵀ * A * B) x := by
  change (A.toBilin'.comp B.toLin' B.toLin') x x = _
  rw [Matrix.toBilin'_comp]
  rfl

/-- The explicit inverse matrix gives the coordinate linear equivalence. -/
def matrixCoordinateEquiv (B : Matrix n n R) (hB : IsUnit B.det) :
    (n → R) ≃ₗ[R] (n → R) where
  __ := B.toLin'
  invFun := fun x => B⁻¹ *ᵥ x
  left_inv x := by
    change B⁻¹ *ᵥ (B *ᵥ x) = x
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul B hB, Matrix.one_mulVec]
  right_inv x := by
    change B *ᵥ (B⁻¹ *ᵥ x) = x
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv B hB, Matrix.one_mulVec]

@[simp] theorem matrixCoordinateEquiv_apply (B : Matrix n n R) (hB : IsUnit B.det)
    (x : n → R) : matrixCoordinateEquiv B hB x = B *ᵥ x := rfl

/-- An actual matrix congruence, with its coordinate map retained. -/
def matrixQuadraticIsometryOfCongruence (A B N : Matrix n n R)
    (hB : IsUnit B.det) (h : Bᵀ * A * B = N) :
    (matrixQuadraticForm N).IsometryEquiv (matrixQuadraticForm A) where
  __ := matrixCoordinateEquiv B hB
  map_app' x := by
    change matrixQuadraticForm A (B *ᵥ x) = matrixQuadraticForm N x
    rw [matrixQuadraticForm_congruence, h]

@[simp] theorem matrixQuadraticIsometryOfCongruence_apply (A B N : Matrix n n R)
    (hB : IsUnit B.det) (h : Bᵀ * A * B = N) (x : n → R) :
    matrixQuadraticIsometryOfCongruence A B N hB h x = B *ᵥ x := rfl

/-- Invertible matrix congruence induces an actual coefficient-preserving equivalence. -/
def matrixEvenCliffordEquivOfCongruence (A B N : Matrix n n R)
    (hB : IsUnit B.det) (h : Bᵀ * A * B = N) :
    CliffordAlgebra.even (matrixQuadraticForm N) ≃ₐ[R]
      CliffordAlgebra.even (matrixQuadraticForm A) :=
  evenCliffordEquivOfIsometry (matrixQuadraticIsometryOfCongruence A B N hB h)

@[simp] theorem matrixEvenCliffordEquivOfCongruence_ι (A B N : Matrix n n R)
    (hB : IsUnit B.det) (h : Bᵀ * A * B = N) (x y : n → R) :
    matrixEvenCliffordEquivOfCongruence A B N hB h
        ((CliffordAlgebra.even.ι (matrixQuadraticForm N)).bilin x y) =
      (CliffordAlgebra.even.ι (matrixQuadraticForm A)).bilin (B *ᵥ x) (B *ᵥ y) :=
  evenCliffordEquivOfIsometry_ι _ x y

end MatrixForm

end Incidence
end EvenQuinticConic
