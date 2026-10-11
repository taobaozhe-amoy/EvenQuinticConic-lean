import EvenQuinticConic.PlaneJacobianPresentation
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent

/-!
# Actual coordinate differential frames on plane-curve charts

On the derivative principal open of the chart `X i = 1`, the remaining coordinate
`v k` is a genuine differential parameter. We construct a basis of the actual module
of Kähler differentials and identify its sole vector with `d(v k)`, after applying
the actual localization map. No differential module or rank assumption is an input.

This is a statement about the actual affine Kähler module. Its comparison with a
scheme differential sheaf and compatibility across projective charts are separate
steps; they are not part of the hypotheses or conclusions below.
-/

noncomputable section

namespace EvenQuinticConic

open Algebra MvPolynomial Module KaehlerDifferential

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- The complementary basis in a submersive presentation consists of the actual
universal differentials of the chosen generator values. -/
theorem submersive_basisKaehlerOfIsCompl_apply
    {ι σ κ : Type*} [Finite σ] (P : SubmersivePresentation R S ι σ)
    {f : κ → ι} (hf : Function.Injective f)
    (hcompl : IsCompl (Set.range f) (Set.range P.map)) (k : κ) :
    P.basisKaehlerOfIsCompl hf hcompl k = D R S (P.val (f k)) := by
  simp only [SubmersivePresentation.basisKaehlerOfIsCompl,
    Basis.ofSplitExact, Basis.mk_apply, Function.comp_apply,
    Generators.toKaehler_cotangentSpaceBasis]

/-- The explicit standard-smooth presentation of the actual derivative localization. -/
def planeChartJacobianLocalization
    (F : MvPolynomial (Fin 3) R) (i j : Fin 3) (hji : j ≠ i)
    (v : Fin 3 → S) (hv : Function.Surjective (aeval (R := R) v))
    (hker : RingHom.ker (aeval (R := R) v) = Ideal.span {F, X i - 1})
    (T : Type*) [CommRing T] [Algebra R T] [Algebra S T]
    [IsScalarTower R S T] [IsLocalization.Away (aeval v (pderiv j F)) T] :
    SubmersivePresentation R T (Unit ⊕ Fin 3) (Unit ⊕ Fin 2) := by
  let P := planeChartPreSubmersivePresentation F i j hji v hv hker
  haveI : IsLocalization.Away P.jacobian T := by
    rw [show P.jacobian = aeval v (pderiv j F) from
      planeChartPreSubmersivePresentation_jacobian F i j hji v hv hker]
    infer_instance
  exact presentationJacobianLocalization P T

/-- The old chart coordinates remain the images of the actual localization map. -/
theorem planeChartJacobianLocalization_val_inr
    (F : MvPolynomial (Fin 3) R) (i j : Fin 3) (hji : j ≠ i)
    (v : Fin 3 → S) (hv : Function.Surjective (aeval (R := R) v))
    (hker : RingHom.ker (aeval (R := R) v) = Ideal.span {F, X i - 1})
    (T : Type*) [CommRing T] [Algebra R T] [Algebra S T]
    [IsScalarTower R S T] [IsLocalization.Away (aeval v (pderiv j F)) T]
    (k : Fin 3) :
    (planeChartJacobianLocalization F i j hji v hv hker T).val (.inr k) =
      algebraMap S T (v k) := rfl

/-- The remaining coordinate is complementary to the Jacobian columns, including
the extra column used to present the localization. -/
theorem planeChartJacobianLocalization_isCompl
    (F : MvPolynomial (Fin 3) R) (i j k : Fin 3)
    (hji : j ≠ i) (hki : k ≠ i) (hkj : k ≠ j)
    (v : Fin 3 → S) (hv : Function.Surjective (aeval (R := R) v))
    (hker : RingHom.ker (aeval (R := R) v) = Ideal.span {F, X i - 1})
    (T : Type*) [CommRing T] [Algebra R T] [Algebra S T]
    [IsScalarTower R S T] [IsLocalization.Away (aeval v (pderiv j F)) T] :
    IsCompl (Set.range (fun _ : Unit => (Sum.inr k : Unit ⊕ Fin 3)))
      (Set.range (planeChartJacobianLocalization F i j hji v hv hker T).map) := by
  change IsCompl (Set.range (fun _ : Unit => (Sum.inr k : Unit ⊕ Fin 3)))
    (Set.range (Sum.elim (fun _ : Unit => (Sum.inl () : Unit ⊕ Fin 3))
      (fun a : Fin 2 => Sum.inr (![j, i] a))))
  fin_cases i <;> fin_cases j <;> fin_cases k <;> try contradiction
  all_goals
    apply IsCompl.of_eq <;> ext x
    · rcases x with u | l
      · simp [Set.mem_range]
      · fin_cases l <;> simp [Set.mem_range, Fin.exists_fin_succ]
    · rcases x with u | l
      · simp [Set.mem_range]
      · fin_cases l <;> simp [Set.mem_range, Fin.exists_fin_succ]

/-- The actual module of Kähler differentials has the single basis vector given by
the differential of the remaining chart coordinate. -/
def planeChartKaehlerBasis
    (F : MvPolynomial (Fin 3) R) (i j k : Fin 3)
    (hji : j ≠ i) (hki : k ≠ i) (hkj : k ≠ j)
    (v : Fin 3 → S) (hv : Function.Surjective (aeval (R := R) v))
    (hker : RingHom.ker (aeval (R := R) v) = Ideal.span {F, X i - 1})
    (T : Type*) [CommRing T] [Algebra R T] [Algebra S T]
    [IsScalarTower R S T] [IsLocalization.Away (aeval v (pderiv j F)) T] :
    Basis Unit T Ω[T⁄R] :=
  (planeChartJacobianLocalization F i j hji v hv hker T).basisKaehlerOfIsCompl
    (f := fun _ : Unit => Sum.inr k) (by intro a b _; exact Subsingleton.elim a b)
    (planeChartJacobianLocalization_isCompl F i j k hji hki hkj v hv hker T)

/-- The basis vector is an actual universal differential, rather than an abstract
chosen generator of a rank-one free module. -/
theorem planeChartKaehlerBasis_apply
    (F : MvPolynomial (Fin 3) R) (i j k : Fin 3)
    (hji : j ≠ i) (hki : k ≠ i) (hkj : k ≠ j)
    (v : Fin 3 → S) (hv : Function.Surjective (aeval (R := R) v))
    (hker : RingHom.ker (aeval (R := R) v) = Ideal.span {F, X i - 1})
    (T : Type*) [CommRing T] [Algebra R T] [Algebra S T]
    [IsScalarTower R S T] [IsLocalization.Away (aeval v (pderiv j F)) T] :
    planeChartKaehlerBasis F i j k hji hki hkj v hv hker T () =
      D R T (algebraMap S T (v k)) := by
  rw [planeChartKaehlerBasis, submersive_basisKaehlerOfIsCompl_apply]
  rfl

/-- The actual local differential trivialization, oriented from the coefficient
ring to the module of differentials. -/
def planeChartKaehlerTrivialization
    (F : MvPolynomial (Fin 3) R) (i j k : Fin 3)
    (hji : j ≠ i) (hki : k ≠ i) (hkj : k ≠ j)
    (v : Fin 3 → S) (hv : Function.Surjective (aeval (R := R) v))
    (hker : RingHom.ker (aeval (R := R) v) = Ideal.span {F, X i - 1})
    (T : Type*) [CommRing T] [Algebra R T] [Algebra S T]
    [IsScalarTower R S T] [IsLocalization.Away (aeval v (pderiv j F)) T] :
    T ≃ₗ[T] Ω[T⁄R] :=
  (LinearEquiv.funUnique Unit T T).symm.trans
    (planeChartKaehlerBasis F i j k hji hki hkj v hv hker T).equivFun.symm

/-- The local trivialization sends a coefficient to that coefficient times the
universal differential of the remaining actual chart coordinate. -/
theorem planeChartKaehlerTrivialization_apply
    (F : MvPolynomial (Fin 3) R) (i j k : Fin 3)
    (hji : j ≠ i) (hki : k ≠ i) (hkj : k ≠ j)
    (v : Fin 3 → S) (hv : Function.Surjective (aeval (R := R) v))
    (hker : RingHom.ker (aeval (R := R) v) = Ideal.span {F, X i - 1})
    (T : Type*) [CommRing T] [Algebra R T] [Algebra S T]
    [IsScalarTower R S T] [IsLocalization.Away (aeval v (pderiv j F)) T]
    (t : T) :
    planeChartKaehlerTrivialization F i j k hji hki hkj v hv hker T t =
      t • D R T (algebraMap S T (v k)) := by
  simp [planeChartKaehlerTrivialization, planeChartKaehlerBasis_apply]

end EvenQuinticConic
