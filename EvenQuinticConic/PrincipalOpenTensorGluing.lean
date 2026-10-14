import EvenQuinticConic.PrincipalOpenKummerSections
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-! # Gluing tensor sections on a principal Kummer chart

Both coordinates glue using the actual structure sheaf. This proves the
required gluing for these tensor algebras without assuming they are sheaves.
-/
noncomputable section
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
namespace EvenQuinticConic
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
variable {f : R} {u : Localization.Away f}
    (e : Localization.Away f ⊗[R] A ≃ₐ[Localization.Away f] KummerAlgebra u)
    (V : Opens (PrimeSpectrum.Top R)) (hV : V ≤ PrimeSpectrum.basicOpen f)
    {ι : Type*} (W : ι → Opens (PrimeSpectrum.Top R)) (hWV : ∀ i, W i ≤ V)
    (hcover : V ≤ iSup W)

include e hV hcover

/-- Tensor sections on a Kummer chart are determined by their restrictions to a cover. -/
theorem principalOpenTensor_eq_of_restrict_eq
    (x y : (Spec.structureSheaf R).val.obj (op V) ⊗[R] A)
    (heq : ∀ i, principalOpenKummerSectionRestriction V (W i) (hWV i) x =
      principalOpenKummerSectionRestriction V (W i) (hWV i) y) : x = y := by
  apply (principalOpenKummerSectionModel e V hV).injective
  apply QuadraticAlgebra.ext
  · apply (Spec.structureSheaf R).eq_of_locally_eq' W V
      (fun i => homOfLE (hWV i)) hcover
    intro i
    rw [← principalOpenKummerSectionModel_re_restrict e V (W i) hV ((hWV i).trans hV),
      ← principalOpenKummerSectionModel_re_restrict e V (W i) hV ((hWV i).trans hV), heq i]
  · apply (Spec.structureSheaf R).eq_of_locally_eq' W V
      (fun i => homOfLE (hWV i)) hcover
    intro i
    rw [← principalOpenKummerSectionModel_im_restrict e V (W i) hV ((hWV i).trans hV),
      ← principalOpenKummerSectionModel_im_restrict e V (W i) hV ((hWV i).trans hV), heq i]

/-- Compatible tensor sections on a Kummer chart glue uniquely on any open cover. -/
theorem existsUnique_principalOpenTensor_gluing
    (s : ∀ i, (Spec.structureSheaf R).val.obj (op (W i)) ⊗[R] A)
    (hcompat : ∀ i j,
      principalOpenKummerSectionRestriction (W i) (W i ⊓ W j) inf_le_left (s i) =
        principalOpenKummerSectionRestriction (W j) (W i ⊓ W j) inf_le_right (s j)) :
    ∃! t : (Spec.structureSheaf R).val.obj (op V) ⊗[R] A,
      ∀ i, principalOpenKummerSectionRestriction V (W i) (hWV i) t = s i := by
  let cr := fun i => (principalOpenKummerSectionModel e (W i) ((hWV i).trans hV) (s i)).re
  let ci := fun i => (principalOpenKummerSectionModel e (W i) ((hWV i).trans hV) (s i)).im
  have hr : TopCat.Presheaf.IsCompatible (Spec.structureSheaf R).val W cr := by
    intro i j
    rw [Subsingleton.elim ((W i).infLELeft (W j)) (homOfLE inf_le_left),
      Subsingleton.elim ((W i).infLERight (W j)) (homOfLE inf_le_right)]
    dsimp only [cr]
    rw [← principalOpenKummerSectionModel_re_restrict e (W i) (W i ⊓ W j)
        ((hWV i).trans hV) (inf_le_left.trans ((hWV i).trans hV)) inf_le_left (s i),
      ← principalOpenKummerSectionModel_re_restrict e (W j) (W i ⊓ W j)
        ((hWV j).trans hV) (inf_le_left.trans ((hWV i).trans hV)) inf_le_right (s j), hcompat i j]
  have hi : TopCat.Presheaf.IsCompatible (Spec.structureSheaf R).val W ci := by
    intro i j
    rw [Subsingleton.elim ((W i).infLELeft (W j)) (homOfLE inf_le_left),
      Subsingleton.elim ((W i).infLERight (W j)) (homOfLE inf_le_right)]
    dsimp only [ci]
    rw [← principalOpenKummerSectionModel_im_restrict e (W i) (W i ⊓ W j)
        ((hWV i).trans hV) (inf_le_left.trans ((hWV i).trans hV)) inf_le_left (s i),
      ← principalOpenKummerSectionModel_im_restrict e (W j) (W i ⊓ W j)
        ((hWV j).trans hV) (inf_le_left.trans ((hWV i).trans hV)) inf_le_right (s j), hcompat i j]
  obtain ⟨r, hr, _⟩ := (Spec.structureSheaf R).existsUnique_gluing' W V
    (fun i => homOfLE (hWV i)) hcover cr hr
  obtain ⟨q, hq, _⟩ := (Spec.structureSheaf R).existsUnique_gluing' W V
    (fun i => homOfLE (hWV i)) hcover ci hi
  let t := (principalOpenKummerSectionModel e V hV).symm ⟨r, q⟩
  have ht : ∀ i, principalOpenKummerSectionRestriction V (W i) (hWV i) t = s i := by
    intro i
    apply (principalOpenKummerSectionModel e (W i) ((hWV i).trans hV)).injective
    apply QuadraticAlgebra.ext
    · rw [principalOpenKummerSectionModel_re_restrict e V (W i) hV ((hWV i).trans hV)]
      simpa [t] using hr i
    · rw [principalOpenKummerSectionModel_im_restrict e V (W i) hV ((hWV i).trans hV)]
      simpa [t] using hq i
  refine ⟨t, ht, ?_⟩
  intro t' ht'
  exact principalOpenTensor_eq_of_restrict_eq e V hV W hWV hcover t' t
    (fun i => (ht' i).trans (ht i).symm)

end EvenQuinticConic
