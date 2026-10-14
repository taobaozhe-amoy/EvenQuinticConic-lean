import EvenQuinticConic.AffinePushforwardPrincipal
import EvenQuinticConic.PrincipalOpenTensorGluing
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Comparison with actual pushforward sections on chart subopens

A principal-localization Kummer model makes the tensor coefficient
presheaf a sheaf on that chart. Principal-open comparison and actual
sheaf separation then identify it with the genuine affine pushforward
on every smaller open, including non-affine opens.
-/

noncomputable section
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

namespace EvenQuinticConic

universe u

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

/-- All principal opens contained in an open cover that open. -/
theorem principalSubopens_cover (V : Opens (PrimeSpectrum.Top R)) :
    V ≤ ⨆ g : {g : R // PrimeSpectrum.basicOpen g ≤ V}, PrimeSpectrum.basicOpen g.val := by
  intro x hx
  obtain ⟨_, ⟨_, ⟨g, rfl⟩, rfl⟩, hxg, hgV⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hx V.2
  exact (le_iSup (fun g : {g : R // PrimeSpectrum.basicOpen g ≤ V} =>
    PrimeSpectrum.basicOpen g.val) ⟨g, hgV⟩) hxg

/-- Restrictions of actual pushforward sections compose. -/
theorem affinePushforwardSectionRestriction_comp
    (V W Z : Opens (PrimeSpectrum.Top R)) (hWV : W ≤ V) (hZW : Z ≤ W)
    (s : (Spec.structureSheaf A).val.obj (op (affinePushforwardOpen (A := A) V))) :
    affinePushforwardSectionRestriction (A := A) W Z hZW
      (affinePushforwardSectionRestriction (A := A) V W hWV s) =
    affinePushforwardSectionRestriction (A := A) V Z (hZW.trans hWV) s := by
  change (Spec.structureSheaf A).val.map _ ((Spec.structureSheaf A).val.map _ s) = _
  rw [← ConcreteCategory.comp_apply, ← (Spec.structureSheaf A).val.map_comp]
  rfl

/-- Actual pushforward sections are determined on every open cover of the base. -/
theorem affinePushforwardSection_eq_of_restrict_eq
    (V : Opens (PrimeSpectrum.Top R)) {ι : Type*} (W : ι → Opens (PrimeSpectrum.Top R))
    (hWV : ∀ i, W i ≤ V) (hcover : V ≤ iSup W)
    (s t : (Spec.structureSheaf A).val.obj (op (affinePushforwardOpen (A := A) V)))
    (heq : ∀ i, affinePushforwardSectionRestriction (A := A) V (W i) (hWV i) s =
      affinePushforwardSectionRestriction (A := A) V (W i) (hWV i) t) : s = t := by
  apply (Spec.structureSheaf A).eq_of_locally_eq'
    (fun i => affinePushforwardOpen (A := A) (W i))
    (affinePushforwardOpen (A := A) V)
    (fun i => homOfLE (show affinePushforwardOpen (A := A) (W i) ≤
      affinePushforwardOpen (A := A) V from fun _ hx => hWV i hx))
  · intro x hx
    have hx' : PrimeSpectrum.comap (algebraMap R A) x ∈ iSup W := hcover hx
    change x ∈ iSup (fun i => affinePushforwardOpen (A := A) (W i))
    simp only [Opens.mem_iSup] at hx' ⊢
    obtain ⟨i, hi⟩ := hx'
    exact ⟨i, hi⟩
  · exact heq

/-- The canonical comparison is bijective on every open inside a principal
Kummer chart. No affineness condition is imposed on the smaller open. -/
theorem affinePushforwardTensorMap_bijective_of_kummerModel
    {f : R} {u : Localization.Away f}
    (e : Localization.Away f ⊗[R] A ≃ₐ[Localization.Away f] KummerAlgebra u)
    (V : Opens (PrimeSpectrum.Top R)) (hV : V ≤ PrimeSpectrum.basicOpen f) :
    Function.Bijective (affinePushforwardTensorMap (A := A) V) := by
  let I := {g : R // PrimeSpectrum.basicOpen g ≤ V}
  let W : I → Opens (PrimeSpectrum.Top R) := fun g => PrimeSpectrum.basicOpen g.val
  have hWV : ∀ i, W i ≤ V := fun i => i.prop
  have hcover : V ≤ iSup W := principalSubopens_cover V
  constructor
  · intro x y hxy
    apply principalOpenTensor_eq_of_restrict_eq e V hV W hWV hcover x y
    intro i
    apply (affinePushforwardTensorMap_basicOpen_bijective (A := A) i.val).1
    rw [← affinePushforwardTensorMap_restrict V (W i) (hWV i),
      ← affinePushforwardTensorMap_restrict V (W i) (hWV i), hxy]
  · intro t
    have hlocal : ∀ i : I, ∃ s,
        affinePushforwardTensorMap (A := A) (W i) s =
          affinePushforwardSectionRestriction (A := A) V (W i) (hWV i) t :=
      fun i => (affinePushforwardTensorMap_basicOpen_bijective (A := A) i.val).2 _
    choose s hs using hlocal
    have hcompat : ∀ i j,
        principalOpenKummerSectionRestriction (W i) (W i ⊓ W j) inf_le_left (s i) =
          principalOpenKummerSectionRestriction (W j) (W i ⊓ W j) inf_le_right (s j) := by
      intro i j
      have hinj : Function.Injective
          (affinePushforwardTensorMap (A := A) (W i ⊓ W j)) := by
        change Function.Injective (affinePushforwardTensorMap (A := A)
          (PrimeSpectrum.basicOpen i.val ⊓ PrimeSpectrum.basicOpen j.val))
        rw [← PrimeSpectrum.basicOpen_mul]
        exact (affinePushforwardTensorMap_basicOpen_bijective (A := A) (i.val * j.val)).1
      apply hinj
      rw [← affinePushforwardTensorMap_restrict (W i) (W i ⊓ W j) inf_le_left,
        ← affinePushforwardTensorMap_restrict (W j) (W i ⊓ W j) inf_le_right,
        hs i, hs j, affinePushforwardSectionRestriction_comp,
        affinePushforwardSectionRestriction_comp]
    obtain ⟨x, hx, _⟩ := existsUnique_principalOpenTensor_gluing e V hV W hWV hcover s hcompat
    refine ⟨x, ?_⟩
    apply affinePushforwardSection_eq_of_restrict_eq V W hWV hcover
    intro i
    rw [affinePushforwardTensorMap_restrict, hx i, hs i]

/-- Actual pushforward sections are canonically the tensor algebra on any
subopen of a principal Kummer chart. -/
def affinePushforwardTensorEquiv
    {f : R} {u : Localization.Away f}
    (e : Localization.Away f ⊗[R] A ≃ₐ[Localization.Away f] KummerAlgebra u)
    (V : Opens (PrimeSpectrum.Top R)) (hV : V ≤ PrimeSpectrum.basicOpen f) :
    ((Spec.structureSheaf R).val.obj (op V) ⊗[R] A) ≃+*
      (Spec.structureSheaf A).val.obj (op (affinePushforwardOpen (A := A) V)) :=
  RingEquiv.ofBijective (affinePushforwardTensorMap (A := A) V)
    (affinePushforwardTensorMap_bijective_of_kummerModel e V hV)

/-- The inverse identification also commutes with all chart-subopen restrictions. -/
theorem affinePushforwardTensorEquiv_symm_restrict
    {f : R} {u : Localization.Away f}
    (e : Localization.Away f ⊗[R] A ≃ₐ[Localization.Away f] KummerAlgebra u)
    (V W : Opens (PrimeSpectrum.Top R)) (hV : V ≤ PrimeSpectrum.basicOpen f)
    (hW : W ≤ PrimeSpectrum.basicOpen f) (hWV : W ≤ V)
    (s : (Spec.structureSheaf A).val.obj (op (affinePushforwardOpen (A := A) V))) :
    (affinePushforwardTensorEquiv e W hW).symm
        (affinePushforwardSectionRestriction (A := A) V W hWV s) =
      principalOpenKummerSectionRestriction V W hWV
        ((affinePushforwardTensorEquiv e V hV).symm s) := by
  apply (affinePushforwardTensorEquiv e W hW).injective
  rw [RingEquiv.apply_symm_apply]
  change _ = affinePushforwardTensorMap (A := A) W _
  rw [← affinePushforwardTensorMap_restrict]
  congr 1
  exact ((affinePushforwardTensorEquiv e V hV).apply_symm_apply s).symm

end EvenQuinticConic
