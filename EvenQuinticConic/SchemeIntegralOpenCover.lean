import Mathlib.AlgebraicGeometry.Properties

/-!
# Integrality from intersecting integral open charts

An actual scheme is integral if it has a nonempty open cover by integral
schemes whose ranges intersect pairwise.  The openness matters: a union of
arbitrary irreducible closed subsets with nonempty intersections need not
be irreducible.
-/

noncomputable section

namespace EvenQuinticConic

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u v

/-- Reducedness descends from every member of an actual open cover, using
the isomorphisms on stalks furnished by the open immersions. -/
theorem scheme_isReduced_of_openCover {X : Scheme.{u}} (𝒰 : Scheme.OpenCover.{v} X)
    (hred : ∀ i, IsReduced (𝒰.X i)) : IsReduced X := by
  apply (config := { allowSynthFailures := true }) isReduced_of_isReduced_stalk
  intro x
  obtain ⟨i, y, hy⟩ := 𝒰.exists_eq x
  letI := hred i
  have hinj : Function.Injective ((𝒰.f i).stalkMap y) :=
    (asIso ((𝒰.f i).stalkMap y)).commRingCatIsoToRingEquiv.injective
  have hyred : _root_.IsReduced (X.presheaf.stalk ((𝒰.f i).base y)) :=
    isReduced_of_injective ((𝒰.f i).stalkMap y).hom hinj
  exact hy ▸ hyred

/-- Every member of a pairwise-intersecting cover by irreducible open
schemes has dense range in the whole scheme. -/
theorem scheme_openCover_denseRange_of_pairwise_intersection
    {X : Scheme.{u}} (𝒰 : Scheme.OpenCover.{v} X)
    (hirr : ∀ i, IrreducibleSpace (𝒰.X i))
    (hinter : ∀ i j,
      (Set.range (𝒰.f i).base ∩ Set.range (𝒰.f j).base).Nonempty)
    (i : 𝒰.I₀) : DenseRange (𝒰.f i).base := by
  apply dense_iff_inter_open.mpr
  intro V hV hVne
  obtain ⟨x, hx⟩ := hVne
  obtain ⟨j, y, hy⟩ := 𝒰.exists_eq x
  letI := hirr j
  have hVj : IsOpen ((𝒰.f j).base ⁻¹' V) :=
    hV.preimage (𝒰.f j).base.hom.continuous
  have hij : IsOpen ((𝒰.f j).base ⁻¹' Set.range (𝒰.f i).base) :=
    (IsOpenImmersion.isOpen_range (𝒰.f i)).preimage
      (𝒰.f j).base.hom.continuous
  have hVjne : (((𝒰.f j).base) ⁻¹' V).Nonempty := ⟨y, by change (𝒰.f j).base y ∈ V; rwa [hy]⟩
  obtain ⟨z, hzi, w, hw⟩ := hinter i j
  have hijne : (((𝒰.f j).base) ⁻¹' Set.range (𝒰.f i).base).Nonempty :=
    ⟨w, by change (𝒰.f j).base w ∈ Set.range (𝒰.f i).base; rwa [hw]⟩
  obtain ⟨t, htV, hti⟩ := nonempty_preirreducible_inter hVj hij hVjne hijne
  exact ⟨(𝒰.f j).base t, htV, hti⟩

/-- A nonempty actual open cover by pairwise-intersecting integral schemes
proves integrality of the covered scheme. -/
theorem scheme_isIntegral_of_openCover
    {X : Scheme.{u}} (𝒰 : Scheme.OpenCover.{v} X) [Nonempty 𝒰.I₀]
    (hint : ∀ i, IsIntegral (𝒰.X i))
    (hinter : ∀ i j,
      (Set.range (𝒰.f i).base ∩ Set.range (𝒰.f j).base).Nonempty) :
    IsIntegral X := by
  letI : IsReduced X := scheme_isReduced_of_openCover 𝒰 fun i =>
    letI := hint i
    inferInstance
  let i : 𝒰.I₀ := Classical.choice inferInstance
  letI := hint i
  have hirr : ∀ j, IrreducibleSpace (𝒰.X j) := fun j =>
    letI := hint j
    inferInstance
  have hd := scheme_openCover_denseRange_of_pairwise_intersection 𝒰 hirr hinter i
  have hrange : IsIrreducible (Set.range (𝒰.f i).base) := by
    simpa only [Set.image_univ] using
      (IrreducibleSpace.isIrreducible_univ (X := 𝒰.X i)).image
        (𝒰.f i).base (𝒰.f i).base.hom.continuous.continuousOn
  have hwhole : IsIrreducible (Set.univ : Set X) := by
    rw [← hd.closure_range]
    exact hrange.closure
  letI : IrreducibleSpace X := (irreducibleSpace_def X).mpr hwhole
  exact isIntegral_of_irreducibleSpace_of_isReduced X

end EvenQuinticConic
