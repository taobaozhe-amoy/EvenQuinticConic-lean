import EvenQuinticConic.SchemePushforwardOpenChart

/-!
# Global Kummer atlases from local multiplicative charts

Charts on the actual restricted morphisms over a cover of the base produce
one covering atlas on the original pushforward module. The overlaps between
charts coming from different base opens are constructed through the same
actual source section rings, so no cross-open overlap data is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace EvenQuinticConic

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {ι : Type u} (U : ι → Y.Opens)
  {κ : ι → Type u} (V : ∀ i, κ i → (U i).toScheme.Opens)
  (v : ∀ i j, Γ((U i).toScheme, V i j)ˣ)
  (c : ∀ i j, PushforwardKummerChart (f ∣_ U i) (V i j) (v i j))

/-- Assemble actual multiplicative local charts into a global module atlas.
Its overlaps compare the actual multiplication on the original pushforward. -/
def schemePushforwardKummerCoverAtlas :
    KummerModuleAtlas (schemePushforwardStructureModule f)
      (fun p : Σ i, κ i ↦ (U p.1).ι ''ᵁ V p.1 p.2) :=
  pushforwardKummerAtlas (fun p : Σ i, κ i ↦ (U p.1).ι ''ᵁ V p.1 p.2)
    (fun p ↦ v p.1 p.2) (fun p ↦ (c p.1 p.2).openImage)

/-- Assembly preserves the coefficient unit of every original local chart. -/
theorem schemePushforwardKummerCoverAtlas_parameter (p : Σ i, κ i) :
    (schemePushforwardKummerCoverAtlas f U V v c).parameter p = v p.1 p.2 := rfl

include v c in
/-- Local covering charts of the actual restricted morphisms give a covering
atlas of the original pushforward, including all cross-chart overlap maps. -/
theorem exists_schemePushforwardKummerAtlas_of_local_charts
    (hU : iSup U = ⊤) (hV : ∀ i, iSup (V i) = ⊤) :
    ∃ W : (Σ i, κ i) → Y.Opens, iSup W = ⊤ ∧
      Nonempty (KummerModuleAtlas (schemePushforwardStructureModule f) W) := by
  exact ⟨(fun p ↦ (U p.1).ι ''ᵁ V p.1 p.2),
    schemeOpen_image_refinement_cover U hU V hV,
    ⟨schemePushforwardKummerCoverAtlas f U V v c⟩⟩

/-- Existential local constructions produce global multiplicative charts,
retaining the actual ring coordinates needed for trace independence. -/
theorem exists_schemePushforwardKummerCharts_of_local_existence
    (hU : iSup U = ⊤)
    (hlocal : ∀ i, ∃ V : κ i → (U i).toScheme.Opens, iSup V = ⊤ ∧
      ∃ v : ∀ j, Γ((U i).toScheme, V j)ˣ,
        Nonempty (∀ j, PushforwardKummerChart (f ∣_ U i) (V j) (v j))) :
    ∃ W : (Σ i, κ i) → Y.Opens, iSup W = ⊤ ∧
      ∃ w : ∀ j, Γ(Y, W j)ˣ,
        Nonempty (∀ j, PushforwardKummerChart f (W j) (w j)) := by
  classical
  choose V hV v hc using hlocal
  exact ⟨(fun p ↦ (U p.1).ι ''ᵁ V p.1 p.2),
    schemeOpen_image_refinement_cover U hU V hV, (fun p ↦ v p.1 p.2),
    ⟨fun p ↦ (Classical.choice (hc p.1) p.2).openImage⟩⟩

/-- Existential local chart constructions can be assembled without choosing
any local parameters or overlap maps in the theorem's hypotheses. -/
theorem exists_schemePushforwardKummerAtlas_of_local_existence
    (hU : iSup U = ⊤)
    (hlocal : ∀ i, ∃ V : κ i → (U i).toScheme.Opens, iSup V = ⊤ ∧
      ∃ v : ∀ j, Γ((U i).toScheme, V j)ˣ,
        Nonempty (∀ j, PushforwardKummerChart (f ∣_ U i) (V j) (v j))) :
    ∃ W : (Σ i, κ i) → Y.Opens, iSup W = ⊤ ∧
      Nonempty (KummerModuleAtlas (schemePushforwardStructureModule f) W) := by
  obtain ⟨W, hW, w, ⟨c⟩⟩ :=
    exists_schemePushforwardKummerCharts_of_local_existence f U hU hlocal
  exact ⟨W, hW, ⟨pushforwardKummerAtlas W w c⟩⟩

end EvenQuinticConic
