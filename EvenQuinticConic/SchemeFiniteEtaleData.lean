import EvenQuinticConic.SchemeFiniteEtaleTrace

/-!
# Chosen geometric Kummer data and the canonical trace kernel

The choices in this file select witnesses of the proved geometric existence
theorem. They do not introduce a supplied atlas or a supplied line bundle.
The resulting descent isomorphism starts from the categorical kernel of the
uniquely characterized trace of the original scheme morphism.
-/

noncomputable section
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
universe u
namespace EvenQuinticConic

/-- A covering family of actual multiplicative charts of a fixed morphism. -/
structure PushforwardKummerCover {X Y : Scheme.{u}} (f : X ⟶ Y) (κ : Type u) where
  openSet : κ → Y.Opens
  cover : iSup openSet = ⊤
  parameter : ∀ j, Γ(Y, openSet j)ˣ
  chart : ∀ j, PushforwardKummerChart f (openSet j) (parameter j)

/-- Actual multiplicative charts supply their overlap maps internally. -/
def PushforwardKummerCover.moduleAtlas {X Y : Scheme.{u}} {f : X ⟶ Y} {κ : Type u}
    (d : PushforwardKummerCover f κ) :
    KummerModuleAtlas (schemePushforwardStructureModule f) d.openSet :=
  pushforwardKummerAtlas d.openSet d.parameter d.chart

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] [IsEtale f] [AlgebraicGeometry.Flat f]
    {ι : Type u} (U : ι → Y.Opens) (hU : iSup U = ⊤)
    (hAffine : ∀ i, IsAffineOpen (U i))
    [∀ i, IsNoetherianRing Γ(Y, U i)] [∀ i, Invertible (2 : Γ(Y, U i))]
    (hrank : ∀ i, letI : Algebra Γ(Y, U i) Γ(X, f ⁻¹ᵁ U i) := (f.app (U i)).hom.toAlgebra
      ∀ p : PrimeSpectrum Γ(Y, U i), Module.finrank (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime p.asIdeal ⊗[Γ(Y, U i)] Γ(X, f ⁻¹ᵁ U i)) = 2)

/-- Choose actual covering charts from the proved finite-etale construction. -/
def finiteEtaleKummerCover :
    PushforwardKummerCover f (Σ i, PrimeSpectrum Γ(Y, U i)) := by
  have hex : Nonempty (PushforwardKummerCover f (Σ i, PrimeSpectrum Γ(Y, U i))) := by
    obtain ⟨W, hW, w, ⟨c⟩⟩ :=
      exists_schemePushforwardKummerCharts_of_affine_cover f U hU hAffine hrank
    exact ⟨⟨W, hW, w, c⟩⟩
  exact Classical.choice hex

/-- The selected charts compute the uniquely characterized original trace. -/
theorem finiteEtaleKummerCover_trace :
    schemeFiniteEtaleTrace f U hU hAffine hrank =
      (finiteEtaleKummerCover f U hU hAffine hrank).moduleAtlas.trace
        (finiteEtaleKummerCover f U hU hAffine hrank).cover :=
  schemeFiniteEtaleTrace_eq_atlas f U hU hAffine hrank _ _ _ _

/-- The selected atlas kernel is the actual canonical trace kernel. -/
theorem finiteEtaleKummerCover_traceZeroSheaf_eq :
    schemeFiniteEtaleTraceZeroSheaf f U hU hAffine hrank =
      (finiteEtaleKummerCover f U hU hAffine hrank).moduleAtlas.traceZeroSheaf
        (finiteEtaleKummerCover f U hU hAffine hrank).cover :=
  schemeFiniteEtaleTraceZeroSheaf_eq_atlas f U hU hAffine hrank _ _ _ _

/-- Comparison of kernels, induced by the identity of the underlying traces. -/
def schemeFiniteEtaleTraceZeroAtlasIso :
    schemeFiniteEtaleTraceZeroSheaf f U hU hAffine hrank ≅
      (finiteEtaleKummerCover f U hU hAffine hrank).moduleAtlas.traceZeroSheaf
        (finiteEtaleKummerCover f U hU hAffine hrank).cover :=
  kernel.mapIso _ _ (Iso.refl _) (Iso.refl _)
    (by simpa using finiteEtaleKummerCover_trace f U hU hAffine hrank)

/-- Kernel comparison preserves the inclusion into the original pushforward. -/
theorem schemeFiniteEtaleTraceZeroAtlasIso_hom_ι :
    (schemeFiniteEtaleTraceZeroAtlasIso f U hU hAffine hrank).hom ≫
      kernel.ι ((finiteEtaleKummerCover f U hU hAffine hrank).moduleAtlas.trace
        (finiteEtaleKummerCover f U hU hAffine hrank).cover) =
      kernel.ι (schemeFiniteEtaleTrace f U hU hAffine hrank) := by
  simp [schemeFiniteEtaleTraceZeroAtlasIso, kernel.mapIso, kernel.map]

/-- The line cocycle is extracted from the internally selected actual charts. -/
def schemeFiniteEtaleTraceZeroTransition :
    UnitTransition Y (finiteEtaleKummerCover f U hU hAffine hrank).openSet := by
  letI : ∀ V : Y.Opens, Invertible (2 : Γ(Y, V)) :=
    schemeTwoInvertibleOfCover U hU (fun _ ↦ isUnit_of_invertible _)
  exact (finiteEtaleKummerCover f U hU hAffine hrank).moduleAtlas.traceZeroTransition
    (finiteEtaleKummerCover f U hU hAffine hrank).cover

/-- Descent identifies the canonical trace kernel itself with the extracted line. -/
def schemeFiniteEtaleTraceZeroDescentIso :
    schemeFiniteEtaleTraceZeroSheaf f U hU hAffine hrank ≅
      (schemeFiniteEtaleTraceZeroTransition f U hU hAffine hrank).moduleSheaf := by
  letI : ∀ V : Y.Opens, Invertible (2 : Γ(Y, V)) :=
    schemeTwoInvertibleOfCover U hU (fun _ ↦ isUnit_of_invertible _)
  exact schemeFiniteEtaleTraceZeroAtlasIso f U hU hAffine hrank ≪≫
    (finiteEtaleKummerCover f U hU hAffine hrank).moduleAtlas.traceZeroDescentIso
      (finiteEtaleKummerCover f U hU hAffine hrank).cover

/-- Multiplication supplies the square trivialization of the extracted line. -/
def schemeFiniteEtaleTraceZeroSquareIso :
    ((schemeFiniteEtaleTraceZeroTransition f U hU hAffine hrank).mul
      (schemeFiniteEtaleTraceZeroTransition f U hU hAffine hrank)).moduleSheaf ≅
        SheafOfModules.unit Y.ringCatSheaf := by
  letI : ∀ V : Y.Opens, Invertible (2 : Γ(Y, V)) :=
    schemeTwoInvertibleOfCover U hU (fun _ ↦ isUnit_of_invertible _)
  exact (finiteEtaleKummerCover f U hU hAffine hrank).moduleAtlas.traceZeroSquareIso
    (finiteEtaleKummerCover f U hU hAffine hrank).cover

end EvenQuinticConic
