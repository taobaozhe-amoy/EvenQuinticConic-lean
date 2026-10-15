import EvenQuinticConic.SchemeFiniteEtaleKummerAtlas
import EvenQuinticConic.KummerTraceZeroDescent
import EvenQuinticConic.SchemeTwoInvertible

/-!
# The actual trace and trace-zero sheaf without a supplied atlas

The geometric hypotheses construct the multiplicative charts internally.
Their chart-local traces determine one unique morphism of actual module
sheaves. The definition does not replace the sheaf trace on a nonaffine
open by a trace of its global section algebra.
-/

noncomputable section
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
universe u
namespace EvenQuinticConic

/-- Equality with the chart-constructed trace identifies the actual kernel
pairing with multiplication in the original source section rings. -/
theorem pushforwardTraceKernel_squarePairing_of_atlas
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    {κ : Type u} (W : κ → Y.Opens) (hW : iSup W = ⊤)
    (w : ∀ j, Γ(Y, W j)ˣ) (c : ∀ j, PushforwardKummerChart f (W j) (w j))
    (tr : schemePushforwardStructureModule f ⟶ SheafOfModules.unit Y.ringCatSheaf)
    (htr : tr = (pushforwardKummerAtlas W w c).trace hW)
    [∀ V : Y.Opens, Invertible (2 : Γ(Y, V))] :
    ∃ P : ModuleSheafPairing (kernel tr) (kernel tr) (SheafOfModules.unit Y.ringCatSheaf),
      (∀ i V (_hi : V ≤ W i), Function.Bijective (TensorProduct.lift (P.app V))) ∧
      ∀ i V (_hi : V ≤ W i) (s t : (kernel tr).val.obj (op V)),
        f.app V (P.app V s t) =
          (show Γ(X, f ⁻¹ᵁ V) from (kernel.ι tr).val.app (op V) s) *
          (show Γ(X, f ⁻¹ᵁ V) from (kernel.ι tr).val.app (op V) t) := by
  subst tr
  let a := pushforwardKummerAtlas W w c
  refine ⟨a.traceZeroSquarePairing hW, ?_, ?_⟩
  · intro i V hi
    exact a.traceZeroSquarePairing_tensor_bijective hW i V hi
  · intro i V hi s t
    apply ((c i).coordinate V hi).injective
    rw [(c i).coefficient, map_mul]
    exact (a.traceZeroSquarePairing_algebra_mul hW i V hi s t).symm

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] [IsEtale f] [AlgebraicGeometry.Flat f]
    {ι : Type u} (U : ι → Y.Opens) (hU : iSup U = ⊤)
    (hAffine : ∀ i, IsAffineOpen (U i))
    [∀ i, IsNoetherianRing Γ(Y, U i)] [∀ i, Invertible (2 : Γ(Y, U i))]
    (hrank : ∀ i, letI : Algebra Γ(Y, U i) Γ(X, f ⁻¹ᵁ U i) := (f.app (U i)).hom.toAlgebra
      ∀ p : PrimeSpectrum Γ(Y, U i), Module.finrank (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime p.asIdeal ⊗[Γ(Y, U i)] Γ(X, f ⁻¹ᵁ U i)) = 2)

include hU hAffine hrank in
/-- There is a unique actual sheaf trace agreeing with algebra trace on every
multiplicative chart of the original morphism. No atlas is an input. -/
theorem existsUnique_schemeFiniteEtaleTrace :
    ∃! tr : schemePushforwardStructureModule f ⟶ SheafOfModules.unit Y.ringCatSheaf,
      ∀ (W : Y.Opens) (w : Γ(Y, W)ˣ) (d : PushforwardKummerChart f W w)
        (V : Y.Opens) (hV : V ≤ W) (s : Γ(X, f ⁻¹ᵁ V)),
        tr.val.app (op V) s = Algebra.trace Γ(Y, V) _ (d.coordinate V hV s) := by
  obtain ⟨W, hW, w, ⟨c⟩⟩ :=
    exists_schemePushforwardKummerCharts_of_affine_cover f U hU hAffine hrank
  let a := pushforwardKummerAtlas W w c
  refine ⟨a.trace hW, ?_, ?_⟩
  · intro Z z d V hV s
    exact pushforwardKummerAtlas_trace_on_chart W w c hW d V hV s
  · intro tr htr
    apply SheafOfModules.hom_ext
    ext V s
    apply module_eq_of_cover_restrictions W hW V.unop
    intro i
    trans tr.val.app (op (V.unop ⊓ W i))
      (moduleRestrict (schemePushforwardStructureModule f) inf_le_left s)
    · exact (PresheafOfModules.naturality_apply tr.val
        (homOfLE (show V.unop ⊓ W i ≤ V.unop from inf_le_left)).op s).symm
    trans (a.trace hW).val.app (op (V.unop ⊓ W i))
      (moduleRestrict (schemePushforwardStructureModule f) inf_le_left s)
    · exact (htr (W i) (w i) (c i) (V.unop ⊓ W i) inf_le_right _).trans
        (a.trace_apply hW i (V.unop ⊓ W i) inf_le_right _).symm
    exact PresheafOfModules.naturality_apply (a.trace hW).val
      (homOfLE (show V.unop ⊓ W i ≤ V.unop from inf_le_left)).op s

/-- The trace is the uniquely characterized actual module-sheaf morphism. -/
def schemeFiniteEtaleTrace :
    schemePushforwardStructureModule f ⟶ SheafOfModules.unit Y.ringCatSheaf :=
  (existsUnique_schemeFiniteEtaleTrace f U hU hAffine hrank).choose

/-- The constructed trace has the correct value on every actual algebra chart. -/
theorem schemeFiniteEtaleTrace_on_chart
    (W : Y.Opens) (w : Γ(Y, W)ˣ) (d : PushforwardKummerChart f W w)
    (V : Y.Opens) (hV : V ≤ W) (s : Γ(X, f ⁻¹ᵁ V)) :
    (schemeFiniteEtaleTrace f U hU hAffine hrank).val.app (op V) s =
      Algebra.trace Γ(Y, V) _ (d.coordinate V hV s) :=
  (existsUnique_schemeFiniteEtaleTrace f U hU hAffine hrank).choose_spec.1 W w d V hV s

/-- Any covering multiplicative atlas computes the same intrinsically
characterized trace of the original scheme morphism. -/
theorem schemeFiniteEtaleTrace_eq_atlas {κ : Type u} (W : κ → Y.Opens)
    (hW : iSup W = ⊤) (w : ∀ j, Γ(Y, W j)ˣ)
    (c : ∀ j, PushforwardKummerChart f (W j) (w j)) :
    schemeFiniteEtaleTrace f U hU hAffine hrank = (pushforwardKummerAtlas W w c).trace hW := by
  symm
  apply (existsUnique_schemeFiniteEtaleTrace f U hU hAffine hrank).choose_spec.2
  intro Z z d V hV s
  exact pushforwardKummerAtlas_trace_on_chart W w c hW d V hV s

/-- The trace-zero sheaf is the actual categorical kernel of this trace. -/
def schemeFiniteEtaleTraceZeroSheaf : Y.Modules :=
  kernel (schemeFiniteEtaleTrace f U hU hAffine hrank)

/-- A covering multiplicative atlas identifies its kernel with the actual
geometrically constructed trace-zero sheaf. -/
theorem schemeFiniteEtaleTraceZeroSheaf_eq_atlas {κ : Type u} (W : κ → Y.Opens)
    (hW : iSup W = ⊤) (w : ∀ j, Γ(Y, W j)ˣ)
    (c : ∀ j, PushforwardKummerChart f (W j) (w j)) :
    schemeFiniteEtaleTraceZeroSheaf f U hU hAffine hrank =
      (pushforwardKummerAtlas W w c).traceZeroSheaf hW := by
  unfold schemeFiniteEtaleTraceZeroSheaf KummerModuleAtlas.traceZeroSheaf
  simp only [schemeFiniteEtaleTrace_eq_atlas f U hU hAffine hrank W hW w c]

/-- The actual trace kernel has coherent rank-one frames on a covering family.
Invertibility of two on arbitrary opens follows from the supplied affine cover. -/
theorem exists_schemeFiniteEtaleTraceZeroFrames :
    ∃ W : (Σ i, PrimeSpectrum Γ(Y, U i)) → Y.Opens, iSup W = ⊤ ∧
      Nonempty (∀ j, ModuleSheafFrame
        (schemeFiniteEtaleTraceZeroSheaf f U hU hAffine hrank) (W j)) := by
  obtain ⟨W, hW, w, ⟨c⟩⟩ :=
    exists_schemePushforwardKummerCharts_of_affine_cover f U hU hAffine hrank
  refine ⟨W, hW, ⟨?_⟩⟩
  rw [schemeFiniteEtaleTraceZeroSheaf_eq_atlas f U hU hAffine hrank W hW w c]
  letI : ∀ V : Y.Opens, Invertible (2 : Γ(Y, V)) :=
    schemeTwoInvertibleOfCover U hU (fun _ ↦ isUnit_of_invertible _)
  exact (pushforwardKummerAtlas W w c).traceZeroFrame hW

/-- The actual kernel has a locally tensor-perfect square pairing, and on
every chart subopen its value is exactly multiplication in the original
source section ring, followed by descent through the coefficient map. -/
theorem exists_schemeFiniteEtaleTraceZeroSquarePairing :
    ∃ W : (Σ i, PrimeSpectrum Γ(Y, U i)) → Y.Opens, iSup W = ⊤ ∧
      ∃ P : ModuleSheafPairing
        (schemeFiniteEtaleTraceZeroSheaf f U hU hAffine hrank)
        (schemeFiniteEtaleTraceZeroSheaf f U hU hAffine hrank)
        (SheafOfModules.unit Y.ringCatSheaf),
        (∀ i V (_hi : V ≤ W i), Function.Bijective (TensorProduct.lift (P.app V))) ∧
        ∀ i V (_hi : V ≤ W i)
          (s t : (schemeFiniteEtaleTraceZeroSheaf f U hU hAffine hrank).val.obj (op V)),
          f.app V (P.app V s t) =
            (show Γ(X, f ⁻¹ᵁ V) from
              (kernel.ι (schemeFiniteEtaleTrace f U hU hAffine hrank)).val.app (op V) s) *
            (show Γ(X, f ⁻¹ᵁ V) from
              (kernel.ι (schemeFiniteEtaleTrace f U hU hAffine hrank)).val.app (op V) t) := by
  obtain ⟨W, hW, w, ⟨c⟩⟩ :=
    exists_schemePushforwardKummerCharts_of_affine_cover f U hU hAffine hrank
  refine ⟨W, hW, ?_⟩
  let tr := schemeFiniteEtaleTrace f U hU hAffine hrank
  have he : tr = (pushforwardKummerAtlas W w c).trace hW :=
    schemeFiniteEtaleTrace_eq_atlas f U hU hAffine hrank W hW w c
  letI : ∀ V : Y.Opens, Invertible (2 : Γ(Y, V)) :=
    schemeTwoInvertibleOfCover U hU (fun _ ↦ isUnit_of_invertible _)
  exact pushforwardTraceKernel_squarePairing_of_atlas W hW w c tr he

end EvenQuinticConic
