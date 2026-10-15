import EvenQuinticConic.SchemeFiniteEtaleTrace

/-!
# Independence of the affine cover used to construct the trace

The trace is characterized on every multiplicative chart of the original
scheme morphism. Consequently changing the affine cover, its rank proofs,
or its auxiliary instances does not change the trace. The resulting
identification of the actual kernel sheaves preserves their inclusions
into the original pushforward, and is the unique such identification.
-/

noncomputable section
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
universe u
namespace EvenQuinticConic

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] [IsEtale f] [AlgebraicGeometry.Flat f]
    {ι κ : Type u}
    (U : ι → Y.Opens) (hU : iSup U = ⊤)
    (hAffineU : ∀ i, IsAffineOpen (U i))
    [noethU : ∀ i, IsNoetherianRing Γ(Y, U i)]
    [twoU : ∀ i, Invertible (2 : Γ(Y, U i))]
    (hrankU : ∀ i, letI : Algebra Γ(Y, U i) Γ(X, f ⁻¹ᵁ U i) :=
        (f.app (U i)).hom.toAlgebra
      ∀ p : PrimeSpectrum Γ(Y, U i), Module.finrank (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime p.asIdeal ⊗[Γ(Y, U i)] Γ(X, f ⁻¹ᵁ U i)) = 2)
    (V : κ → Y.Opens) (hV : iSup V = ⊤)
    (hAffineV : ∀ i, IsAffineOpen (V i))
    [noethV : ∀ i, IsNoetherianRing Γ(Y, V i)]
    [twoV : ∀ i, Invertible (2 : Γ(Y, V i))]
    (hrankV : ∀ i, letI : Algebra Γ(Y, V i) Γ(X, f ⁻¹ᵁ V i) :=
        (f.app (V i)).hom.toAlgebra
      ∀ p : PrimeSpectrum Γ(Y, V i), Module.finrank (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime p.asIdeal ⊗[Γ(Y, V i)] Γ(X, f ⁻¹ᵁ V i)) = 2)

/-- The actual trace is independent of the affine cover and of all auxiliary
data used to construct it. The two families of instances are passed explicitly. -/
theorem schemeFiniteEtaleTrace_eq_of_cover :
    @schemeFiniteEtaleTrace X Y f _ _ _ ι U hU hAffineU noethU twoU hrankU =
      @schemeFiniteEtaleTrace X Y f _ _ _ κ V hV hAffineV noethV twoV hrankV := by
  apply (@existsUnique_schemeFiniteEtaleTrace X Y f _ _ _ κ V hV hAffineV
    noethV twoV hrankV).choose_spec.2
  intro W w c Z hZ s
  exact @schemeFiniteEtaleTrace_on_chart X Y f _ _ _ ι U hU hAffineU noethU twoU
    hrankU W w c Z hZ s

/-- Changing the construction cover gives equal actual kernel sheaves. -/
theorem schemeFiniteEtaleTraceZeroSheaf_eq_of_cover :
    @schemeFiniteEtaleTraceZeroSheaf X Y f _ _ _ ι U hU hAffineU noethU twoU hrankU =
      @schemeFiniteEtaleTraceZeroSheaf X Y f _ _ _ κ V hV hAffineV noethV twoV hrankV := by
  unfold schemeFiniteEtaleTraceZeroSheaf
  exact congrArg (fun tr ↦ kernel tr)
    (schemeFiniteEtaleTrace_eq_of_cover f U hU hAffineU hrankU V hV hAffineV hrankV)

/-- The canonical comparison of trace-zero sheaves for two affine covers. -/
def schemeFiniteEtaleTraceZeroIsoOfCover :
    @schemeFiniteEtaleTraceZeroSheaf X Y f _ _ _ ι U hU hAffineU noethU twoU hrankU ≅
      @schemeFiniteEtaleTraceZeroSheaf X Y f _ _ _ κ V hV hAffineV noethV twoV hrankV :=
  kernelIsoOfEq
    (schemeFiniteEtaleTrace_eq_of_cover f U hU hAffineU hrankU V hV hAffineV hrankV)

/-- The comparison retains the actual inclusion into the original pushforward. -/
theorem schemeFiniteEtaleTraceZeroIsoOfCover_hom_comp_ι :
    (schemeFiniteEtaleTraceZeroIsoOfCover f U hU hAffineU hrankU V hV hAffineV hrankV).hom ≫
        kernel.ι (@schemeFiniteEtaleTrace X Y f _ _ _ κ V hV hAffineV noethV twoV hrankV) =
      kernel.ι (@schemeFiniteEtaleTrace X Y f _ _ _ ι U hU hAffineU noethU twoU hrankU) :=
  kernelIsoOfEq_hom_comp_ι _

/-- The inverse comparison retains the same inclusion. -/
theorem schemeFiniteEtaleTraceZeroIsoOfCover_inv_comp_ι :
    (schemeFiniteEtaleTraceZeroIsoOfCover f U hU hAffineU hrankU V hV hAffineV hrankV).inv ≫
        kernel.ι (@schemeFiniteEtaleTrace X Y f _ _ _ ι U hU hAffineU noethU twoU hrankU) =
      kernel.ι (@schemeFiniteEtaleTrace X Y f _ _ _ κ V hV hAffineV noethV twoV hrankV) :=
  kernelIsoOfEq_inv_comp_ι _

/-- Any identification retaining the actual kernel inclusions equals the
canonical comparison. Thus the comparison carries no further choice. -/
theorem schemeFiniteEtaleTraceZeroIsoOfCover_unique
    (e : @schemeFiniteEtaleTraceZeroSheaf X Y f _ _ _ ι U hU hAffineU noethU twoU hrankU ≅
      @schemeFiniteEtaleTraceZeroSheaf X Y f _ _ _ κ V hV hAffineV noethV twoV hrankV)
    (he : e.hom ≫
        kernel.ι (@schemeFiniteEtaleTrace X Y f _ _ _ κ V hV hAffineV noethV twoV hrankV) =
      kernel.ι (@schemeFiniteEtaleTrace X Y f _ _ _ ι U hU hAffineU noethU twoU hrankU)) :
    e = schemeFiniteEtaleTraceZeroIsoOfCover f U hU hAffineU hrankU V hV hAffineV hrankV := by
  apply Iso.ext
  apply (cancel_mono
    (kernel.ι (@schemeFiniteEtaleTrace X Y f _ _ _ κ V hV hAffineV noethV twoV hrankV))).1
  exact he.trans
    (schemeFiniteEtaleTraceZeroIsoOfCover_hom_comp_ι f U hU hAffineU hrankU
      V hV hAffineV hrankV).symm

end EvenQuinticConic
