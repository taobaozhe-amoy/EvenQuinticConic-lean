import EvenQuinticConic.SchemePushforwardKummerAtlas

/-!
# Transport of actual pushforward charts along a source isomorphism

The transport below uses the inverse of the isomorphism's map on genuine
structure sheaf sections. Scalar compatibility and restriction compatibility
follow from composition and naturality of scheme morphisms.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
universe u
namespace EvenQuinticConic
variable {X X' Y : Scheme.{u}}

/-- Recover source sections through a scheme isomorphism. -/
def schemeSourceIsoSectionEquiv (e : X ≅ X') (V : X'.Opens) :
    Γ(X, e.hom ⁻¹ᵁ V) ≃+* Γ(X', V) :=
  (asIso (e.hom.app V)).symm.commRingCatIsoToRingEquiv

@[simp] theorem schemeSourceIsoSectionEquiv_symm_apply
    (e : X ≅ X') (V : X'.Opens) (s : Γ(X', V)) :
    (schemeSourceIsoSectionEquiv e V).symm s = e.hom.app V s := rfl

/-- Recovering sections commutes with restriction to smaller opens. -/
theorem schemeSourceIsoSectionEquiv_restrict (e : X ≅ X')
    (V W : X'.Opens) (hWV : W ≤ V) (s : Γ(X, e.hom ⁻¹ᵁ V)) :
    schemeSourceIsoSectionEquiv e W
      (X.presheaf.map ((Opens.map e.hom.base).map (homOfLE hWV)).op s) =
    X'.presheaf.map (homOfLE hWV).op (schemeSourceIsoSectionEquiv e V s) := by
  apply (schemeSourceIsoSectionEquiv e W).symm.injective
  simp only [RingEquiv.symm_apply_apply, schemeSourceIsoSectionEquiv_symm_apply]
  have hn := e.hom.naturality (homOfLE hWV).op
  have hn' := congrArg (fun k => k (schemeSourceIsoSectionEquiv e V s)) hn
  simpa only [CommRingCat.comp_apply, ← schemeSourceIsoSectionEquiv_symm_apply,
    RingEquiv.symm_apply_apply] using hn'.symm

namespace PushforwardKummerChart
variable {g : X' ⟶ Y} {U : Y.Opens} {u : Γ(Y, U)ˣ}

/-- A source isomorphism transports multiplicative coordinates on the actual
pushforward, preserving the same base chart and parameter. -/
def sourceIso (c : PushforwardKummerChart g U u) (e : X ≅ X') :
    PushforwardKummerChart (e.hom ≫ g) U u where
  coordinate V hV := (schemeSourceIsoSectionEquiv e (g ⁻¹ᵁ V)).trans
    (c.coordinate V hV)
  coefficient V hV r := by
    change c.coordinate V hV
      (schemeSourceIsoSectionEquiv e (g ⁻¹ᵁ V) (e.hom.app _ (g.app V r))) = _
    rw [← schemeSourceIsoSectionEquiv_symm_apply, RingEquiv.apply_symm_apply]
    exact c.coefficient V hV r
  re_restrict V W hV hW hWV s := by
    change (c.coordinate W hW (schemeSourceIsoSectionEquiv e (g ⁻¹ᵁ W)
      (X.presheaf.map ((Opens.map e.hom.base).map
        ((Opens.map g.base).map (homOfLE hWV))).op s))).re = _
    have hm : (Opens.map g.base).map (homOfLE hWV) =
        homOfLE (g.preimage_le_preimage_of_le hWV) := Subsingleton.elim _ _
    rw [hm, schemeSourceIsoSectionEquiv_restrict]
    exact c.re_restrict V W hV hW hWV (schemeSourceIsoSectionEquiv e (g ⁻¹ᵁ V) s)
  im_restrict V W hV hW hWV s := by
    change (c.coordinate W hW (schemeSourceIsoSectionEquiv e (g ⁻¹ᵁ W)
      (X.presheaf.map ((Opens.map e.hom.base).map
        ((Opens.map g.base).map (homOfLE hWV))).op s))).im = _
    have hm : (Opens.map g.base).map (homOfLE hWV) =
        homOfLE (g.preimage_le_preimage_of_le hWV) := Subsingleton.elim _ _
    rw [hm, schemeSourceIsoSectionEquiv_restrict]
    exact c.im_restrict V W hV hW hWV (schemeSourceIsoSectionEquiv e (g ⁻¹ᵁ V) s)

/-- Coordinate transport is the inverse source section map followed by the
original coordinates. -/
@[simp] theorem sourceIso_coordinate (c : PushforwardKummerChart g U u)
    (e : X ≅ X') (V : Y.Opens) (hV : V ≤ U)
    (s : Γ(X, (e.hom ≫ g) ⁻¹ᵁ V)) :
    (c.sourceIso e).coordinate V hV s =
      c.coordinate V hV (schemeSourceIsoSectionEquiv e (g ⁻¹ᵁ V) s) := rfl

/-- Use a commuting source-isomorphism triangle stated as an equality of
morphisms. -/
def sourceIsoOfEq (c : PushforwardKummerChart g U u) (e : X ≅ X')
    {f : X ⟶ Y} (h : f = e.hom ≫ g) : PushforwardKummerChart f U u :=
  h ▸ c.sourceIso e

end PushforwardKummerChart
end EvenQuinticConic
