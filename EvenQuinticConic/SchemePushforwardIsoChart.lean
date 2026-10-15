import EvenQuinticConic.SchemePushforwardSourceIso
import EvenQuinticConic.KummerScalarEquiv

/-!
# Multiplicative Kummer charts under scheme isomorphisms

An isomorphism of arrows transports coordinates on the actual preimage section
rings. The two Kummer coefficients are transported by the actual base section
isomorphism. The parameter, scalar action, and all restrictions are compatible;
no local chart compatibility is assumed beyond that of the original chart.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
universe u
namespace EvenQuinticConic
variable {X Y Z : Scheme.{u}}

/-- Section rings on equal opens are canonically isomorphic. -/
def schemeSectionCongr (X : Scheme.{u}) {U V : X.Opens} (h : U = V) :
    Γ(X, U) ≃+* Γ(X, V) :=
  (X.presheaf.mapIso (eqToIso (congrArg op h))).commRingCatIsoToRingEquiv

@[simp] theorem schemeSectionCongr_rfl (X : Scheme.{u}) (U : X.Opens) :
    schemeSectionCongr X (rfl : U = U) = RingEquiv.refl _ := by
  ext s
  change X.presheaf.map (𝟙 (op U)) s = s
  simp

theorem schemeSectionCongr_apply (X : Scheme.{u}) {U V : X.Opens}
    (h : U = V) (s : Γ(X, U)) :
    schemeSectionCongr X h s = X.presheaf.map (eqToHom h.symm).op s := by
  subst V
  simp

/-- Section identifications commute with restriction. -/
theorem schemeSectionCongr_restrict (X : Scheme.{u})
    {U V U' V' : X.Opens} (hU : U = U') (hV : V = V')
    (hVU : V ≤ U) (hVU' : V' ≤ U') (s : Γ(X, U)) :
    schemeSectionCongr X hV (X.presheaf.map (homOfLE hVU).op s) =
      X.presheaf.map (homOfLE hVU').op (schemeSectionCongr X hU s) := by
  subst U'; subst V'
  simp only [schemeSectionCongr_rfl, RingEquiv.refl_apply]

/-- Restriction of a scheme isomorphism on sections, using its inverse. -/
def schemeIsoSectionEquiv (e : Y ≅ Z) (V : Y.Opens) :
    Γ(Z, e.inv ⁻¹ᵁ V) ≃+* Γ(Y, V) :=
  (asIso (e.inv.app V)).symm.commRingCatIsoToRingEquiv

@[simp] theorem schemeIsoSectionEquiv_symm_apply (e : Y ≅ Z) (V : Y.Opens)
    (s : Γ(Y, V)) : (schemeIsoSectionEquiv e V).symm s = e.inv.app V s := rfl

/-- The section equivalences on a base isomorphism commute with restriction. -/
theorem schemeIsoSectionEquiv_restrict (e : Y ≅ Z) (V W : Y.Opens)
    (hWV : W ≤ V) (s : Γ(Z, e.inv ⁻¹ᵁ V)) :
    schemeIsoSectionEquiv e W
      (Z.presheaf.map ((Opens.map e.inv.base).map (homOfLE hWV)).op s) =
    Y.presheaf.map (homOfLE hWV).op (schemeIsoSectionEquiv e V s) := by
  apply (schemeIsoSectionEquiv e W).symm.injective
  simp only [RingEquiv.symm_apply_apply, schemeIsoSectionEquiv_symm_apply]
  have hn := e.inv.naturality (homOfLE hWV).op
  have hn' := congrArg (fun k => k (schemeIsoSectionEquiv e V s)) hn
  simpa only [CommRingCat.comp_apply, ← schemeIsoSectionEquiv_symm_apply,
    RingEquiv.symm_apply_apply] using hn'.symm

/-- Pulling an open back along an isomorphism and its inverse returns it. -/
theorem schemeIso_preimage_hom_inv (e : Y ≅ Z) (V : Y.Opens) :
    e.hom ⁻¹ᵁ e.inv ⁻¹ᵁ V = V := by
  change (e.hom ≫ e.inv) ⁻¹ᵁ V = V
  rw [e.hom_inv_id]
  rfl

/-- A subopen of the transported chart is a subopen of the original chart. -/
theorem schemeIso_inverseSubopen (e : Y ≅ Z) {U : Z.Opens} {V : Y.Opens}
    (hV : V ≤ e.hom ⁻¹ᵁ U) : e.inv ⁻¹ᵁ V ≤ U := by
  have h := e.inv.preimage_le_preimage_of_le hV
  exact h.trans (le_of_eq (schemeIso_preimage_hom_inv e.symm U))

/-- The isomorphism identifies the source opens of a composite morphism. -/
theorem schemeIso_sourceOpen (f : X ⟶ Y) (e : Y ≅ Z) (V : Y.Opens) :
    f ⁻¹ᵁ V = (f ≫ e.hom) ⁻¹ᵁ e.inv ⁻¹ᵁ V := by
  change f ⁻¹ᵁ V = f ⁻¹ᵁ (e.hom ⁻¹ᵁ e.inv ⁻¹ᵁ V)
  rw [schemeIso_preimage_hom_inv]

/-- Source section transport along the base isomorphism. -/
def schemeIsoSourceSectionEquiv (f : X ⟶ Y) (e : Y ≅ Z) (V : Y.Opens) :
    Γ(X, f ⁻¹ᵁ V) ≃+* Γ(X, (f ≫ e.hom) ⁻¹ᵁ e.inv ⁻¹ᵁ V) :=
  schemeSectionCongr X (schemeIso_sourceOpen f e V)

/-- The genuine coefficient maps commute with this source identification. -/
theorem schemeIsoSourceSectionEquiv_coefficient (f : X ⟶ Y) (e : Y ≅ Z)
    (V : Y.Opens) (r : Γ(Y, V)) :
    schemeIsoSourceSectionEquiv f e V (f.app V r) =
      (f ≫ e.hom).app (e.inv ⁻¹ᵁ V) (e.inv.app V r) := by
  have hcomp : (f ≫ e.hom) ≫ e.inv = f := by simp
  have h := congrArg (fun k => k r) (Scheme.congr_app hcomp V)
  rw [schemeIsoSourceSectionEquiv, schemeSectionCongr_apply]
  simpa only [Scheme.comp_app, CommRingCat.comp_apply] using h.symm

/-- Coefficient units transport with the actual structure sheaf restriction. -/
theorem schemeIsoSectionEquiv_parameter (e : Y ≅ Z) (U : Z.Opens)
    (V : Y.Opens) (hV : V ≤ e.hom ⁻¹ᵁ U) (s : Γ(Z, U)) :
    schemeIsoSectionEquiv e V
      (Z.presheaf.map (homOfLE (schemeIso_inverseSubopen e hV)).op s) =
    Y.presheaf.map (homOfLE hV).op (e.hom.app U s) := by
  apply (schemeIsoSectionEquiv e V).symm.injective
  simp only [RingEquiv.symm_apply_apply, schemeIsoSectionEquiv_symm_apply]
  have hn := e.inv.naturality (homOfLE hV).op
  have hi := Scheme.congr_app e.inv_hom_id U
  have hm : e.hom.app U ≫ Y.presheaf.map (homOfLE hV).op ≫ e.inv.app V =
      Z.presheaf.map (homOfLE (schemeIso_inverseSubopen e hV)).op := by
    rw [hn, ← Category.assoc, ← Scheme.comp_app, hi, Scheme.id_app,
      Category.id_comp, ← Z.presheaf.map_comp]
    congr 1
  exact (congrArg (fun k => k s) hm).symm

/-- Source identifications induced by a base isomorphism respect restrictions. -/
theorem schemeIsoSourceSectionEquiv_restrict (f : X ⟶ Y) (e : Y ≅ Z)
    (V W : Y.Opens) (hWV : W ≤ V) (s : Γ(X, f ⁻¹ᵁ V)) :
    schemeIsoSourceSectionEquiv f e W
      (X.presheaf.map ((Opens.map f.base).map (homOfLE hWV)).op s) =
    X.presheaf.map ((Opens.map (f ≫ e.hom).base).map
      ((Opens.map e.inv.base).map (homOfLE hWV))).op
      (schemeIsoSourceSectionEquiv f e V s) :=
  schemeSectionCongr_restrict X (schemeIso_sourceOpen f e V)
    (schemeIso_sourceOpen f e W) _ _ s

namespace PushforwardKummerChart
variable {f : X ⟶ Y} (e : Y ≅ Z) {U : Z.Opens} {u : Γ(Z, U)ˣ}
  (c : PushforwardKummerChart (f ≫ e.hom) U u)

/-- The transported coordinate ring isomorphism, on every subopen. -/
def baseIsoCoordinate (V : Y.Opens) (hV : V ≤ e.hom ⁻¹ᵁ U) :
    Γ(X, f ⁻¹ᵁ V) ≃+*
      KummerAlgebra (Y.presheaf.map (homOfLE hV).op (e.hom.app U (u : Γ(Z, U)))) :=
  ((schemeIsoSourceSectionEquiv f e V).trans
    (c.coordinate (e.inv ⁻¹ᵁ V) (schemeIso_inverseSubopen e hV))).trans
    (kummerScalarEquivOfEq (schemeIsoSectionEquiv e V)
      (schemeIsoSectionEquiv_parameter e U V hV (u : Γ(Z, U))))

/-- A base scheme isomorphism transports genuine multiplicative charts. -/
def baseIso : PushforwardKummerChart f (e.hom ⁻¹ᵁ U)
    (Units.map (e.hom.app U).hom.toMonoidHom u) where
  coordinate := c.baseIsoCoordinate e
  coefficient V hV r := by
    change kummerScalarEquivOfEq (schemeIsoSectionEquiv e V)
      (schemeIsoSectionEquiv_parameter e U V hV (u : Γ(Z, U)))
      (c.coordinate _ _ (schemeIsoSourceSectionEquiv f e V (f.app V r))) = _
    rw [schemeIsoSourceSectionEquiv_coefficient, c.coefficient,
      kummerScalarEquivOfEq_algebraMap]
    congr 1
    exact (schemeIsoSectionEquiv e V).apply_symm_apply r
  re_restrict V W hV hW hWV s := by
    change schemeIsoSectionEquiv e W
      (c.coordinate _ _ (schemeIsoSourceSectionEquiv f e W
        (X.presheaf.map ((Opens.map f.base).map (homOfLE hWV)).op s))).re =
      Y.presheaf.map (homOfLE hWV).op
        (schemeIsoSectionEquiv e V
          (c.coordinate _ _ (schemeIsoSourceSectionEquiv f e V s)).re)
    rw [schemeIsoSourceSectionEquiv_restrict]
    have hmap : (Opens.map e.inv.base).map (homOfLE hWV) =
        homOfLE (e.inv.preimage_le_preimage_of_le hWV) := Subsingleton.elim _ _
    rw [hmap, c.re_restrict]
    simpa only [hmap] using schemeIsoSectionEquiv_restrict e V W hWV
      (c.coordinate _ (schemeIso_inverseSubopen e hV)
        (schemeIsoSourceSectionEquiv f e V s)).re
  im_restrict V W hV hW hWV s := by
    change schemeIsoSectionEquiv e W
      (c.coordinate _ _ (schemeIsoSourceSectionEquiv f e W
        (X.presheaf.map ((Opens.map f.base).map (homOfLE hWV)).op s))).im =
      Y.presheaf.map (homOfLE hWV).op
        (schemeIsoSectionEquiv e V
          (c.coordinate _ _ (schemeIsoSourceSectionEquiv f e V s)).im)
    rw [schemeIsoSourceSectionEquiv_restrict]
    have hmap : (Opens.map e.inv.base).map (homOfLE hWV) =
        homOfLE (e.inv.preimage_le_preimage_of_le hWV) := Subsingleton.elim _ _
    rw [hmap, c.im_restrict]
    simpa only [hmap] using schemeIsoSectionEquiv_restrict e V W hWV
      (c.coordinate _ (schemeIso_inverseSubopen e hV)
        (schemeIsoSourceSectionEquiv f e V s)).im

/-- Coordinates under base transport apply the genuine coefficient-ring
isomorphism independently to the two Kummer coefficients. -/
@[simp] theorem baseIso_coordinate_re (V : Y.Opens) (hV : V ≤ e.hom ⁻¹ᵁ U)
    (s : Γ(X, f ⁻¹ᵁ V)) :
    ((c.baseIso e).coordinate V hV s).re =
      schemeIsoSectionEquiv e V
        (c.coordinate _ (schemeIso_inverseSubopen e hV)
          (schemeIsoSourceSectionEquiv f e V s)).re := rfl

@[simp] theorem baseIso_coordinate_im (V : Y.Opens) (hV : V ≤ e.hom ⁻¹ᵁ U)
    (s : Γ(X, f ⁻¹ᵁ V)) :
    ((c.baseIso e).coordinate V hV s).im =
      schemeIsoSectionEquiv e V
        (c.coordinate _ (schemeIso_inverseSubopen e hV)
          (schemeIsoSourceSectionEquiv f e V s)).im := rfl

end PushforwardKummerChart

namespace PushforwardKummerChart
variable {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {g : X' ⟶ Y'}
  {U : Y'.Opens} {u : Γ(Y', U)ˣ}

/-- An isomorphism of scheme arrows transports the actual ring coordinates,
including their coefficient and restriction laws. -/
def isoTransport (c : PushforwardKummerChart g U u)
    (eX : X ≅ X') (eY : Y ≅ Y') (hcomm : f ≫ eY.hom = eX.hom ≫ g) :
    PushforwardKummerChart f (eY.hom ⁻¹ᵁ U)
      (Units.map (eY.hom.app U).hom.toMonoidHom u) :=
  (c.sourceIsoOfEq eX hcomm).baseIso eY

end PushforwardKummerChart

end EvenQuinticConic
