import EvenQuinticConic.SchemePushforwardKummerAtlas
import EvenQuinticConic.SchemePushforwardRestriction
import EvenQuinticConic.KummerModuleTransport

/-!
# Multiplicative pushforward charts on image opens

A chart of the restriction of an actual scheme morphism gives a chart on the
corresponding image open of its original base. The coordinate comparison is
the actual structure-sheaf ring isomorphism; in particular, multiplication and
the coefficient map are preserved as well as the restriction maps.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace EvenQuinticConic

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Equality of base opens transports genuine multiplicative coordinates. -/
def pushforwardKummerCoordinateTransport {U V V' : Y.Opens}
    (u : Γ(Y, U)ˣ) (h : V' = V) (hV : V ≤ U) (hV' : V' ≤ U)
    (e : Γ(X, f ⁻¹ᵁ V') ≃+*
      KummerAlgebra (Y.presheaf.map (homOfLE hV').op (u : Γ(Y, U)))) :
    Γ(X, f ⁻¹ᵁ V) ≃+*
      KummerAlgebra (Y.presheaf.map (homOfLE hV).op (u : Γ(Y, U))) := by
  subst V'
  exact e

/-- The actual coefficient law survives equality transport. -/
theorem pushforwardKummerCoordinateTransport_coefficient {U V V' : Y.Opens}
    (u : Γ(Y, U)ˣ) (h : V' = V) (hV : V ≤ U) (hV' : V' ≤ U)
    (e : Γ(X, f ⁻¹ᵁ V') ≃+*
      KummerAlgebra (Y.presheaf.map (homOfLE hV').op (u : Γ(Y, U))))
    (he : ∀ r, e (f.app V' r) = algebraMap _ _ r) (r : Γ(Y, V)) :
    pushforwardKummerCoordinateTransport f u h hV hV' e (f.app V r) =
      algebraMap _ _ r := by
  subst V'
  exact he r

/-- Both coordinate restriction laws survive equality transport. -/
theorem pushforwardKummerCoordinateTransport_restrict {U V W V' W' : Y.Opens}
    (u : Γ(Y, U)ˣ) (hV : V' = V) (hW : W' = W)
    (hVU : V ≤ U) (hWU : W ≤ U) (hV'U : V' ≤ U) (hW'U : W' ≤ U)
    (hWV : W ≤ V) (hW'V' : W' ≤ V')
    (eV : Γ(X, f ⁻¹ᵁ V') ≃+*
      KummerAlgebra (Y.presheaf.map (homOfLE hV'U).op (u : Γ(Y, U))))
    (eW : Γ(X, f ⁻¹ᵁ W') ≃+*
      KummerAlgebra (Y.presheaf.map (homOfLE hW'U).op (u : Γ(Y, U))))
    (he : ∀ s,
      (eW (X.presheaf.map ((Opens.map f.base).map (homOfLE hW'V')).op s)).re =
        Y.presheaf.map (homOfLE hW'V').op (eV s).re ∧
      (eW (X.presheaf.map ((Opens.map f.base).map (homOfLE hW'V')).op s)).im =
        Y.presheaf.map (homOfLE hW'V').op (eV s).im)
    (s : Γ(X, f ⁻¹ᵁ V)) :
    (pushforwardKummerCoordinateTransport f u hW hWU hW'U eW
      (X.presheaf.map ((Opens.map f.base).map (homOfLE hWV)).op s)).re =
        Y.presheaf.map (homOfLE hWV).op
          (pushforwardKummerCoordinateTransport f u hV hVU hV'U eV s).re ∧
    (pushforwardKummerCoordinateTransport f u hW hWU hW'U eW
      (X.presheaf.map ((Opens.map f.base).map (homOfLE hWV)).op s)).im =
        Y.presheaf.map (homOfLE hWV).op
          (pushforwardKummerCoordinateTransport f u hV hVU hV'U eV s).im := by
  subst V'
  subst W'
  exact he s

namespace PushforwardKummerChart

variable {f} {U : Y.Opens} {V : U.toScheme.Opens} {u : Γ(U.toScheme, V)ˣ}
  (c : PushforwardKummerChart (f ∣_ U) V u)

/-- Coordinates on an actual image open, before identifying equal base opens. -/
def imageCoordinate (W : U.toScheme.Opens) (hW : W ≤ V) :
    Γ(X, f ⁻¹ᵁ (U.ι ''ᵁ W)) ≃+*
      KummerAlgebra (Y.presheaf.map
        (homOfLE (U.ι.image_le_image_of_le hW)).op (u : Γ(U.toScheme, V))) :=
  (schemePushforwardRestrictionRingEquiv f U W).trans (c.coordinate W hW)

/-- Image coordinates preserve the coefficient map of the original morphism. -/
theorem imageCoordinate_coefficient (W : U.toScheme.Opens) (hW : W ≤ V)
    (r : Γ(Y, U.ι ''ᵁ W)) :
    c.imageCoordinate W hW (f.app (U.ι ''ᵁ W) r) = algebraMap _ _ r := by
  change c.coordinate W hW
    (schemePushforwardRestrictionRingEquiv f U W (f.app (U.ι ''ᵁ W) r)) = _
  rw [schemePushforwardRestrictionRingEquiv_coefficient, c.coefficient]
  rfl

/-- Image coordinates preserve both actual coordinate restriction maps. -/
theorem imageCoordinate_restrict (W Z : U.toScheme.Opens)
    (hW : W ≤ V) (hZ : Z ≤ V) (hZW : Z ≤ W)
    (s : Γ(X, f ⁻¹ᵁ (U.ι ''ᵁ W))) :
    (c.imageCoordinate Z hZ
      (X.presheaf.map ((Opens.map f.base).map
        (homOfLE (U.ι.image_le_image_of_le hZW))).op s)).re =
      Y.presheaf.map (homOfLE (U.ι.image_le_image_of_le hZW)).op
        (c.imageCoordinate W hW s).re ∧
    (c.imageCoordinate Z hZ
      (X.presheaf.map ((Opens.map f.base).map
        (homOfLE (U.ι.image_le_image_of_le hZW))).op s)).im =
      Y.presheaf.map (homOfLE (U.ι.image_le_image_of_le hZW)).op
        (c.imageCoordinate W hW s).im := by
  have hn := schemePushforwardRestrictionLinearMap_restrict f U W Z hZW s
  change schemePushforwardRestrictionRingEquiv f U Z
      (X.presheaf.map ((Opens.map f.base).map
        (homOfLE (U.ι.image_le_image_of_le hZW))).op s) =
    (f ⁻¹ᵁ U).toScheme.presheaf.map
      ((Opens.map (f ∣_ U).base).map (homOfLE hZW)).op
      (schemePushforwardRestrictionRingEquiv f U W s) at hn
  change (c.coordinate Z hZ
      (schemePushforwardRestrictionRingEquiv f U Z _)).re = _ ∧
    (c.coordinate Z hZ
      (schemePushforwardRestrictionRingEquiv f U Z _)).im = _
  rw [hn]
  exact ⟨c.re_restrict W Z hW hZ hZW _, c.im_restrict W Z hW hZ hZW _⟩

/-- Descend a multiplicative chart of a restricted morphism to the original
scheme. All coordinates are isomorphisms of actual source section rings. -/
def openImage : PushforwardKummerChart f (U.ι ''ᵁ V) u where
  coordinate W hW := pushforwardKummerCoordinateTransport f u
    (schemeOpen_image_preimage_of_le U W (hW.trans (U.ι_image_le V))) hW
    (U.ι.image_le_image_of_le (schemeOpen_preimage_le_of_le_image U V W hW))
    (c.imageCoordinate (U.ι ⁻¹ᵁ W) (schemeOpen_preimage_le_of_le_image U V W hW))
  coefficient W hW r := by
    exact pushforwardKummerCoordinateTransport_coefficient f u
      (schemeOpen_image_preimage_of_le U W (hW.trans (U.ι_image_le V))) hW
      (U.ι.image_le_image_of_le (schemeOpen_preimage_le_of_le_image U V W hW))
      (c.imageCoordinate (U.ι ⁻¹ᵁ W) (schemeOpen_preimage_le_of_le_image U V W hW))
      (c.imageCoordinate_coefficient (U.ι ⁻¹ᵁ W)
        (schemeOpen_preimage_le_of_le_image U V W hW)) r
  re_restrict W Z hW hZ hZW s := by
    exact (pushforwardKummerCoordinateTransport_restrict f u
      (schemeOpen_image_preimage_of_le U W (hW.trans (U.ι_image_le V)))
      (schemeOpen_image_preimage_of_le U Z (hZ.trans (U.ι_image_le V))) hW hZ
      (U.ι.image_le_image_of_le (schemeOpen_preimage_le_of_le_image U V W hW))
      (U.ι.image_le_image_of_le (schemeOpen_preimage_le_of_le_image U V Z hZ))
      hZW (U.ι.image_le_image_of_le
        (show U.ι ⁻¹ᵁ Z ≤ U.ι ⁻¹ᵁ W from fun _ hx ↦ hZW hx))
      (c.imageCoordinate (U.ι ⁻¹ᵁ W) (schemeOpen_preimage_le_of_le_image U V W hW))
      (c.imageCoordinate (U.ι ⁻¹ᵁ Z) (schemeOpen_preimage_le_of_le_image U V Z hZ))
      (c.imageCoordinate_restrict (U.ι ⁻¹ᵁ W) (U.ι ⁻¹ᵁ Z)
        (schemeOpen_preimage_le_of_le_image U V W hW)
        (schemeOpen_preimage_le_of_le_image U V Z hZ)
        (show U.ι ⁻¹ᵁ Z ≤ U.ι ⁻¹ᵁ W from fun _ hx ↦ hZW hx)) s).1
  im_restrict W Z hW hZ hZW s := by
    exact (pushforwardKummerCoordinateTransport_restrict f u
      (schemeOpen_image_preimage_of_le U W (hW.trans (U.ι_image_le V)))
      (schemeOpen_image_preimage_of_le U Z (hZ.trans (U.ι_image_le V))) hW hZ
      (U.ι.image_le_image_of_le (schemeOpen_preimage_le_of_le_image U V W hW))
      (U.ι.image_le_image_of_le (schemeOpen_preimage_le_of_le_image U V Z hZ))
      hZW (U.ι.image_le_image_of_le
        (show U.ι ⁻¹ᵁ Z ≤ U.ι ⁻¹ᵁ W from fun _ hx ↦ hZW hx))
      (c.imageCoordinate (U.ι ⁻¹ᵁ W) (schemeOpen_preimage_le_of_le_image U V W hW))
      (c.imageCoordinate (U.ι ⁻¹ᵁ Z) (schemeOpen_preimage_le_of_le_image U V Z hZ))
      (c.imageCoordinate_restrict (U.ι ⁻¹ᵁ W) (U.ι ⁻¹ᵁ Z)
        (schemeOpen_preimage_le_of_le_image U V W hW)
        (schemeOpen_preimage_le_of_le_image U V Z hZ)
        (show U.ι ⁻¹ᵁ Z ≤ U.ι ⁻¹ᵁ W from fun _ hx ↦ hZW hx)) s).2

/-- Image coordinates at equal subopens agree under equality transport. -/
theorem imageCoordinate_transport (W Z : U.toScheme.Opens) (h : W = Z)
    (hW : W ≤ V) (hZ : Z ≤ V) (himage : U.ι ''ᵁ W = U.ι ''ᵁ Z) :
    pushforwardKummerCoordinateTransport f u himage
      (U.ι.image_le_image_of_le hZ) (U.ι.image_le_image_of_le hW)
      (c.imageCoordinate W hW) = c.imageCoordinate Z hZ := by
  subst Z
  rfl

/-- On an actual image open, the descended coordinate is precisely the
original coordinate after the actual structure-section comparison. -/
theorem openImage_coordinate_image (W : U.toScheme.Opens) (hW : W ≤ V)
    (s : Γ(X, f ⁻¹ᵁ (U.ι ''ᵁ W))) :
    c.openImage.coordinate (U.ι ''ᵁ W) (U.ι.image_le_image_of_le hW) s =
      c.coordinate W hW (schemePushforwardRestrictionRingEquiv f U W s) := by
  exact congrArg (fun e ↦ e s) (c.imageCoordinate_transport
    (U.ι ⁻¹ᵁ (U.ι ''ᵁ W)) W (U.ι.preimage_image_eq W)
    (schemeOpen_preimage_le_of_le_image U V (U.ι ''ᵁ W)
      (U.ι.image_le_image_of_le hW)) hW
    (schemeOpen_image_preimage_of_le U (U.ι ''ᵁ W) (U.ι_image_le W)))

end PushforwardKummerChart

end EvenQuinticConic
