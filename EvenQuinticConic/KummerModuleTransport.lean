import EvenQuinticConic.KummerModuleAtlas
import EvenQuinticConic.SchemeOpenModuleFrames

/-!
# Transport of actual Kummer coordinates

Module-sheaf isomorphisms transport coherent Kummer coordinates on the same
scheme. Coordinates on an actual open subscheme also descend to its image
open in the original scheme, using the actual image-preimage equality.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace EvenQuinticConic

variable {X : Scheme.{u}}

/-- Evaluation of an actual module-sheaf isomorphism at an open. -/
def moduleSheafIsoCoordinate {M N : X.Modules} (e : M ≅ N) (V : X.Opens) :
    M.val.obj (op V) ≃ₗ[Γ(X, V)] N.val.obj (op V) :=
  ((SheafOfModules.evaluation X.ringCatSheaf (op V)).mapIso e).toLinearEquiv

theorem moduleSheafIsoCoordinate_restrict {M N : X.Modules} (e : M ≅ N)
    (V W : X.Opens) (hWV : W ≤ V) (s : M.val.obj (op V)) :
    moduleSheafIsoCoordinate e W (moduleRestrict M hWV s) =
      moduleRestrict N hWV (moduleSheafIsoCoordinate e V s) :=
  PresheafOfModules.naturality_apply e.hom.val (homOfLE hWV).op s

namespace KummerModuleChart

variable {M N : X.Modules} {U : X.Opens} {u : Γ(X, U)ˣ}

/-- Transport a coherent Kummer chart along an actual module-sheaf isomorphism. -/
def transport (c : KummerModuleChart M U u) (e : M ≅ N) :
    KummerModuleChart N U u where
  coordinate V hV := (moduleSheafIsoCoordinate e.symm V).trans (c.coordinate V hV)
  re_restrict V W hV hW hWV s := by
    change (c.coordinate W hW (moduleSheafIsoCoordinate e.symm W
      (moduleRestrict N hWV s))).re = _
    rw [moduleSheafIsoCoordinate_restrict]
    exact c.re_restrict V W hV hW hWV _
  im_restrict V W hV hW hWV s := by
    change (c.coordinate W hW (moduleSheafIsoCoordinate e.symm W
      (moduleRestrict N hWV s))).im = _
    rw [moduleSheafIsoCoordinate_restrict]
    exact c.im_restrict V W hV hW hWV _

@[simp]
theorem transport_coordinate (c : KummerModuleChart M U u) (e : M ≅ N)
    (V : X.Opens) (hV : V ≤ U) (s : N.val.obj (op V)) :
    (c.transport e).coordinate V hV s =
      c.coordinate V hV (e.inv.val.app (op V) s) := rfl

end KummerModuleChart

namespace KummerModuleAtlas

variable {M N : X.Modules} {ι : Type u} {U : ι → X.Opens}

/-- All actual overlap algebra isomorphisms survive module-sheaf transport. -/
def transport (a : KummerModuleAtlas M U) (e : M ≅ N) :
    KummerModuleAtlas N U where
  parameter := a.parameter
  chart i := (a.chart i).transport e
  overlap := a.overlap
  overlap_coordinate i j V hi hj s := a.overlap_coordinate i j V hi hj
    (e.inv.val.app (op V) s)

end KummerModuleAtlas

/-- Inverse image of an original open contained in an image open. -/
theorem schemeOpen_preimage_le_of_le_image (U : X.Opens) (V : U.toScheme.Opens)
    (W : X.Opens) (hW : W ≤ U.ι ''ᵁ V) : U.ι ⁻¹ᵁ W ≤ V := by
  rw [← U.ι.preimage_image_eq V]
  exact fun _ hx ↦ hW hx

/-- A cover of the actual open subscheme gives an image-open cover of `U`. -/
theorem schemeOpen_image_cover (U : X.Opens) {ι : Type u} (V : ι → U.toScheme.Opens)
    (hcover : iSup V = ⊤) : (⨆ i, U.ι ''ᵁ V i) = U := by
  rw [← U.ι.image_iSup, hcover, U.ι_image_top]

/-- Local covers of the members of an original cover combine to a cover of
the original scheme by their actual image opens. -/
theorem schemeOpen_image_refinement_cover {ι : Type u} (U : ι → X.Opens)
    (hU : iSup U = ⊤) {κ : ι → Type u}
    (V : ∀ i, κ i → (U i).toScheme.Opens) (hV : ∀ i, iSup (V i) = ⊤) :
    (⨆ p : Σ i, κ i, (U p.1).ι ''ᵁ V p.1 p.2) = ⊤ := by
  rw [iSup_sigma]
  simp_rw [schemeOpen_image_cover _ _ (hV _)]
  exact hU

/-- Equality of opens transports actual quadratic coordinates, with their
structure-ring action and restricted parameter. -/
def kummerCoordinateTransport (M : X.Modules) {U V V' : X.Opens}
    (u : Γ(X, U)ˣ) (h : V' = V) (hV : V ≤ U) (hV' : V' ≤ U)
    (e : M.val.obj (op V') ≃ₗ[Γ(X, V')]
      KummerAlgebra (X.presheaf.map (homOfLE hV').op (u : Γ(X, U)))) :
    M.val.obj (op V) ≃ₗ[Γ(X, V)]
      KummerAlgebra (X.presheaf.map (homOfLE hV).op (u : Γ(X, U))) := by
  subst V'
  exact e

/-- The two restriction identities survive equality transport of their opens. -/
theorem kummerCoordinateTransport_restrict (M : X.Modules) {U V W V' W' : X.Opens}
    (u : Γ(X, U)ˣ) (hV : V' = V) (hW : W' = W)
    (hVU : V ≤ U) (hWU : W ≤ U) (hV'U : V' ≤ U) (hW'U : W' ≤ U)
    (hWV : W ≤ V) (hW'V' : W' ≤ V')
    (eV : M.val.obj (op V') ≃ₗ[Γ(X, V')]
      KummerAlgebra (X.presheaf.map (homOfLE hV'U).op (u : Γ(X, U))))
    (eW : M.val.obj (op W') ≃ₗ[Γ(X, W')]
      KummerAlgebra (X.presheaf.map (homOfLE hW'U).op (u : Γ(X, U))))
    (he : ∀ s, (eW (moduleRestrict M hW'V' s)).re =
        X.presheaf.map (homOfLE hW'V').op (eV s).re ∧
      (eW (moduleRestrict M hW'V' s)).im =
        X.presheaf.map (homOfLE hW'V').op (eV s).im)
    (s : M.val.obj (op V)) :
    ((kummerCoordinateTransport M u hW hWU hW'U eW)
        (moduleRestrict M hWV s)).re =
        X.presheaf.map (homOfLE hWV).op
          ((kummerCoordinateTransport M u hV hVU hV'U eV) s).re ∧
    ((kummerCoordinateTransport M u hW hWU hW'U eW)
        (moduleRestrict M hWV s)).im =
        X.presheaf.map (homOfLE hWV).op
          ((kummerCoordinateTransport M u hV hVU hV'U eV) s).im := by
  subst V'
  subst W'
  exact he s

namespace KummerModuleChart

variable {M : X.Modules} {U : X.Opens} {V : U.toScheme.Opens}
  {u : Γ(U.toScheme, V)ˣ}

/-- Descend a coherent chart from an actual open subscheme to its image open
in the original scheme. Every coordinate is on the original module sheaf. -/
def openImage (c : KummerModuleChart ((schemeModuleRestrict U).obj M) V u) :
    KummerModuleChart M (U.ι ''ᵁ V) u where
  coordinate W hW := kummerCoordinateTransport M u
    (schemeOpen_image_preimage_of_le U W (hW.trans (U.ι_image_le V))) hW
    (U.ι.image_le_image_of_le (schemeOpen_preimage_le_of_le_image U V W hW))
    (c.coordinate (U.ι ⁻¹ᵁ W) (schemeOpen_preimage_le_of_le_image U V W hW))
  re_restrict W Z hW hZ hZW s := by
    apply (kummerCoordinateTransport_restrict M u
      (schemeOpen_image_preimage_of_le U W (hW.trans (U.ι_image_le V)))
      (schemeOpen_image_preimage_of_le U Z (hZ.trans (U.ι_image_le V)))
      hW hZ
      (U.ι.image_le_image_of_le (schemeOpen_preimage_le_of_le_image U V W hW))
      (U.ι.image_le_image_of_le (schemeOpen_preimage_le_of_le_image U V Z hZ))
      hZW (U.ι.image_le_image_of_le (show U.ι ⁻¹ᵁ Z ≤ U.ι ⁻¹ᵁ W from fun _ hx ↦ hZW hx))
      (c.coordinate (U.ι ⁻¹ᵁ W) (schemeOpen_preimage_le_of_le_image U V W hW))
      (c.coordinate (U.ι ⁻¹ᵁ Z) (schemeOpen_preimage_le_of_le_image U V Z hZ))
      (fun t ↦ ⟨c.re_restrict (U.ι ⁻¹ᵁ W) (U.ι ⁻¹ᵁ Z)
        (schemeOpen_preimage_le_of_le_image U V W hW)
        (schemeOpen_preimage_le_of_le_image U V Z hZ)
        (show U.ι ⁻¹ᵁ Z ≤ U.ι ⁻¹ᵁ W from fun _ hx ↦ hZW hx) t,
        c.im_restrict (U.ι ⁻¹ᵁ W) (U.ι ⁻¹ᵁ Z)
        (schemeOpen_preimage_le_of_le_image U V W hW)
        (schemeOpen_preimage_le_of_le_image U V Z hZ)
        (show U.ι ⁻¹ᵁ Z ≤ U.ι ⁻¹ᵁ W from fun _ hx ↦ hZW hx) t⟩) s).1
  im_restrict W Z hW hZ hZW s := by
    apply (kummerCoordinateTransport_restrict M u
      (schemeOpen_image_preimage_of_le U W (hW.trans (U.ι_image_le V)))
      (schemeOpen_image_preimage_of_le U Z (hZ.trans (U.ι_image_le V)))
      hW hZ
      (U.ι.image_le_image_of_le (schemeOpen_preimage_le_of_le_image U V W hW))
      (U.ι.image_le_image_of_le (schemeOpen_preimage_le_of_le_image U V Z hZ))
      hZW (U.ι.image_le_image_of_le (show U.ι ⁻¹ᵁ Z ≤ U.ι ⁻¹ᵁ W from fun _ hx ↦ hZW hx))
      (c.coordinate (U.ι ⁻¹ᵁ W) (schemeOpen_preimage_le_of_le_image U V W hW))
      (c.coordinate (U.ι ⁻¹ᵁ Z) (schemeOpen_preimage_le_of_le_image U V Z hZ))
      (fun t ↦ ⟨c.re_restrict (U.ι ⁻¹ᵁ W) (U.ι ⁻¹ᵁ Z)
        (schemeOpen_preimage_le_of_le_image U V W hW)
        (schemeOpen_preimage_le_of_le_image U V Z hZ)
        (show U.ι ⁻¹ᵁ Z ≤ U.ι ⁻¹ᵁ W from fun _ hx ↦ hZW hx) t,
        c.im_restrict (U.ι ⁻¹ᵁ W) (U.ι ⁻¹ᵁ Z)
        (schemeOpen_preimage_le_of_le_image U V W hW)
        (schemeOpen_preimage_le_of_le_image U V Z hZ)
        (show U.ι ⁻¹ᵁ Z ≤ U.ι ⁻¹ᵁ W from fun _ hx ↦ hZW hx) t⟩) s).2

end KummerModuleChart

/-- An overlap algebra isomorphism transports along an equality of opens. -/
def kummerOverlapTransport {U₁ U₂ V V' : X.Opens}
    (u₁ : Γ(X, U₁)ˣ) (u₂ : Γ(X, U₂)ˣ) (h : V' = V)
    (h₁ : V ≤ U₁) (h₂ : V ≤ U₂) (h₁' : V' ≤ U₁) (h₂' : V' ≤ U₂)
    (e : KummerAlgebra (X.presheaf.map (homOfLE h₂').op (u₂ : Γ(X, U₂))) ≃ₐ[Γ(X, V')]
      KummerAlgebra (X.presheaf.map (homOfLE h₁').op (u₁ : Γ(X, U₁)))) :
    KummerAlgebra (X.presheaf.map (homOfLE h₂).op (u₂ : Γ(X, U₂))) ≃ₐ[Γ(X, V)]
      KummerAlgebra (X.presheaf.map (homOfLE h₁).op (u₁ : Γ(X, U₁))) := by
  subst V'
  exact e

/-- Coordinate compatibility survives the same equality transport. -/
theorem kummerOverlapTransport_coordinate (M : X.Modules) {U₁ U₂ V V' : X.Opens}
    (u₁ : Γ(X, U₁)ˣ) (u₂ : Γ(X, U₂)ˣ) (h : V' = V)
    (h₁ : V ≤ U₁) (h₂ : V ≤ U₂) (h₁' : V' ≤ U₁) (h₂' : V' ≤ U₂)
    (e : KummerAlgebra (X.presheaf.map (homOfLE h₂').op (u₂ : Γ(X, U₂))) ≃ₐ[Γ(X, V')]
      KummerAlgebra (X.presheaf.map (homOfLE h₁').op (u₁ : Γ(X, U₁))))
    (c₁ : M.val.obj (op V') ≃ₗ[Γ(X, V')]
      KummerAlgebra (X.presheaf.map (homOfLE h₁').op (u₁ : Γ(X, U₁))))
    (c₂ : M.val.obj (op V') ≃ₗ[Γ(X, V')]
      KummerAlgebra (X.presheaf.map (homOfLE h₂').op (u₂ : Γ(X, U₂))))
    (hc : ∀ s, e (c₂ s) = c₁ s) (s : M.val.obj (op V)) :
    kummerOverlapTransport u₁ u₂ h h₁ h₂ h₁' h₂' e
      ((kummerCoordinateTransport M u₂ h h₂ h₂' c₂) s) =
      (kummerCoordinateTransport M u₁ h h₁ h₁' c₁) s := by
  subst V'
  exact hc s

namespace KummerModuleAtlas

variable {M : X.Modules} {U : X.Opens} {ι : Type u} {V : ι → U.toScheme.Opens}

/-- An actual open-subscheme atlas supplies an atlas on the corresponding
image opens of the original scheme, with its original overlap algebra maps. -/
def openImage (a : KummerModuleAtlas ((schemeModuleRestrict U).obj M) V) :
    KummerModuleAtlas M (fun i ↦ U.ι ''ᵁ V i) where
  parameter := a.parameter
  chart i := (a.chart i).openImage
  overlap i j W hi hj := kummerOverlapTransport (X := X) (a.parameter i) (a.parameter j)
    (schemeOpen_image_preimage_of_le U W (hi.trans (U.ι_image_le (V i)))) hi hj
    (U.ι.image_le_image_of_le (schemeOpen_preimage_le_of_le_image U (V i) W hi))
    (U.ι.image_le_image_of_le (schemeOpen_preimage_le_of_le_image U (V j) W hj))
    (a.overlap i j (U.ι ⁻¹ᵁ W)
      (schemeOpen_preimage_le_of_le_image U (V i) W hi)
      (schemeOpen_preimage_le_of_le_image U (V j) W hj))
  overlap_coordinate i j W hi hj s := by
    exact kummerOverlapTransport_coordinate M (a.parameter i) (a.parameter j)
      (schemeOpen_image_preimage_of_le U W (hi.trans (U.ι_image_le (V i)))) hi hj
      (U.ι.image_le_image_of_le (schemeOpen_preimage_le_of_le_image U (V i) W hi))
      (U.ι.image_le_image_of_le (schemeOpen_preimage_le_of_le_image U (V j) W hj))
      (a.overlap i j (U.ι ⁻¹ᵁ W)
        (schemeOpen_preimage_le_of_le_image U (V i) W hi)
        (schemeOpen_preimage_le_of_le_image U (V j) W hj))
      ((a.chart i).coordinate (U.ι ⁻¹ᵁ W)
        (schemeOpen_preimage_le_of_le_image U (V i) W hi))
      ((a.chart j).coordinate (U.ι ⁻¹ᵁ W)
        (schemeOpen_preimage_le_of_le_image U (V j) W hj))
      (a.overlap_coordinate i j (U.ι ⁻¹ᵁ W)
        (schemeOpen_preimage_le_of_le_image U (V i) W hi)
        (schemeOpen_preimage_le_of_le_image U (V j) W hj)) s

end KummerModuleAtlas

end EvenQuinticConic
