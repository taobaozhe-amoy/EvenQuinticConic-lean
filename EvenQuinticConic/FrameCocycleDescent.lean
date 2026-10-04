import EvenQuinticConic.LineBundleFrames
import EvenQuinticConic.ModuleHomGluing
import EvenQuinticConic.LocalTrivializationFrames

/-!
# Descent of an actual line sheaf from its coherent frames

Changes between actual rank-one frames are units. Their coefficients form
an actual cocycle, whose descended module sheaf is isomorphic to the original
sheaf when the framing opens cover. No isomorphism is included in the input.
-/

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace EvenQuinticConic

variable {X : Scheme.{u}} {M : X.Modules}

local instance frameDescentCommRing (V : X.Opens) : CommRing (X.ringCatSheaf.val.obj (op V)) :=
  inferInstanceAs (CommRing Γ(X, V))

/-- A frame generator restricts to the generator of the same frame. -/
theorem ModuleSheafFrame.restrict_generator {U : X.Opens}
    (f : ModuleSheafFrame M U) (V W : X.Opens)
    (hV : V ≤ U) (hW : W ≤ U) (hWV : W ≤ V) :
    moduleRestrict M hWV ((f.coordinate V hV).symm 1) =
      (f.coordinate W hW).symm 1 := by
  apply (f.coordinate W hW).injective
  rw [f.coordinate_restrict V W hV hW hWV]
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  exact map_one _

/-- The scalar change from frame `b` to frame `a` on a common subopen. -/
def frameChangeCoefficient {U V : X.Opens}
    (a : ModuleSheafFrame M U) (b : ModuleSheafFrame M V)
    (W : X.Opens) (hU : W ≤ U) (hV : W ≤ V) : Γ(X, W) :=
  a.coordinate W hU ((b.coordinate W hV).symm 1)

/-- Every section changes coordinates by the same scalar coefficient. -/
theorem frameChangeCoefficient_mul_coordinate {U V : X.Opens}
    (a : ModuleSheafFrame M U) (b : ModuleSheafFrame M V)
    (W : X.Opens) (hU : W ≤ U) (hV : W ≤ V)
    (s : M.val.obj (op W)) :
    frameChangeCoefficient a b W hU hV * (show Γ(X, W) from b.coordinate W hV s) =
      a.coordinate W hU s := by
  have hs : s = b.coordinate W hV s • (b.coordinate W hV).symm 1 := by
    apply (b.coordinate W hV).injective
    rw [map_smul, LinearEquiv.apply_symm_apply]
    exact (mul_one _).symm
  conv_rhs => rw [hs]
  simp only [map_smul, smul_eq_mul, frameChangeCoefficient]
  exact mul_comm _ _

/-- The scalar change has the opposite scalar change as its inverse. -/
theorem frameChangeCoefficient_mul_reverse {U V : X.Opens}
    (a : ModuleSheafFrame M U) (b : ModuleSheafFrame M V)
    (W : X.Opens) (hU : W ≤ U) (hV : W ≤ V) :
    frameChangeCoefficient a b W hU hV * frameChangeCoefficient b a W hV hU = 1 := by
  simpa only [frameChangeCoefficient, LinearEquiv.apply_symm_apply] using
    frameChangeCoefficient_mul_coordinate a b W hU hV ((a.coordinate W hU).symm 1)

/-- The actual unit relating two coherent frames. -/
def frameChangeUnit {U V : X.Opens}
    (a : ModuleSheafFrame M U) (b : ModuleSheafFrame M V)
    (W : X.Opens) (hU : W ≤ U) (hV : W ≤ V) : Γ(X, W)ˣ where
  val := frameChangeCoefficient a b W hU hV
  inv := frameChangeCoefficient b a W hV hU
  val_inv := frameChangeCoefficient_mul_reverse a b W hU hV
  inv_val := frameChangeCoefficient_mul_reverse b a W hV hU

@[simp] theorem frameChangeUnit_val {U V : X.Opens}
    (a : ModuleSheafFrame M U) (b : ModuleSheafFrame M V)
    (W : X.Opens) (hU : W ≤ U) (hV : W ≤ V) :
    (frameChangeUnit a b W hU hV : Γ(X, W)) = frameChangeCoefficient a b W hU hV := rfl

/-- Coordinate-change units commute with genuine restriction maps. -/
theorem frameChangeUnit_restrict {U V : X.Opens}
    (a : ModuleSheafFrame M U) (b : ModuleSheafFrame M V)
    (W Z : X.Opens) (hU : W ≤ U) (hV : W ≤ V) (hZW : Z ≤ W) :
    Units.map (X.presheaf.map (homOfLE hZW).op).hom (frameChangeUnit a b W hU hV) =
      frameChangeUnit a b Z (hZW.trans hU) (hZW.trans hV) := by
  apply Units.ext
  change X.ringCatSheaf.val.map (homOfLE hZW).op
    (a.coordinate W hU ((b.coordinate W hV).symm 1)) = _
  rw [← a.coordinate_restrict W Z hU (hZW.trans hU) hZW]
  change a.coordinate Z (hZW.trans hU)
    (moduleRestrict M hZW ((b.coordinate W hV).symm 1)) = _
  rw [b.restrict_generator W Z hV (hZW.trans hV) hZW]
  rfl

/-- The unit cocycle canonically extracted from actual coherent frames. -/
def frameUnitTransition {ι : Type u} (U : ι → X.Opens)
    (f : ∀ i, ModuleSheafFrame M (U i)) : UnitTransition X U where
  transition i j W hi hj := frameChangeUnit (f i) (f j) W hi hj
  restrict i j W V hi hj hVW := frameChangeUnit_restrict (f i) (f j) W V hi hj hVW
  self i W hi := by
    apply Units.ext
    change (f i).coordinate W hi (((f i).coordinate W hi).symm 1) = 1
    exact LinearEquiv.apply_symm_apply _ _
  cocycle i j k W hi hj hk := by
    apply Units.ext
    exact frameChangeCoefficient_mul_coordinate (f i) (f j) W hi hj
      (((f k).coordinate W hk).symm 1)

/-- A section in one frame corresponds to the same scalar in the descended frame. -/
noncomputable def frameDescentLocalEquiv {ι : Type u} (U : ι → X.Opens)
    (f : ∀ i, ModuleSheafFrame M (U i)) (i : ι)
    (V : X.Opens) (hi : V ≤ U i) :
    M.val.obj (op V) ≃ₗ[X.ringCatSheaf.val.obj (op V)]
      (frameUnitTransition U f).moduleSheaf.val.obj (op V) :=
  ((f i).coordinate V hi).trans
    (((frameUnitTransition U f).frame i).coordinate V hi).symm

@[simp] theorem frameDescentLocalEquiv_coordinate {ι : Type u} (U : ι → X.Opens)
    (f : ∀ i, ModuleSheafFrame M (U i)) (i : ι)
    (V : X.Opens) (hi : V ≤ U i) (s : M.val.obj (op V)) :
    ((frameUnitTransition U f).frame i).coordinate V hi
      (frameDescentLocalEquiv U f i V hi s) = (f i).coordinate V hi s := by
  exact LinearEquiv.apply_symm_apply _ _

/-- Frame descent gives natural local linear maps into the descended sheaf. -/
noncomputable def frameDescentLocalHom {ι : Type u} (U : ι → X.Opens)
    (f : ∀ i, ModuleSheafFrame M (U i)) (i : ι) :
    LocalModuleHom M (frameUnitTransition U f).moduleSheaf (U i) where
  app V hi := (frameDescentLocalEquiv U f i V hi).toLinearMap
  naturality V W hV hW hWV s := by
    apply (((frameUnitTransition U f).frame i).coordinate W hW).injective
    change ((frameUnitTransition U f).frame i).coordinate W hW
        (frameDescentLocalEquiv U f i W hW (moduleRestrict M hWV s)) = _
    rw [frameDescentLocalEquiv_coordinate,
      ((frameUnitTransition U f).frame i).coordinate_restrict V W hV hW hWV]
    change (f i).coordinate W hW (moduleRestrict M hWV s) =
      X.ringCatSheaf.val.map (homOfLE hWV).op
        (((frameUnitTransition U f).frame i).coordinate V hV
          (frameDescentLocalEquiv U f i V hV s))
    rw [frameDescentLocalEquiv_coordinate]
    exact (f i).coordinate_restrict V W hV hW hWV s

/-- The local descent maps agree because their coordinate changes are the
units extracted from the original frames. -/
theorem frameDescentLocalHom_compatible {ι : Type u} (U : ι → X.Opens)
    (f : ∀ i, ModuleSheafFrame M (U i))
    (i j : ι) (V : X.Opens) (hi : V ≤ U i) (hj : V ≤ U j) :
    (frameDescentLocalHom U f i).app V hi = (frameDescentLocalHom U f j).app V hj := by
  ext s
  apply (((frameUnitTransition U f).frame i).coordinate V hi).injective
  change ((frameUnitTransition U f).frame i).coordinate V hi
      (frameDescentLocalEquiv U f i V hi s) =
    ((frameUnitTransition U f).frame i).coordinate V hi
      (frameDescentLocalEquiv U f j V hj s)
  rw [frameDescentLocalEquiv_coordinate]
  calc
    _ = frameChangeCoefficient (f i) (f j) V hi hj *
        (show Γ(X, V) from (f j).coordinate V hj s) :=
      (frameChangeCoefficient_mul_coordinate (f i) (f j) V hi hj s).symm
    _ = (frameUnitTransition U f).transition i j V hi hj *
        (show Γ(X, V) from ((frameUnitTransition U f).frame j).coordinate V hj
          (frameDescentLocalEquiv U f j V hj s)) := by
      rw [frameDescentLocalEquiv_coordinate]
      rfl
    _ = _ := ((frameUnitTransition U f).frame_transition i j V hi hj _).symm

/-- An actual sheaf with coherent rank-one frames on a cover is isomorphic
to the sheaf descended from their unit cocycle. -/
noncomputable def frameDescentIso {ι : Type u} (U : ι → X.Opens)
    (hcover : iSup U = ⊤) (f : ∀ i, ModuleSheafFrame M (U i)) :
    M ≅ (frameUnitTransition U f).moduleSheaf :=
  glueModuleIso U hcover (frameDescentLocalHom U f)
    (frameDescentLocalHom_compatible U f)
    (fun i V hi ↦ (frameDescentLocalEquiv U f i V hi).bijective)

/-- The descent isomorphism preserves the prescribed coordinates on every
subopen of a framing chart. -/
theorem frameDescentIso_coordinate {ι : Type u} (U : ι → X.Opens)
    (hcover : iSup U = ⊤) (f : ∀ i, ModuleSheafFrame M (U i))
    (i : ι) (V : X.Opens) (hi : V ≤ U i) (s : M.val.obj (op V)) :
    ((frameUnitTransition U f).frame i).coordinate V hi
      ((frameDescentIso U hcover f).hom.val.app (op V) s) =
      (f i).coordinate V hi s := by
  rw [frameDescentIso, glueModuleIso_hom_app U hcover (frameDescentLocalHom U f)
    (frameDescentLocalHom_compatible U f) _ i V hi]
  exact frameDescentLocalEquiv_coordinate U f i V hi s

/-- The unit cocycle extracted directly from actual local trivializations. -/
noncomputable def localTrivializationTransition {ι : Type u} (U : ι → X.Opens)
    (e : ∀ i, M.over (U i) ≅ SheafOfModules.unit (X.ringCatSheaf.over (U i))) :
    UnitTransition X U :=
  frameUnitTransition U (fun i ↦ moduleSheafFrameOfLocalIso (e i))

/-- Actual local trivializations on a covering family reconstruct the
original sheaf by descent. -/
noncomputable def localTrivializationDescentIso {ι : Type u} (U : ι → X.Opens)
    (hcover : iSup U = ⊤)
    (e : ∀ i, M.over (U i) ≅ SheafOfModules.unit (X.ringCatSheaf.over (U i))) :
    M ≅ (localTrivializationTransition U e).moduleSheaf :=
  frameDescentIso U hcover (fun i ↦ moduleSheafFrameOfLocalIso (e i))

/-- The descended isomorphism recovers the coordinates of each given actual
local trivialization. -/
theorem localTrivializationDescentIso_coordinate {ι : Type u} (U : ι → X.Opens)
    (hcover : iSup U = ⊤)
    (e : ∀ i, M.over (U i) ≅ SheafOfModules.unit (X.ringCatSheaf.over (U i)))
    (i : ι) (V : X.Opens) (hi : V ≤ U i) (s : M.val.obj (op V)) :
    ((localTrivializationTransition U e).frame i).coordinate V hi
      ((localTrivializationDescentIso U hcover e).hom.val.app (op V) s) =
      (e i).hom.val.app (op (Over.mk (homOfLE hi))) s :=
  frameDescentIso_coordinate U hcover (fun i ↦ moduleSheafFrameOfLocalIso (e i)) i V hi s

end EvenQuinticConic
