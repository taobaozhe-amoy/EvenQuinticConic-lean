import EvenQuinticConic.FrameCocycleDescent

/-!
# Comparing actual sheaves with the same frame transitions

Actual coherent rank-one frames on a cover determine an isomorphism whenever
their transition coefficients agree. Local maps and their compatibility are
constructed from the frames; no desired sheaf isomorphism is an input.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

namespace EvenQuinticConic

universe u
variable {X : Scheme.{u}} {M N : X.Modules} {ι : Type u}

/-- A coherent frame restricts to any actual subopen, retaining its coordinates. -/
def ModuleSheafFrame.onSubopen {U V : X.Opens}
    (e : ModuleSheafFrame M U) (hVU : V ≤ U) : ModuleSheafFrame M V where
  coordinate W hW := e.coordinate W (hW.trans hVU)
  coordinate_restrict W Z hW hZ hZW s :=
    e.coordinate_restrict W Z (hW.trans hVU) (hZ.trans hVU) hZW s

@[simp]
theorem ModuleSheafFrame.onSubopen_coordinate {U V : X.Opens}
    (e : ModuleSheafFrame M U) (hVU : V ≤ U)
    (W : X.Opens) (hW : W ≤ V) (s : M.val.obj (op W)) :
    (e.onSubopen hVU).coordinate W hW s = e.coordinate W (hW.trans hVU) s := rfl

/-- A proved relation between the actual generators determines the exact
transition coefficient, including on empty overlaps. -/
theorem frameChangeCoefficient_eq_of_generator_eq {U V : X.Opens}
    (a : ModuleSheafFrame M U) (b : ModuleSheafFrame M V)
    (W : X.Opens) (hU : W ≤ U) (hV : W ≤ V) (c : Γ(X, W))
    (h : (b.coordinate W hV).symm 1 = c • (a.coordinate W hU).symm 1) :
    frameChangeCoefficient a b W hU hV = c := by
  unfold frameChangeCoefficient
  rw [h]
  change a.coordinate W hU
    ((show X.ringCatSheaf.val.obj (op W) from c) • (a.coordinate W hU).symm 1) = c
  rw [map_smul, LinearEquiv.apply_symm_apply]
  exact mul_one c

/-- The actual local linear equivalence preserving two specified frame coordinates. -/
def frameCoordinateComparison {U : X.Opens}
    (m : ModuleSheafFrame M U) (n : ModuleSheafFrame N U)
    (V : X.Opens) (hV : V ≤ U) :
    M.val.obj (op V) ≃ₗ[X.ringCatSheaf.val.obj (op V)] N.val.obj (op V) :=
  (m.coordinate V hV).trans (n.coordinate V hV).symm

@[simp]
theorem frameCoordinateComparison_coordinate {U : X.Opens}
    (m : ModuleSheafFrame M U) (n : ModuleSheafFrame N U)
    (V : X.Opens) (hV : V ≤ U) (s : M.val.obj (op V)) :
    n.coordinate V hV (frameCoordinateComparison m n V hV s) = m.coordinate V hV s :=
  (n.coordinate V hV).apply_symm_apply _

/-- Frame-coordinate comparisons commute with actual restriction maps. -/
def frameCoordinateLocalHom {U : X.Opens}
    (m : ModuleSheafFrame M U) (n : ModuleSheafFrame N U) : LocalModuleHom M N U where
  app V hV := (frameCoordinateComparison m n V hV).toLinearMap
  naturality V W hV hW hWV s := by
    apply (n.coordinate W hW).injective
    change n.coordinate W hW (frameCoordinateComparison m n W hW
      (moduleRestrict M hWV s)) = _
    rw [frameCoordinateComparison_coordinate, n.coordinate_restrict V W hV hW hWV]
    change m.coordinate W hW (moduleRestrict M hWV s) =
      X.ringCatSheaf.val.map (homOfLE hWV).op
        (n.coordinate V hV (frameCoordinateComparison m n V hV s))
    rw [frameCoordinateComparison_coordinate]
    exact m.coordinate_restrict V W hV hW hWV s

/-- Equality of the actual transition coefficients forces agreement of the
coordinate-preserving local maps on all common subopens. -/
theorem frameCoordinateLocalHom_agree
    (U : ι → X.Opens) (m : ∀ i, ModuleSheafFrame M (U i))
    (n : ∀ i, ModuleSheafFrame N (U i))
    (h : ∀ i j V (hi : V ≤ U i) (hj : V ≤ U j),
      frameChangeCoefficient (m i) (m j) V hi hj =
        frameChangeCoefficient (n i) (n j) V hi hj)
    (i j : ι) (V : X.Opens) (hi : V ≤ U i) (hj : V ≤ U j) :
    (frameCoordinateLocalHom (m i) (n i)).app V hi =
      (frameCoordinateLocalHom (m j) (n j)).app V hj := by
  ext s
  apply ((n i).coordinate V hi).injective
  change (n i).coordinate V hi (frameCoordinateComparison (m i) (n i) V hi s) =
    (n i).coordinate V hi (frameCoordinateComparison (m j) (n j) V hj s)
  rw [frameCoordinateComparison_coordinate,
    ← frameChangeCoefficient_mul_coordinate (n i) (n j) V hi hj,
    frameCoordinateComparison_coordinate, ← h i j V hi hj]
  exact (frameChangeCoefficient_mul_coordinate (m i) (m j) V hi hj s).symm

/-- Equal actual frame transitions produce an actual global module-sheaf isomorphism. -/
def frameTransitionComparisonIso
    (U : ι → X.Opens) (hcover : iSup U = ⊤)
    (m : ∀ i, ModuleSheafFrame M (U i)) (n : ∀ i, ModuleSheafFrame N (U i))
    (h : ∀ i j V (hi : V ≤ U i) (hj : V ≤ U j),
      frameChangeCoefficient (m i) (m j) V hi hj =
        frameChangeCoefficient (n i) (n j) V hi hj) : M ≅ N :=
  glueModuleIso U hcover (fun i ↦ frameCoordinateLocalHom (m i) (n i))
    (frameCoordinateLocalHom_agree U m n h)
    (fun i V hi ↦ (frameCoordinateComparison (m i) (n i) V hi).bijective)

/-- The glued isomorphism preserves the chosen coordinates on every frame subopen. -/
theorem frameTransitionComparisonIso_coordinate
    (U : ι → X.Opens) (hcover : iSup U = ⊤)
    (m : ∀ i, ModuleSheafFrame M (U i)) (n : ∀ i, ModuleSheafFrame N (U i))
    (h : ∀ i j V (hi : V ≤ U i) (hj : V ≤ U j),
      frameChangeCoefficient (m i) (m j) V hi hj =
        frameChangeCoefficient (n i) (n j) V hi hj)
    (i : ι) (V : X.Opens) (hi : V ≤ U i) (s : M.val.obj (op V)) :
    (n i).coordinate V hi ((frameTransitionComparisonIso U hcover m n h).hom.val.app
      (op V) s) = (m i).coordinate V hi s := by
  rw [frameTransitionComparisonIso, glueModuleIso_hom_app U hcover
    (fun i ↦ frameCoordinateLocalHom (m i) (n i))
    (frameCoordinateLocalHom_agree U m n h) _ i V hi]
  exact frameCoordinateComparison_coordinate (m i) (n i) V hi s

end EvenQuinticConic
