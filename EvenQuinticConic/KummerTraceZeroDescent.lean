import EvenQuinticConic.KummerTraceZeroFrames
import EvenQuinticConic.PlaneThetaKummer

/-!
# Descent of the actual global trace kernel

The line cocycle, its identification with the kernel, and its square
trivialization are all constructed from the actual quadratic atlas.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
universe u
namespace EvenQuinticConic.KummerModuleAtlas
variable {X : Scheme.{u}} {M : X.Modules} {ι : Type u} {U : ι → X.Opens}
    (a : KummerModuleAtlas M U) (hcover : iSup U = ⊤)
    [∀ V : X.Opens, Invertible (2 : Γ(X, V))]

/-- The unit line cocycle extracted from genuine frames of the global trace kernel. -/
def traceZeroTransition : UnitTransition X U :=
  frameUnitTransition U (a.traceZeroFrame hcover)

/-- The actual trace kernel is isomorphic to the sheaf descended from its extracted cocycle. -/
def traceZeroDescentIso : a.traceZeroSheaf hcover ≅ (a.traceZeroTransition hcover).moduleSheaf :=
  frameDescentIso U hcover (a.traceZeroFrame hcover)

/-- Its units equal those derived from the actual overlap algebra isomorphisms. -/
theorem traceZeroTransition_eq (i j : ι) (V : X.Opens) (hi : V ≤ U i) (hj : V ≤ U j) :
    (a.traceZeroTransition hcover).transition i j V hi hj =
      kummerChangeUnit (a.overlap i j V hi hj) := by
  apply Units.ext
  change (a.traceZeroFrame hcover i).coordinate V hi
    (((a.traceZeroFrame hcover j).coordinate V hj).symm 1) = _
  rw [a.traceZeroFrame_coordinate]
  rw [← a.overlap_coordinate i j V hi hj, a.traceZeroFrame_generator]
  rfl

/-- The overlap maps use the internally extracted line coordinates. -/
theorem traceZeroOverlapCoordinates :
    (a.traceZeroTransition hcover).KummerOverlapCoordinates a.parameter
      (fun i j V hi hj ↦ (a.overlap i j V hi hj).toAlgHom) := by
  intro i j V hi hj
  change a.overlap i j V hi hj (kummerGenerator _) =
    ((a.traceZeroTransition hcover).transition i j V hi hj : Γ(X, V)) • kummerGenerator _
  rw [a.traceZeroTransition_eq]
  exact kummer_map_generator (a.overlap i j V hi hj)

/-- Actual local algebra multiplication constructs the square of the extracted line. -/
def traceZeroSquareIso :
    ((a.traceZeroTransition hcover).mul (a.traceZeroTransition hcover)).moduleSheaf ≅
      SheafOfModules.unit X.ringCatSheaf :=
  (a.traceZeroTransition hcover).squareIsoOfKummerMaps hcover a.parameter
    (fun i j V hi hj ↦ (a.overlap i j V hi hj).toAlgHom)
    (a.traceZeroOverlapCoordinates hcover)

/-- Multiplication pairing on the actual kernel, transported through the proved descent iso. -/
def traceZeroSquarePairing :
    ModuleSheafPairing (a.traceZeroSheaf hcover) (a.traceZeroSheaf hcover)
      (SheafOfModules.unit X.ringCatSheaf) :=
  ((a.traceZeroTransition hcover).squarePairingOfIso (a.traceZeroSquareIso hcover)).precomposeIso
    (a.traceZeroDescentIso hcover) (a.traceZeroDescentIso hcover)

/-- The actual kernel-square pairing is locally tensor-perfect. -/
theorem traceZeroSquarePairing_tensor_bijective (i : ι) (V : X.Opens) (hi : V ≤ U i) :
    Function.Bijective (TensorProduct.lift ((a.traceZeroSquarePairing hcover).app V)) := by
  apply ModuleSheafPairing.precomposeIso_tensor_bijective
  exact (a.traceZeroTransition hcover).squarePairingOfIso_tensor_bijective
    (a.traceZeroSquareIso hcover) i V hi

/-- The descended pairing has the original local multiplication coefficient. -/
theorem traceZeroSquarePairing_coordinate (i : ι) (V : X.Opens) (hi : V ≤ U i)
    (s t : (a.traceZeroSheaf hcover).val.obj (op V)) :
    (a.traceZeroSquarePairing hcover).app V s t =
      X.presheaf.map (homOfLE hi).op (a.parameter i : Γ(X, U i)) *
        ((show Γ(X, V) from (a.traceZeroFrame hcover i).coordinate V hi s) *
          (show Γ(X, V) from (a.traceZeroFrame hcover i).coordinate V hi t)) := by
  change ((a.traceZeroTransition hcover).squareIsoOfLocalUnits hcover a.parameter
    ((a.traceZeroTransition hcover).squareCoefficientsCompatible_of_kummerMaps a.parameter
      (fun i j V hi hj ↦ (a.overlap i j V hi hj).toAlgHom)
      (a.traceZeroOverlapCoordinates hcover))).hom.val.app
    (op V) (((a.traceZeroDescentIso hcover).hom.val.app (op V) s).mul
      ((a.traceZeroDescentIso hcover).hom.val.app (op V) t)) = _
  rw [UnitTransition.squareIsoOfLocalUnits_apply _ _ _ _ i V hi]
  change _ * (((a.traceZeroTransition hcover).frame i).coordinate V hi
      ((a.traceZeroDescentIso hcover).hom.val.app (op V) s) *
    ((a.traceZeroTransition hcover).frame i).coordinate V hi
      ((a.traceZeroDescentIso hcover).hom.val.app (op V) t)) = _
  dsimp only [traceZeroTransition, traceZeroDescentIso]
  rw [frameDescentIso_coordinate, frameDescentIso_coordinate]

/-- The actual kernel-square pairing agrees with algebra multiplication in every chart. -/
theorem traceZeroSquarePairing_algebra_mul (i : ι) (V : X.Opens) (hi : V ≤ U i)
    (s t : (a.traceZeroSheaf hcover).val.obj (op V)) :
    (a.chart i).coordinate V hi ((kernel.ι (a.trace hcover)).val.app (op V) s) *
      (a.chart i).coordinate V hi ((kernel.ι (a.trace hcover)).val.app (op V) t) =
    algebraMap Γ(X, V) (KummerAlgebra (X.presheaf.map (homOfLE hi).op (a.parameter i : Γ(X, U i))))
      ((a.traceZeroSquarePairing hcover).app V s t) := by
  have h := kummer_traceZero_mul _ (a.traceZeroChartEquiv hcover i V hi s)
    (a.traceZeroChartEquiv hcover i V hi t)
  change _ * _ = algebraMap Γ(X, V) _
    (_ * ((a.traceZeroChartEquiv hcover i V hi s).val.im *
      (a.traceZeroChartEquiv hcover i V hi t).val.im)) at h
  rw [a.traceZeroChartEquiv_val, a.traceZeroChartEquiv_val] at h
  rw [a.traceZeroSquarePairing_coordinate, a.traceZeroFrame_coordinate, a.traceZeroFrame_coordinate]
  exact h

end EvenQuinticConic.KummerModuleAtlas
