import EvenQuinticConic.KummerModuleAtlas

/-! # Genuine rank-one frames on the kernel of the constructed global trace -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
universe u
namespace EvenQuinticConic.KummerModuleAtlas
variable {X : Scheme.{u}} {M : X.Modules} {ι : Type u} {U : ι → X.Opens}
    (a : KummerModuleAtlas M U) (hcover : iSup U = ⊤)

local instance sectionCommRing (V : X.Opens) : CommRing (X.ringCatSheaf.val.obj (op V)) :=
  inferInstanceAs (CommRing Γ(X, V))

/-- A local quadratic chart identifies the actual sectionwise trace kernels. -/
def traceKernelChartEquiv (i : ι) (V : X.Opens) (hi : V ≤ U i) :
    LinearMap.ker ((a.trace hcover).val.app (op V)).hom ≃ₗ[Γ(X, V)]
      KummerTraceZero (X.presheaf.map (homOfLE hi).op (a.parameter i : Γ(X, U i))) where
  toFun s := ⟨(a.chart i).coordinate V hi s.val, by
    change Algebra.trace Γ(X, V) _ ((a.chart i).coordinate V hi s.val) = 0
    rw [← a.trace_apply hcover i V hi]
    exact s.property⟩
  invFun s := ⟨((a.chart i).coordinate V hi).symm s.val, by
    change (a.trace hcover).val.app (op V) (((a.chart i).coordinate V hi).symm s.val) = 0
    rw [a.trace_apply hcover i V hi, LinearEquiv.apply_symm_apply]
    exact s.property⟩
  left_inv s := by apply Subtype.ext; exact LinearEquiv.symm_apply_apply _ _
  right_inv s := by apply Subtype.ext; exact LinearEquiv.apply_symm_apply _ _
  map_add' s t := by apply Subtype.ext; exact map_add _ _ _
  map_smul' r s := by apply Subtype.ext; exact map_smul _ _ _

/-- Actual sections of the categorical kernel are identified with the local algebra kernel. -/
def traceZeroChartEquiv (i : ι) (V : X.Opens) (hi : V ≤ U i) :
    (a.traceZeroSheaf hcover).val.obj (op V) ≃ₗ[Γ(X, V)]
      KummerTraceZero (X.presheaf.map (homOfLE hi).op (a.parameter i : Γ(X, U i))) where
  toFun s := a.traceKernelChartEquiv hcover i V hi (moduleSheafKernelSectionEquiv (a.trace hcover) V s)
  invFun s := (moduleSheafKernelSectionEquiv (a.trace hcover) V).symm
    ((a.traceKernelChartEquiv hcover i V hi).symm s)
  left_inv s :=
    (congrArg (moduleSheafKernelSectionEquiv (a.trace hcover) V).symm
      ((a.traceKernelChartEquiv hcover i V hi).symm_apply_apply
        (moduleSheafKernelSectionEquiv (a.trace hcover) V s))).trans
      ((moduleSheafKernelSectionEquiv (a.trace hcover) V).symm_apply_apply s)
  right_inv s :=
    (congrArg (a.traceKernelChartEquiv hcover i V hi)
      ((moduleSheafKernelSectionEquiv (a.trace hcover) V).apply_symm_apply
        ((a.traceKernelChartEquiv hcover i V hi).symm s))).trans
      ((a.traceKernelChartEquiv hcover i V hi).apply_symm_apply s)
  map_add' s t := by simp
  map_smul' r s := by simp

/-- This local identification uses the original kernel inclusion in M. -/
theorem traceZeroChartEquiv_val (i : ι) (V : X.Opens) (hi : V ≤ U i)
    (s : (a.traceZeroSheaf hcover).val.obj (op V)) :
    (a.traceZeroChartEquiv hcover i V hi s).val =
      (a.chart i).coordinate V hi ((kernel.ι (a.trace hcover)).val.app (op V) s) := by
  change (a.chart i).coordinate V hi (moduleSheafKernelSectionEquiv (a.trace hcover) V s).val = _
  rw [moduleSheafKernelSectionEquiv_val]

variable [∀ V : X.Opens, Invertible (2 : Γ(X, V))]

/-- Coherent rank-one frames are constructed on the actual global trace kernel. -/
def traceZeroFrame (i : ι) : ModuleSheafFrame (a.traceZeroSheaf hcover) (U i) where
  coordinate V hi := by
    let e := a.traceZeroChartEquiv hcover i V hi
    let f : KummerTraceZero (X.presheaf.map (homOfLE hi).op (a.parameter i : Γ(X, U i)))
        ≃ₗ[Γ(X, V)] Γ(X, V) := kummerTraceZeroCoordinate _
    exact
      { toFun := fun s ↦ f (e s)
        invFun := fun r ↦ e.symm (f.symm r)
        left_inv := fun s ↦ (congrArg e.symm (f.symm_apply_apply (e s))).trans (e.symm_apply_apply s)
        right_inv := fun r ↦ (congrArg f (e.apply_symm_apply (f.symm r))).trans (f.apply_symm_apply r)
        map_add' := fun s t ↦ by simp
        map_smul' := fun r s ↦ by simp }
  coordinate_restrict V W hi hj hWV s := by
    change (a.traceZeroChartEquiv hcover i W hj (moduleRestrict _ hWV s)).val.im =
      X.presheaf.map (homOfLE hWV).op (a.traceZeroChartEquiv hcover i V hi s).val.im
    rw [a.traceZeroChartEquiv_val, a.traceZeroChartEquiv_val]
    dsimp only [traceZeroSheaf, moduleRestrict]
    rw [PresheafOfModules.naturality_apply (kernel.ι (a.trace hcover)).val (homOfLE hWV).op s]
    exact (a.chart i).im_restrict V W hi hj hWV _

/-- The frame coordinate is the imaginary coefficient of the actual included section. -/
theorem traceZeroFrame_coordinate (i : ι) (V : X.Opens) (hi : V ≤ U i)
    (s : (a.traceZeroSheaf hcover).val.obj (op V)) :
    (a.traceZeroFrame hcover i).coordinate V hi s =
      ((a.chart i).coordinate V hi ((kernel.ι (a.trace hcover)).val.app (op V) s)).im := by
  change (a.traceZeroChartEquiv hcover i V hi s).val.im = _
  rw [a.traceZeroChartEquiv_val]

/-- The genuine frame generator maps to t in its actual quadratic chart. -/
theorem traceZeroFrame_generator (i : ι) (V : X.Opens) (hi : V ≤ U i) :
    (a.chart i).coordinate V hi ((kernel.ι (a.trace hcover)).val.app (op V)
      (((a.traceZeroFrame hcover i).coordinate V hi).symm 1)) = kummerGenerator _ := by
  rw [← a.traceZeroChartEquiv_val]
  change ((a.traceZeroChartEquiv hcover i V hi)
    ((a.traceZeroChartEquiv hcover i V hi).symm ((kummerTraceZeroCoordinate _).symm 1))).val = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

end EvenQuinticConic.KummerModuleAtlas
