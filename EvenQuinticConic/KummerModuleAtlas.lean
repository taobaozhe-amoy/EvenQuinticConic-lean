import EvenQuinticConic.ModuleSheafKernelSections
import EvenQuinticConic.QuadraticTraceZeroTransition

/-!
# Local quadratic-algebra coordinates on an actual module sheaf

An atlas here supplies actual linear coordinates, actual restriction laws,
and actual algebra isomorphisms on overlaps. The global trace morphism is
constructed by gluing the algebra traces; it is not an input.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
universe u
namespace EvenQuinticConic
variable {X : Scheme.{u}}

/-- Coherent quadratic coordinates on an actual module sheaf over one open. -/
structure KummerModuleChart (M : X.Modules) (U : X.Opens) (u : Γ(X, U)ˣ) where
  coordinate : ∀ V (hV : V ≤ U), M.val.obj (op V) ≃ₗ[Γ(X, V)]
    KummerAlgebra (X.presheaf.map (homOfLE hV).op (u : Γ(X, U)))
  re_restrict : ∀ V W (hV : V ≤ U) (hW : W ≤ U) (hWV : W ≤ V)
    (s : M.val.obj (op V)),
    (coordinate W hW (moduleRestrict M hWV s)).re =
      X.presheaf.map (homOfLE hWV).op (coordinate V hV s).re
  im_restrict : ∀ V W (hV : V ≤ U) (hW : W ≤ U) (hWV : W ≤ V)
    (s : M.val.obj (op V)),
    (coordinate W hW (moduleRestrict M hWV s)).im =
      X.presheaf.map (homOfLE hWV).op (coordinate V hV s).im

/-- Actual quadratic coordinate comparisons, rather than an assumed line cocycle. -/
structure KummerModuleAtlas (M : X.Modules) {ι : Type u} (U : ι → X.Opens) where
  parameter : ∀ i, Γ(X, U i)ˣ
  chart : ∀ i, KummerModuleChart M (U i) (parameter i)
  overlap : ∀ i j V (hi : V ≤ U i) (hj : V ≤ U j),
    KummerAlgebra (X.presheaf.map (homOfLE hj).op (parameter j : Γ(X, U j))) ≃ₐ[Γ(X, V)]
      KummerAlgebra (X.presheaf.map (homOfLE hi).op (parameter i : Γ(X, U i)))
  overlap_coordinate : ∀ i j V (hi : V ≤ U i) (hj : V ≤ U j)
    (s : M.val.obj (op V)),
    overlap i j V hi hj ((chart j).coordinate V hj s) = (chart i).coordinate V hi s

namespace KummerModuleChart
variable {M : X.Modules} {U : X.Opens} {u : Γ(X, U)ˣ} (c : KummerModuleChart M U u)

/-- Local actual algebra trace as a natural local module-sheaf morphism. -/
def localTrace : LocalModuleHom M (SheafOfModules.unit X.ringCatSheaf) U where
  app V hV := (Algebra.trace Γ(X, V) _).comp (c.coordinate V hV).toLinearMap
  naturality V W hV hW hWV s := by
    change Algebra.trace Γ(X, W) _ (c.coordinate W hW (moduleRestrict M hWV s)) =
      X.presheaf.map (homOfLE hWV).op (Algebra.trace Γ(X, V) _ (c.coordinate V hV s))
    rw [kummer_trace, kummer_trace, c.re_restrict V W hV hW hWV]
    simp only [map_mul]
    congr 1
    exact (map_ofNat (X.presheaf.map (homOfLE hWV).op).hom 2).symm

end KummerModuleChart
namespace KummerModuleAtlas
variable {M : X.Modules} {ι : Type u} {U : ι → X.Opens} (a : KummerModuleAtlas M U)

/-- Trace invariance of actual algebra isomorphisms proves overlap compatibility. -/
theorem localTrace_compatible (i j : ι) (V : X.Opens) (hi : V ≤ U i) (hj : V ≤ U j) :
    ((a.chart i).localTrace).app V hi = ((a.chart j).localTrace).app V hj := by
  ext s
  change Algebra.trace Γ(X, V) _ ((a.chart i).coordinate V hi s) =
    Algebra.trace Γ(X, V) _ ((a.chart j).coordinate V hj s)
  rw [← a.overlap_coordinate i j V hi hj s]
  exact kummer_trace_map (a.overlap i j V hi hj) _

/-- The actual global trace morphism, constructed using the sheaf axiom. -/
def trace (hcover : iSup U = ⊤) : M ⟶ SheafOfModules.unit X.ringCatSheaf :=
  glueModuleHom U hcover (fun i ↦ (a.chart i).localTrace) a.localTrace_compatible

/-- The global trace equals the actual algebra trace on every chart subopen. -/
theorem trace_apply (hcover : iSup U = ⊤) (i : ι) (V : X.Opens) (hi : V ≤ U i)
    (s : M.val.obj (op V)) :
    (a.trace hcover).val.app (op V) s =
      Algebra.trace Γ(X, V) _ ((a.chart i).coordinate V hi s) :=
  glueModuleHom_app U hcover (fun i ↦ (a.chart i).localTrace) a.localTrace_compatible i V hi s

/-- The actual categorical kernel sheaf of the constructed trace. -/
def traceZeroSheaf (hcover : iSup U = ⊤) : X.Modules := kernel (a.trace hcover)

end KummerModuleAtlas
end EvenQuinticConic
