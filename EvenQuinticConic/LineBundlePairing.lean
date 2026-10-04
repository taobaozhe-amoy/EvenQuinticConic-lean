import EvenQuinticConic.LineBundleFrames
import EvenQuinticConic.ModulePairing

/-!
# Products of line bundles constructed from actual cocycles

Multiplication of transition units gives a new actual cocycle. Coordinatewise
multiplication of the corresponding regular-function families gives sections
of the product cocycle, bilinearly and naturally under restriction.
-/

noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open scoped TensorProduct

universe u

namespace EvenQuinticConic.UnitTransition

variable {X : Scheme.{u}} {ι : Type u} {U : ι → X.Opens}

/-- Pointwise product of genuine unit transition cocycles. -/
def mul (g h : UnitTransition X U) : UnitTransition X U where
  transition i j W hi hj := g.transition i j W hi hj * h.transition i j W hi hj
  restrict := by
    intro i j W V hi hj hVW
    simp only [map_mul, g.restrict, h.restrict]
  self := by
    intro i W hi
    rw [g.self, h.self, one_mul]
  cocycle := by
    intro i j k W hi hj hk
    calc
      (g.transition i j W hi hj * h.transition i j W hi hj) *
          (g.transition j k W hj hk * h.transition j k W hj hk) =
        (g.transition i j W hi hj * g.transition j k W hj hk) *
          (h.transition i j W hi hj * h.transition j k W hj hk) := by ac_rfl
      _ = _ := by rw [g.cocycle, h.cocycle]

/-- A nonnegative tensor power at the level of actual unit cocycles. -/
def pow (g : UnitTransition X U) (n : ℕ) : UnitTransition X U where
  transition i j W hi hj := (g.transition i j W hi hj) ^ n
  restrict := by
    intro i j W V hi hj hVW
    simp only [map_pow, g.restrict]
  self := by
    intro i W hi
    rw [g.self, one_pow]
  cocycle := by
    intro i j k W hi hj hk
    rw [← mul_pow, g.cocycle]

/-- The square cocycle agrees with the product cocycle, including all
restriction and cocycle proof data by proof irrelevance. -/
theorem pow_two (g : UnitTransition X U) : g.pow 2 = g.mul g := by
  simp only [pow, mul, _root_.pow_two]

namespace Section

variable {g h : UnitTransition X U} {V W : X.Opens}

/-- The product is the literal product of actual regular coordinate sections;
the target transition rule is proved from both source transition rules. -/
def mul (s : g.Section V) (t : h.Section V) : (g.mul h).Section V :=
  ⟨fun i Z => s.val i Z * t.val i Z, by
    constructor
    · intro i A B hAV hAi hBA
      change res hBA (s.eval i A hAV hAi * t.eval i A hAV hAi) = _
      rw [map_mul, s.naturality, t.naturality]
      rfl
    · intro i j A hAV hi hj
      change s.eval i A hAV hi * t.eval i A hAV hi =
        ((g.transition i j A hi hj * h.transition i j A hi hj : Γ(X,A)ˣ) : Γ(X,A)) *
          (s.eval j A hAV hj * t.eval j A hAV hj)
      rw [s.transition i j A hAV hi hj, t.transition i j A hAV hi hj, Units.val_mul]
      ring⟩

@[simp]
theorem eval_mul (s : g.Section V) (t : h.Section V) i Z hZV hZi :
    (s.mul t).eval i Z hZV hZi = s.eval i Z hZV hZi * t.eval i Z hZV hZi := rfl

/-- Coordinatewise multiplication commutes with the actual section restriction. -/
theorem restrict_mul (hWV : W ≤ V) (s : g.Section V) (t : h.Section V) :
    (s.mul t).restrict hWV = (s.restrict hWV).mul (t.restrict hWV) := by
  apply Section.ext
  intro i Z hZW hZi
  rfl

end Section

/-- Multiplication of descended sections as an actual bilinear map. -/
def sectionMulLinear (g h : UnitTransition X U) (V : X.Opens) :
    g.Section V →ₗ[Γ(X,V)] h.Section V →ₗ[Γ(X,V)] (g.mul h).Section V where
  toFun s := {
    toFun := s.mul
    map_add' := by
      intro t t'
      apply Section.ext
      intro i Z hZV hZi
      simp only [Section.eval_mul, Section.eval_add, mul_add]
    map_smul' := by
      intro r t
      apply Section.ext
      intro i Z hZV hZi
      simp only [Section.eval_mul, Section.eval_smul, RingHom.id_apply]
      ring }
  map_add' := by
    intro s s'
    apply LinearMap.ext
    intro t
    apply Section.ext
    intro i Z hZV hZi
    change ((s + s').mul t).eval i Z hZV hZi =
      (s.mul t + s'.mul t).eval i Z hZV hZi
    simp only [Section.eval_mul, Section.eval_add, add_mul]
  map_smul' := by
    intro r s
    apply LinearMap.ext
    intro t
    apply Section.ext
    intro i Z hZV hZi
    change ((r • s).mul t).eval i Z hZV hZi = (r • s.mul t).eval i Z hZV hZi
    simp only [Section.eval_mul, Section.eval_smul]
    ring

@[simp]
theorem sectionMulLinear_apply (g h : UnitTransition X U) (V : X.Opens)
    (s : g.Section V) (t : h.Section V) :
    sectionMulLinear g h V s t = s.mul t := rfl

/-- The actual sheaves descended from two cocycles possess the natural
coordinatewise multiplication pairing into the product-cocycle sheaf. -/
def multiplicationPairing (g h : UnitTransition X U) :
    ModuleSheafPairing g.moduleSheaf h.moduleSheaf (g.mul h).moduleSheaf where
  app := sectionMulLinear g h
  naturality _ _ hWV s t := Section.restrict_mul hWV s t

@[simp]
theorem multiplicationPairing_app (g h : UnitTransition X U) (V : X.Opens)
    (s : g.Section V) (t : h.Section V) :
    (multiplicationPairing g h).app V s t = s.mul t := rfl

/-- In the actually constructed local frames, the pairing is literal
multiplication, with coefficient one. -/
theorem multiplicationPairing_coordinates (g h : UnitTransition X U)
    (i : ι) (V : X.Opens) (hVi : V ≤ U i) (s : g.Section V) (t : h.Section V) :
    ((g.mul h).frame i).coordinate V hVi ((multiplicationPairing g h).app V s t) =
      (g.frame i).coordinate V hVi s * (h.frame i).coordinate V hVi t := rfl

/-- The tensor product of local sections is genuinely isomorphic to the
local sections of the product cocycle, via the constructed chart frames. -/
def multiplicationTensorEquiv (g h : UnitTransition X U)
    (i : ι) (V : X.Opens) (hVi : V ≤ U i) :
    g.Section V ⊗[Γ(X,V)] h.Section V ≃ₗ[Γ(X,V)] (g.mul h).Section V :=
  ((TensorProduct.congr (g.coordinateEquiv i V hVi) (h.coordinateEquiv i V hVi)).trans
    (TensorProduct.lid Γ(X,V) Γ(X,V))).trans ((g.mul h).coordinateEquiv i V hVi).symm

@[simp]
theorem multiplicationTensorEquiv_tmul (g h : UnitTransition X U)
    (i : ι) (V : X.Opens) (hVi : V ≤ U i) (s : g.Section V) (t : h.Section V) :
    multiplicationTensorEquiv g h i V hVi (s ⊗ₜ[Γ(X,V)] t) = s.mul t := by
  apply ((g.mul h).coordinateEquiv i V hVi).injective
  simp only [multiplicationTensorEquiv, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply, TensorProduct.congr_tmul, TensorProduct.lid_tmul,
    smul_eq_mul, coordinateEquiv_apply, Section.eval_mul]

/-- The actual tensor lift of the natural sheaf pairing equals the constructed
local linear equivalence, rather than merely having an assumed inverse. -/
theorem lift_multiplicationPairing_eq (g h : UnitTransition X U)
    (i : ι) (V : X.Opens) (hVi : V ≤ U i) :
    TensorProduct.lift ((multiplicationPairing g h).app V) =
      (multiplicationTensorEquiv g h i V hVi).toLinearMap := by
  apply TensorProduct.ext'
  intro s t
  change s.mul t = multiplicationTensorEquiv g h i V hVi (s ⊗ₜ[Γ(X,V)] t)
  exact (multiplicationTensorEquiv_tmul g h i V hVi s t).symm

/-- Local tensor-perfectness of the actual multiplication pairing is proved
on every subopen of a chart, including the empty open. -/
theorem multiplicationPairing_tensor_bijective (g h : UnitTransition X U)
    (i : ι) (V : X.Opens) (hVi : V ≤ U i) :
    Function.Bijective (TensorProduct.lift ((multiplicationPairing g h).app V)) := by
  rw [lift_multiplicationPairing_eq g h i V hVi]
  exact (multiplicationTensorEquiv g h i V hVi).bijective

/-- In the descended frames the coefficient of the square pairing is exactly
one, so its unit property is a consequence of construction. -/
theorem multiplicationPairing_square_coefficient (g : UnitTransition X U) (i : ι) :
    modulePairingCoefficient (multiplicationPairing g g) (U i)
      (g.frame i) ((g.mul g).frame i) = 1 := by
  unfold modulePairingCoefficient
  rw [multiplicationPairing_coordinates]
  change g.coordinateEquiv i (U i) le_rfl
      ((g.coordinateEquiv i (U i) le_rfl).symm 1) *
    g.coordinateEquiv i (U i) le_rfl
      ((g.coordinateEquiv i (U i) le_rfl).symm 1) = 1
  simp only [LinearEquiv.apply_symm_apply, one_mul]

end EvenQuinticConic.UnitTransition
