import EvenQuinticConic.LineBundleGluing

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
universe u
namespace EvenQuinticConic.UnitTransition
variable {X : Scheme.{u}} {ι : Type u} {U : ι → X.Opens} (g : UnitTransition X U)

/-- Scalar coordinates indexed by chart and subordinate open. -/
def Family (V : X.Opens) := ∀ i (W : {W : X.Opens // W ≤ V ∧ W ≤ U i}), Γ(X,W.val)

instance (V : X.Opens) : AddCommGroup (Family (U := U) V) :=
  inferInstanceAs (AddCommGroup (∀ i (W : {W : X.Opens // W ≤ V ∧ W ≤ U i}), Γ(X,W.val)))

variable {g}
def Family.eval {V : X.Opens} (s : Family (U := U) V) i W
    (hWV : W ≤ V) (hWi : W ≤ U i) : Γ(X,W) := s i ⟨W, hWV, hWi⟩

variable (g)
/-- Compatible coordinate families form an additive group. -/
def sectionGroup (V : X.Opens) : AddSubgroup (Family (U := U) V) where
  carrier := {s | (∀ i W Z (hWV : W ≤ V) (hWi : W ≤ U i) (hZW : Z ≤ W),
      res hZW (s.eval i W hWV hWi) = s.eval i Z (hZW.trans hWV) (hZW.trans hWi)) ∧
    (∀ i j W (hWV : W ≤ V) (hi : W ≤ U i) (hj : W ≤ U j),
      s.eval i W hWV hi = (g.transition i j W hi hj : Γ(X,W)) * s.eval j W hWV hj)}
  zero_mem' := by
    constructor
    · intro i W Z hWV hWi hZW; change res hZW 0 = 0; exact map_zero _
    · intro i j W hWV hi hj; change 0 = _ * 0; exact (mul_zero _).symm
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    constructor
    · intro i W Z hWV hWi hZW
      change res hZW (a.eval i W hWV hWi + b.eval i W hWV hWi) = _
      rw [map_add, ha, hb]; rfl
    · intro i j W hWV hi hj
      change a.eval i W hWV hi + b.eval i W hWV hi = _
      rw [ha', hb']; exact (mul_add _ _ _).symm
  neg_mem' := by
    rintro a ⟨ha, ha'⟩
    constructor
    · intro i W Z hWV hWi hZW
      change res hZW (-a.eval i W hWV hWi) = _
      rw [map_neg, ha]; rfl
    · intro i j W hWV hi hj
      change -a.eval i W hWV hi = _
      rw [ha']; exact (mul_neg _ _).symm

/-- The group of descended sections over one open. -/
def Section (V : X.Opens) : Type u := ↥(g.sectionGroup V)

instance (V : X.Opens) : AddCommGroup (g.Section V) :=
  inferInstanceAs (AddCommGroup ↥(g.sectionGroup V))

namespace Section
variable {g} {V : X.Opens}
def eval (s : g.Section V) i W (hWV : W ≤ V) (hWi : W ≤ U i) : Γ(X,W) :=
  s.val.eval i W hWV hWi

@[ext] theorem ext (s t : g.Section V)
    (h : ∀ i W hWV hWi, s.eval i W hWV hWi = t.eval i W hWV hWi) : s = t := by
  apply Subtype.ext
  funext i W
  exact h i W.val W.prop.1 W.prop.2

theorem naturality (s : g.Section V) i W Z (hWV : W ≤ V) (hWi : W ≤ U i) (hZW : Z ≤ W) :
    res hZW (s.eval i W hWV hWi) = s.eval i Z (hZW.trans hWV) (hZW.trans hWi) :=
  s.prop.1 i W Z hWV hWi hZW

theorem transition (s : g.Section V) i j W (hWV : W ≤ V) (hi : W ≤ U i) (hj : W ≤ U j) :
    s.eval i W hWV hi = (g.transition i j W hi hj : Γ(X,W)) * s.eval j W hWV hj :=
  s.prop.2 i j W hWV hi hj

@[simp] theorem eval_zero i W hWV hWi : (0 : g.Section V).eval i W hWV hWi = 0 := rfl
@[simp] theorem eval_add (s t : g.Section V) i W hWV hWi :
    (s + t).eval i W hWV hWi = s.eval i W hWV hWi + t.eval i W hWV hWi := rfl

instance : SMul Γ(X,V) (g.Section V) where
  smul r s := ⟨fun i W ↦ res W.prop.1 r * s.val i W, by
    constructor
    · intro i W Z hWV hWi hZW
      change res hZW (res hWV r * s.eval i W hWV hWi) = _
      rw [map_mul, res_res, s.naturality]; rfl
    · intro i j W hWV hi hj
      change res hWV r * s.eval i W hWV hi = _
      rw [s.transition i j W hWV hi hj]
      rw [mul_left_comm]
      rfl⟩

@[simp] theorem eval_smul (r : Γ(X,V)) (s : g.Section V) i W hWV hWi :
    (r • s).eval i W hWV hWi = res hWV r * s.eval i W hWV hWi := rfl

instance : Module Γ(X,V) (g.Section V) where
  one_smul s := by ext; simp
  mul_smul r t s := by ext; simp [mul_assoc]
  smul_zero r := by ext; simp
  smul_add r s t := by ext; simp [mul_add]
  add_smul r t s := by ext; simp [add_mul]
  zero_smul s := by ext; simp

/-- Restriction simply forgets coordinates outside the smaller open. -/
def restrict {W : X.Opens} (hWV : W ≤ V) (s : g.Section V) : g.Section W :=
  ⟨fun i Z ↦ s.eval i Z.val (Z.prop.1.trans hWV) Z.prop.2, by
    constructor
    · intro i A B hAW hAi hBA
      exact s.naturality i A B (hAW.trans hWV) hAi hBA
    · intro i j A hAW hi hj
      exact s.transition i j A (hAW.trans hWV) hi hj⟩

@[simp] theorem eval_restrict {W : X.Opens} (hWV : W ≤ V) (s : g.Section V)
    i Z hZW hZi :
    (s.restrict hWV).eval i Z hZW hZi = s.eval i Z (hZW.trans hWV) hZi := rfl

end Section

/-- The module presheaf constructed solely from transition functions. -/
noncomputable def presheaf : X.PresheafOfModules where
  obj V := by
    change ModuleCat Γ(X,V.unop)
    exact ModuleCat.of Γ(X,V.unop) (g.Section V.unop)
  map {V W} f := by
    rcases V with ⟨V⟩
    rcases W with ⟨W⟩
    exact ModuleCat.semilinearMapAddEquiv (X.presheaf.map f).hom
      (ModuleCat.of Γ(X,V) (g.Section V))
      (ModuleCat.of Γ(X,W) (g.Section W)) {
      toFun := Section.restrict f.unop.le
      map_add' := by intros; apply Section.ext; intros; rfl
      map_smul' := by
        intro r s
        apply Section.ext
        intro i Z hZW hZi
        change res (hZW.trans f.unop.le) r * s.eval i Z (hZW.trans f.unop.le) hZi =
          res hZW ((X.presheaf.map f).hom r) * s.eval i Z (hZW.trans f.unop.le) hZi
        have hf : (homOfLE f.unop.le).op = f := Subsingleton.elim _ _
        rw [← hf]
        exact congrArg (fun t ↦ t * s.eval i Z (hZW.trans f.unop.le) hZi)
          (res_res f.unop.le hZW r).symm }
  map_id := by
    rintro ⟨V⟩
    apply ModuleCat.hom_ext
    apply DFunLike.ext
    intro s
    apply Section.ext
    intros
    rfl
  map_comp := by
    rintro ⟨V⟩ ⟨W⟩ ⟨Z⟩ f h
    apply ModuleCat.hom_ext
    apply DFunLike.ext
    intro s
    apply Section.ext
    intros
    rfl

@[simp] theorem presheaf_map_eval {V W : X.Opens} (hWV : W ≤ V) (s : g.Section V)
    i Z hZW hZi :
    (g.presheaf.map (homOfLE hWV).op s).eval i Z hZW hZi =
      s.eval i Z (hZW.trans hWV) hZi := rfl

end EvenQuinticConic.UnitTransition
