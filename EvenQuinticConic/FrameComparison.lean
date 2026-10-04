import EvenQuinticConic.RationalSectionFrames
import EvenQuinticConic.ModuleHomGluing
import EvenQuinticConic.ModuleGenericInjection

/-!
# Comparing actual line-module sheaves by quotients of their sections

Local comparisons are actual linear equivalences built from coherent
frames and units. Their agreement is deduced from the fact that they send
the same generically nonzero section to the same section.
-/

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace EvenQuinticConic

section LinearAlgebra

variable {A : Type*} [CommRing A] [IsDomain A]
  {P Q : Type*} [AddCommGroup P] [AddCommGroup Q] [Module A P] [Module A Q]

/-- Maps between rank-one free modules over a domain agree if they agree on
one nonzero vector. -/
theorem linearMap_eq_of_rankOne_apply_eq
    (p : P ≃ₗ[A] A) (q : Q ≃ₗ[A] A)
    (f g : P →ₗ[A] Q) (a : P) (ha : p a ≠ 0) (h : f a = g a) : f = g := by
  have hrepr (v : P) : v = p v • p.symm 1 := by
    apply p.injective
    simp
  have hcoeff : q (f (p.symm 1)) = q (g (p.symm 1)) := by
    have hh := congrArg q h
    nth_rw 1 [hrepr a] at hh
    nth_rw 2 [hrepr a] at hh
    simp only [map_smul, smul_eq_mul] at hh
    exact mul_left_cancel₀ ha hh
  ext v
  apply q.injective
  rw [hrepr v]
  simp only [map_smul, hcoeff]

end LinearAlgebra

variable (X : Scheme.{u}) {M N : X.Modules}

local instance (V : X.Opens) : CommRing (X.ringCatSheaf.val.obj (op V)) :=
  inferInstanceAs (CommRing Γ(X, V))

/-- The local comparison determined by a unit coefficient, expressed in
actual frames. The source is `N` and the target is `M`. -/
noncomputable def frameUnitComparison {U : X.Opens}
    (m : ModuleSheafFrame M U) (n : ModuleSheafFrame N U)
    (w : Γ(X, U)ˣ) (V : X.Opens) (hV : V ≤ U) :
    N.val.obj (op V) ≃ₗ[X.ringCatSheaf.val.obj (op V)] M.val.obj (op V) :=
  (n.coordinate V hV).trans
    ((LinearEquiv.smulOfUnit (R := X.ringCatSheaf.val.obj (op V))
      (M := X.ringCatSheaf.val.obj (op V))
      (Units.map (X.ringCatSheaf.val.map (homOfLE hV).op).hom.toMonoidHom
        (show (X.ringCatSheaf.val.obj (op U))ˣ from w))).trans
      (m.coordinate V hV).symm)

/-- Formula for the actual local comparison in target coordinates. -/
theorem frameUnitComparison_coordinate {U : X.Opens}
    (m : ModuleSheafFrame M U) (n : ModuleSheafFrame N U)
    (w : Γ(X, U)ˣ) (V : X.Opens) (hV : V ≤ U) (b : N.val.obj (op V)) :
    m.coordinate V hV (frameUnitComparison X m n w V hV b) =
      X.presheaf.map (homOfLE hV).op (w : Γ(X, U)) * (show Γ(X, V) from n.coordinate V hV b) := by
  simp only [frameUnitComparison, LinearEquiv.trans_apply, LinearEquiv.smulOfUnit,
    DistribMulAction.toLinearEquiv_apply, Units.smul_def]
  exact (m.coordinate V hV).apply_symm_apply _

/-- The local comparison commutes with the actual module restriction maps. -/
theorem frameUnitComparison_restrict {U : X.Opens}
    (m : ModuleSheafFrame M U) (n : ModuleSheafFrame N U)
    (w : Γ(X, U)ˣ) (V W : X.Opens) (hV : V ≤ U) (hW : W ≤ U)
    (hWV : W ≤ V) (b : N.val.obj (op V)) :
    M.val.map (homOfLE hWV).op (frameUnitComparison X m n w V hV b) =
      frameUnitComparison X m n w W hW (N.val.map (homOfLE hWV).op b) := by
  apply (m.coordinate W hW).injective
  rw [m.coordinate_restrict V W hV hW hWV, frameUnitComparison_coordinate,
    frameUnitComparison_coordinate, n.coordinate_restrict V W hV hW hWV b]
  change X.presheaf.map (homOfLE hWV).op
      (X.presheaf.map (homOfLE hV).op (w : Γ(X, U)) * (show Γ(X, V) from n.coordinate V hV b)) = _
  rw [map_mul]
  congr 1
  rw [← ConcreteCategory.comp_apply, ← X.presheaf.map_comp]
  rfl

/-- A local comparison carries the source section to the target section
on every subopen once its coefficient equation holds on the covering open. -/
theorem frameUnitComparison_apply_section {U : X.Opens}
    (m : ModuleSheafFrame M U) (n : ModuleSheafFrame N U)
    (w : Γ(X, U)ˣ) (s : M.sections) (a : N.sections)
    (hw : (w : Γ(X, U)) * (show Γ(X, U) from n.coordinate U le_rfl (a.eval (op U))) =
      m.coordinate U le_rfl (s.eval (op U)))
    (V : X.Opens) (hV : V ≤ U) :
    frameUnitComparison X m n w V hV (a.eval (op V)) = s.eval (op V) := by
  apply (m.coordinate V hV).injective
  rw [frameUnitComparison_coordinate, n.coordinate_section_restrict,
    m.coordinate_section_restrict]
  change X.presheaf.map (homOfLE hV).op (w : Γ(X, U)) *
      X.presheaf.map (homOfLE hV).op
        (show Γ(X, U) from n.coordinate U le_rfl (a.eval (op U))) =
    X.presheaf.map (homOfLE hV).op (m.coordinate U le_rfl (s.eval (op U)))
  rw [← map_mul, hw]

variable [IsIntegral X]

local instance (V : X.Opens) [Nonempty V] :
    IsDomain (X.ringCatSheaf.val.obj (op V)) := inferInstanceAs (IsDomain Γ(X, V))

/-- A generically nonzero global section has a nonzero coordinate on every
nonempty subopen of a trivializing open. -/
theorem frame_section_nonzero_on_subopen {U : X.Opens} [Nonempty U]
    (n : ModuleSheafFrame N U) (a : N.sections)
    (ha : X.germToFunctionField U (n.coordinate U le_rfl (a.eval (op U))) ≠ 0)
    (V : X.Opens) [Nonempty V] (hV : V ≤ U) :
    n.coordinate V hV (a.eval (op V)) ≠ 0 := by
  intro hzero
  apply ha
  rw [← generic_germ_restrict X (homOfLE hV)
    (show Γ(X, U) from n.coordinate U le_rfl (a.eval (op U)))]
  have hres := n.coordinate_section_restrict a V hV
  change X.germToFunctionField V
    (X.ringCatSheaf.val.map (homOfLE hV).op
      (n.coordinate U le_rfl (a.eval (op U)))) = 0
  rw [← hres, hzero, map_zero]

/-- Local comparisons with the same action on a generically nonzero source
section agree on overlaps. Compatibility is proved, not supplied as input. -/
theorem frameUnitComparisons_agree
    {U₁ U₂ : X.Opens} [Nonempty U₁] [Nonempty U₂]
    (m₁ : ModuleSheafFrame M U₁) (n₁ : ModuleSheafFrame N U₁)
    (m₂ : ModuleSheafFrame M U₂) (n₂ : ModuleSheafFrame N U₂)
    (w₁ : Γ(X, U₁)ˣ) (w₂ : Γ(X, U₂)ˣ) (s : M.sections) (a : N.sections)
    (ha : X.germToFunctionField U₁ (n₁.coordinate U₁ le_rfl (a.eval (op U₁))) ≠ 0)
    (hw₁ : (w₁ : Γ(X, U₁)) * (show Γ(X, U₁) from n₁.coordinate U₁ le_rfl (a.eval (op U₁))) =
      m₁.coordinate U₁ le_rfl (s.eval (op U₁)))
    (hw₂ : (w₂ : Γ(X, U₂)) * (show Γ(X, U₂) from n₂.coordinate U₂ le_rfl (a.eval (op U₂))) =
      m₂.coordinate U₂ le_rfl (s.eval (op U₂)))
    (V : X.Opens) (h₁ : V ≤ U₁) (h₂ : V ≤ U₂) :
    (frameUnitComparison X m₁ n₁ w₁ V h₁).toLinearMap =
      (frameUnitComparison X m₂ n₂ w₂ V h₂).toLinearMap := by
  by_cases hV : Nonempty V
  · letI : Nonempty V := hV
    apply linearMap_eq_of_rankOne_apply_eq (n₁.coordinate V h₁) (m₁.coordinate V h₁)
      _ _ (a.eval (op V)) (frame_section_nonzero_on_subopen X n₁ a ha V h₁)
    exact (frameUnitComparison_apply_section X m₁ n₁ w₁ s a hw₁ V h₁).trans
      (frameUnitComparison_apply_section X m₂ n₂ w₂ s a hw₂ V h₂).symm
  · have hbot : V = ⊥ := (Opens.not_nonempty_iff_eq_bot V).mp (by
      intro h
      exact hV ⟨⟨h.choose, h.choose_spec⟩⟩)
    subst V
    ext b
    apply (m₁.coordinate ⊥ h₁).injective
    exact @Subsingleton.elim Γ(X, ⊥) inferInstance _ _

/-- A weighted square relation in the actual function field gives a unit
comparison coefficient carrying the source section to the target section. -/
theorem exists_frame_comparison_unit {U : X.Opens} [Nonempty U]
    (hU : IsAffineOpen U) [IsIntegrallyClosed Γ(X, U)]
    (m : ModuleSheafFrame M U) (n : ModuleSheafFrame N U)
    (s : M.sections) (a : N.sections)
    (ha : X.germToFunctionField U (n.coordinate U le_rfl (a.eval (op U))) ≠ 0)
    (p q : Γ(X, U)ˣ)
    (hsquare : X.germToFunctionField U (p : Γ(X, U)) *
        X.germToFunctionField U (m.coordinate U le_rfl (s.eval (op U))) ^ 2 =
      X.germToFunctionField U (q : Γ(X, U)) *
        X.germToFunctionField U (n.coordinate U le_rfl (a.eval (op U))) ^ 2) :
    ∃ w : Γ(X, U)ˣ,
      (w : Γ(X, U)) * (show Γ(X, U) from n.coordinate U le_rfl (a.eval (op U))) =
        m.coordinate U le_rfl (s.eval (op U)) ∧ p * w ^ 2 = q := by
  obtain ⟨w, hw, _⟩ := existsUnique_regular_unit_of_generic_sq_ratio X U hU
    (X.germToFunctionField U (m.coordinate U le_rfl (s.eval (op U))))
    (X.germToFunctionField U (n.coordinate U le_rfl (a.eval (op U)))) ha p q hsquare
  refine ⟨w, ?_, hw.2⟩
  apply X.germToFunctionField_injective U
  rw [map_mul, hw.1, div_mul_cancel₀ _ ha]

omit [IsIntegral X] in
/-- Unit comparison in coherent frames as actual natural local linear maps. -/
noncomputable def frameUnitLocalHom {U : X.Opens}
    (m : ModuleSheafFrame M U) (n : ModuleSheafFrame N U)
    (w : Γ(X, U)ˣ) : LocalModuleHom N M U where
  app V hV := (frameUnitComparison X m n w V hV).toLinearMap
  naturality V W hV hW hWV b :=
    (frameUnitComparison_restrict X m n w V W hV hW hWV b).symm

/-- Actual line-module sheaves are isomorphic when two genuine global
sections satisfy local weighted square identities and the source section
is nonzero. Local comparison maps and their overlap compatibility are
constructed in the proof, rather than assumed. -/
theorem exists_moduleSheafIso_of_frame_square_relation
    {ι : Type*} (U : ι → X.Opens) [∀ i, Nonempty (U i)]
    (hcover : iSup U = ⊤) (hU : ∀ i, IsAffineOpen (U i))
    [∀ i, IsIntegrallyClosed Γ(X, U i)]
    (m : ∀ i, ModuleSheafFrame M (U i))
    (n : ∀ i, ModuleSheafFrame N (U i))
    (s : M.val.obj (op ⊤)) (a : N.val.obj (op ⊤)) (ha : a ≠ 0)
    (p q : ∀ i, Γ(X, U i)ˣ)
    (hsquare : ∀ i, X.germToFunctionField (U i) (p i : Γ(X, U i)) *
        (moduleGlobalGenericLinearMap M (U i) (m i) s) ^ 2 =
      X.germToFunctionField (U i) (q i : Γ(X, U i)) *
        (moduleGlobalGenericLinearMap N (U i) (n i) a) ^ 2) :
    ∃ e : N ≅ M, e.hom.val.app (op ⊤) a = s := by
  let sf := moduleGlobalSectionFamily M s
  let af := moduleGlobalSectionFamily N a
  have hna : ∀ i, X.germToFunctionField (U i)
      ((n i).coordinate (U i) le_rfl (af.eval (op (U i)))) ≠ 0 := by
    intro i hzero
    apply ha
    apply moduleGlobalGenericLinearMap_injective N U hcover n (U i) (n i)
    change moduleGlobalGenericLinearMap N (U i) (n i) a =
      moduleGlobalGenericLinearMap N (U i) (n i) 0
    simpa only [map_zero] using hzero
  choose w hw hwpow using fun i ↦ exists_frame_comparison_unit X (hU i)
    (m i) (n i) sf af (hna i) (p i) (q i) (hsquare i)
  let f : ∀ i, LocalModuleHom N M (U i) := fun i ↦
    frameUnitLocalHom X (m i) (n i) (w i)
  have hcompat : ∀ i j V (hi : V ≤ U i) (hj : V ≤ U j),
      (f i).app V hi = (f j).app V hj := by
    intro i j V hi hj
    exact frameUnitComparisons_agree X (m i) (n i) (m j) (n j)
      (w i) (w j) sf af (hna i) (hw i) (hw j) V hi hj
  have hf : ∀ i V (hi : V ≤ U i), Function.Bijective ((f i).app V hi) := by
    intro i V hi
    exact (frameUnitComparison X (m i) (n i) (w i) V hi).bijective
  let e := glueModuleIso U hcover f hcompat hf
  refine ⟨e, ?_⟩
  apply module_eq_of_cover_restrictions U hcover ⊤
  intro i
  change M.val.map (homOfLE (show ⊤ ⊓ U i ≤ ⊤ from inf_le_left)).op
    (e.hom.val.app (op ⊤) a) = _
  rw [← PresheafOfModules.naturality_apply]
  rw [glueModuleIso_hom_app U hcover f hcompat hf i (⊤ ⊓ U i) inf_le_right]
  exact frameUnitComparison_apply_section X (m i) (n i) (w i) sf af (hw i)
    (⊤ ⊓ U i) inf_le_right

end EvenQuinticConic
