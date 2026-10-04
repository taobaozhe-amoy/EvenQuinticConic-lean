import EvenQuinticConic.LocalFrames
import EvenQuinticConic.GenericPointInjection

/-!
# Rational coefficients in actual local frames

For an integral scheme, rational coefficients in coherent frames determine
compatible regular sections once their positive powers are regular units on
normal affine opens.  Transition factors are computed from the actual
linear coordinates; no gluing or global isomorphism is assumed.
-/

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace EvenQuinticConic

variable (X : Scheme.{u}) [IsIntegral X] {M : X.Modules}

/-- Nonempty opens of an integral scheme intersect at its generic point. -/
theorem integral_open_inf_nonempty (U V : X.Opens) [Nonempty U] [Nonempty V] :
    Nonempty (U ⊓ V : X.Opens) := by
  have hU : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by
      simpa using (inferInstance : Nonempty U))
  have hV : genericPoint X ∈ V :=
    ((genericPoint_spec X).mem_open_set_iff V.isOpen).mpr (by
      simpa using (inferInstance : Nonempty V))
  exact ⟨⟨genericPoint X, hU, hV⟩⟩

/-- The actual change-of-frame coefficient on the intersection. -/
noncomputable def frameTransition {U V : X.Opens}
    (e : ModuleSheafFrame M U) (f : ModuleSheafFrame M V) : Γ(X, U ⊓ V) :=
  e.coordinate (U ⊓ V) inf_le_left ((f.coordinate (U ⊓ V) inf_le_right).symm 1)

omit [IsIntegral X] in
/-- Applying one frame to a vector expressed in another frame multiplies its
coordinate by the actual transition coefficient. -/
theorem frameTransition_apply {U V : X.Opens}
    (e : ModuleSheafFrame M U) (f : ModuleSheafFrame M V) (a : Γ(X, U ⊓ V)) :
    e.coordinate (U ⊓ V) inf_le_left ((f.coordinate (U ⊓ V) inf_le_right).symm a) =
      frameTransition X e f * a := by
  let a' : X.ringCatSheaf.val.obj (op (U ⊓ V)) := a
  rw [mul_comm]
  change e.coordinate (U ⊓ V) inf_le_left
    ((f.coordinate (U ⊓ V) inf_le_right).symm a') =
    a' • e.coordinate (U ⊓ V) inf_le_left
      ((f.coordinate (U ⊓ V) inf_le_right).symm (1 : X.ringCatSheaf.val.obj (op (U ⊓ V))))
  rw [← map_smul, ← map_smul]
  simp

omit [IsIntegral X] in
/-- A genuine change-of-frame coefficient is a unit. -/
theorem frameTransition_isUnit {U V : X.Opens}
    (e : ModuleSheafFrame M U) (f : ModuleSheafFrame M V) :
    IsUnit (frameTransition X e f) := by
  apply (IsUnit.isUnit_iff_mulLeft_bijective).mpr
  have heq : (fun a : Γ(X, U ⊓ V) ↦ frameTransition X e f * a) =
      (fun a ↦ e.coordinate (U ⊓ V) inf_le_left
        ((f.coordinate (U ⊓ V) inf_le_right).symm a)) := by
    funext a
    exact (frameTransition_apply X e f a).symm
  rw [heq]
  exact (e.coordinate (U ⊓ V) inf_le_left).bijective.comp
    (f.coordinate (U ⊓ V) inf_le_right).symm.bijective

/-- The transition coefficient in the actual function field. -/
noncomputable def genericFrameTransition {U V : X.Opens} [Nonempty U] [Nonempty V]
    (e : ModuleSheafFrame M U) (f : ModuleSheafFrame M V) : X.functionField := by
  letI : Nonempty (U ⊓ V : X.Opens) := integral_open_inf_nonempty X U V
  exact X.germToFunctionField (U ⊓ V) (frameTransition X e f)

/-- Unit coefficients whose rational values satisfy the actual frame
transition equations produce compatible sections of the actual module sheaf. -/
theorem frame_inverse_units_compatible
    {ι : Type*} (U : ι → X.Opens) [∀ i, Nonempty (U i)]
    (frame : ∀ i, ModuleSheafFrame M (U i))
    (r : ι → X.functionField) (w : ∀ i, Γ(X, U i)ˣ)
    (hw : ∀ i, X.germToFunctionField (U i) (w i : Γ(X, U i)) = r i)
    (htransition : ∀ i j,
      r i = genericFrameTransition X (frame i) (frame j) * r j) :
    TopCat.Presheaf.IsCompatible ((SheafOfModules.toSheaf X.ringCatSheaf).obj M).val U
      (fun i ↦ (frame i).coordinate (U i) le_rfl |>.symm (w i : Γ(X, U i))) := by
  intro i j
  let W := U i ⊓ U j
  letI : Nonempty W := integral_open_inf_nonempty X (U i) (U j)
  let ti := (frame i).coordinate (U i) le_rfl |>.symm (w i : Γ(X, U i))
  let tj := (frame j).coordinate (U j) le_rfl |>.symm (w j : Γ(X, U j))
  change M.val.map (Opens.infLELeft (U i) (U j)).op ti =
    M.val.map (Opens.infLERight (U i) (U j)).op tj
  apply ((frame i).coordinate W inf_le_left).injective
  have hi : (frame i).coordinate W inf_le_left
      (M.val.map (Opens.infLELeft (U i) (U j)).op ti) =
      X.presheaf.map (Opens.infLELeft (U i) (U j)).op (w i : Γ(X, U i)) := by
    simpa only [ti, LinearEquiv.apply_symm_apply] using
      ((frame i).coordinate_restrict (U i) W le_rfl inf_le_left inf_le_left ti)
  have hj : M.val.map (Opens.infLERight (U i) (U j)).op tj =
      ((frame j).coordinate W inf_le_right).symm
        (X.presheaf.map (Opens.infLERight (U i) (U j)).op (w j : Γ(X, U j))) := by
    apply ((frame j).coordinate W inf_le_right).injective
    simpa only [tj, LinearEquiv.apply_symm_apply] using
      ((frame j).coordinate_restrict (U j) W le_rfl inf_le_right inf_le_right tj)
  rw [hi, hj]
  rw [frameTransition_apply X (frame i) (frame j)]
  apply X.germToFunctionField_injective W
  rw [map_mul, generic_germ_restrict, generic_germ_restrict, hw, hw]
  exact htransition i j

/-- Rational coefficients in actual frames, satisfying the actual transition
relations and positive-power unit identities, extend to a global free
generator and hence an actual isomorphism of module sheaves. The affine
coordinate rings are explicitly assumed integrally closed. -/
theorem exists_global_generator_of_rational_frame_powers
    {ι : Type*} (U : ι → X.Opens) [∀ i, Nonempty (U i)]
    (hcover : iSup U = ⊤) (hU : ∀ i, IsAffineOpen (U i))
    [∀ i, IsIntegrallyClosed Γ(X, U i)]
    (frame : ∀ i, ModuleSheafFrame M (U i))
    (r : ι → X.functionField) (v : ∀ i, Γ(X, U i)ˣ)
    {n : ℕ} (hn : 0 < n)
    (hpower : ∀ i, r i ^ n = X.germToFunctionField (U i) (v i : Γ(X, U i)))
    (htransition : ∀ i j,
      r i = genericFrameTransition X (frame i) (frame j) * r j) :
    ∃ w : ∀ i, Γ(X, U i)ˣ,
      (∀ i, X.germToFunctionField (U i) (w i : Γ(X, U i)) = r i ∧ w i ^ n = v i) ∧
      ∃ s : M.sections,
        (∀ i, (frame i).coordinate (U i) le_rfl (s.eval (op (U i))) = (w i : Γ(X, U i))) ∧
        ∃ e : SheafOfModules.unit X.ringCatSheaf ≅ M,
          ∀ V (a : X.ringCatSheaf.val.obj (op V)),
            e.hom.val.app (op V) a = a • s.eval (op V) := by
  choose w hw using fun i ↦
    (existsUnique_regular_unit_of_generic_pow_eq X (U i) (hU i)
      (r i) (v i) hn (hpower i)).exists
  let t : ∀ i, M.val.obj (op (U i)) := fun i ↦
    ((frame i).coordinate (U i) le_rfl).symm (w i : Γ(X, U i))
  have ht : TopCat.Presheaf.IsCompatible M.val.presheaf U t :=
    frame_inverse_units_compatible X U frame r w (fun i ↦ (hw i).1) htransition
  have hunit : ∀ i, IsUnit ((frame i).coordinate (U i) le_rfl (t i)) := by
    intro i
    simpa only [t, LinearEquiv.apply_symm_apply] using (w i).isUnit
  obtain ⟨s, hs, e, he⟩ :=
    exists_global_generator_of_compatible_local_units U hcover frame t ht hunit
  refine ⟨w, hw, s, ?_, e, he⟩
  intro i
  rw [hs i]
  exact ((frame i).coordinate (U i) le_rfl).apply_symm_apply (w i : Γ(X, U i))

/-- The version needed for a quotient of two sections: even at their common
zeros, the square identity forces the quotient coordinate to be a unit.
Once its actual frame-transition equations hold, the resulting local
sections glue and trivialize the actual module sheaf. -/
theorem exists_global_generator_of_rational_frame_square_ratios
    {ι : Type*} (U : ι → X.Opens) [∀ i, Nonempty (U i)]
    (hcover : iSup U = ⊤) (hU : ∀ i, IsAffineOpen (U i))
    [∀ i, IsIntegrallyClosed Γ(X, U i)]
    (frame : ∀ i, ModuleSheafFrame M (U i))
    (x y : ι → X.functionField) (hy : ∀ i, y i ≠ 0)
    (a b : ∀ i, Γ(X, U i)ˣ)
    (hsquare : ∀ i, X.germToFunctionField (U i) (a i : Γ(X, U i)) * x i ^ 2 =
      X.germToFunctionField (U i) (b i : Γ(X, U i)) * y i ^ 2)
    (htransition : ∀ i j, x i / y i =
      genericFrameTransition X (frame i) (frame j) * (x j / y j)) :
    ∃ w : ∀ i, Γ(X, U i)ˣ,
      (∀ i, X.germToFunctionField (U i) (w i : Γ(X, U i)) = x i / y i ∧
        a i * w i ^ 2 = b i) ∧
      ∃ s : M.sections,
        (∀ i, (frame i).coordinate (U i) le_rfl (s.eval (op (U i))) = (w i : Γ(X, U i))) ∧
        ∃ e : SheafOfModules.unit X.ringCatSheaf ≅ M,
          ∀ V (c : X.ringCatSheaf.val.obj (op V)),
            e.hom.val.app (op V) c = c • s.eval (op V) := by
  choose w hw using fun i ↦
    (existsUnique_regular_unit_of_generic_sq_ratio X (U i) (hU i)
      (x i) (y i) (hy i) (a i) (b i) (hsquare i)).exists
  let t : ∀ i, M.val.obj (op (U i)) := fun i ↦
    ((frame i).coordinate (U i) le_rfl).symm (w i : Γ(X, U i))
  have ht : TopCat.Presheaf.IsCompatible M.val.presheaf U t :=
    frame_inverse_units_compatible X U frame (fun i ↦ x i / y i) w
      (fun i ↦ (hw i).1) htransition
  have hunit : ∀ i, IsUnit ((frame i).coordinate (U i) le_rfl (t i)) := by
    intro i
    simpa only [t, LinearEquiv.apply_symm_apply] using (w i).isUnit
  obtain ⟨s, hs, e, he⟩ :=
    exists_global_generator_of_compatible_local_units U hcover frame t ht hunit
  refine ⟨w, hw, s, ?_, e, he⟩
  intro i
  rw [hs i]
  exact ((frame i).coordinate (U i) le_rfl).apply_symm_apply (w i : Γ(X, U i))

end EvenQuinticConic
