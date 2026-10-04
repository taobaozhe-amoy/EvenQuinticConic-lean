import EvenQuinticConic.GenericPointInjection

/-!
# Pullback of regular functions into an actual function field

For an actual morphism from an integral scheme, a regular function pulls
back to a nonzero rational function exactly when its germ at the image of
the generic point is a unit. This uses the actual local stalk map. No
injective map from the ambient function field is presumed.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace EvenQuinticConic

variable {X Y : Scheme} [IsIntegral X] (f : X ⟶ Y)

/-- A nonempty pullback open contains the generic point of the source. -/
theorem genericPoint_image_mem_of_nonempty_preimage (U : Y.Opens)
    [h : Nonempty (f ⁻¹ᵁ U)] : f.base (genericPoint X) ∈ U :=
  ((genericPoint_spec X).mem_open_set_iff (f ⁻¹ᵁ U).isOpen).mpr (by simpa using h)

/-- Pullback followed by the generic germ is the actual stalk map applied
to the germ at the image of the generic point. -/
theorem generic_pullback_eq_stalkMap (U : Y.Opens) [Nonempty (f ⁻¹ᵁ U)]
    (s : Γ(Y, U)) :
    X.germToFunctionField (f ⁻¹ᵁ U) (f.app U s) =
      f.stalkMap (genericPoint X) (Y.presheaf.germ U (f.base (genericPoint X))
        (genericPoint_image_mem_of_nonempty_preimage f U) s) := by
  exact (Scheme.stalkMap_germ_apply f U (genericPoint X)
    (genericPoint_image_mem_of_nonempty_preimage f U) s).symm

/-- The precise nonvanishing criterion for restriction to an integral
subscheme, or more generally any actual morphism with integral source. -/
theorem generic_pullback_ne_zero_iff_germ_isUnit (U : Y.Opens)
    [Nonempty (f ⁻¹ᵁ U)] (s : Γ(Y, U)) :
    X.germToFunctionField (f ⁻¹ᵁ U) (f.app U s) ≠ 0 ↔
      IsUnit (Y.presheaf.germ U (f.base (genericPoint X))
        (genericPoint_image_mem_of_nonempty_preimage f U) s) := by
  rw [generic_pullback_eq_stalkMap]
  exact (isUnit_iff_ne_zero.symm).trans
    (isUnit_map_iff (f.stalkMap (genericPoint X)).hom _)

end EvenQuinticConic
