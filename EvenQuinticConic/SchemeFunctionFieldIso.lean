import EvenQuinticConic.SchemeScalarAction

/-!
# Function fields induced by actual scheme isomorphisms

The equivalences in this file use the actual map on the generic stalk.
The identification of its source with the target's function field is supplied
by the equality of generic points under an open immersion.  Compatibility
with regular functions is proved before installing any base-field action.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace EvenQuinticConic

section OpenImmersion

variable {X Y : Scheme.{u}} [IrreducibleSpace X] [IrreducibleSpace Y]
    (f : X ⟶ Y) [IsOpenImmersion f]

/-- The actual generic-stalk isomorphism of a nonempty open immersion. -/
def openImmersionFunctionFieldIso : Y.functionField ≅ X.functionField :=
  Y.presheaf.stalkCongr (.of_eq (genericPoint_eq_of_isOpenImmersion f).symm) ≪≫
    asIso (f.stalkMap (genericPoint X))

/-- The field map is the actual stalk map, preceded only by identification
of the two equal generic points in the target. -/
theorem openImmersionFunctionFieldIso_hom :
    (openImmersionFunctionFieldIso f).hom =
      (Y.presheaf.stalkCongr
        (.of_eq (genericPoint_eq_of_isOpenImmersion f).symm)).hom ≫
      f.stalkMap (genericPoint X) := rfl

/-- A regular function followed by the generic-stalk isomorphism is its
actual pullback followed by the generic germ. -/
@[reassoc]
theorem openImmersionFunctionFieldIso_germ (U : Y.Opens)
    [Nonempty U] [Nonempty (f ⁻¹ᵁ U)] :
    Y.germToFunctionField U ≫ (openImmersionFunctionFieldIso f).hom =
      f.app U ≫ X.germToFunctionField (f ⁻¹ᵁ U) := by
  simp only [openImmersionFunctionFieldIso, Iso.trans_hom,
    TopCat.Presheaf.stalkCongr_hom, asIso_hom, ← Category.assoc]
  rw [TopCat.Presheaf.germ_stalkSpecializes]
  exact Scheme.stalkMap_germ f U (genericPoint X) _

/-- The same compatibility as an equality of actual germs. -/
theorem openImmersionFunctionFieldIso_germ_apply (U : Y.Opens)
    [Nonempty U] [Nonempty (f ⁻¹ᵁ U)] (s : Γ(Y, U)) :
    (openImmersionFunctionFieldIso f).hom (Y.germToFunctionField U s) =
      X.germToFunctionField (f ⁻¹ᵁ U) (f.app U s) :=
  DFunLike.congr_fun
    (CommRingCat.hom_ext_iff.mp (openImmersionFunctionFieldIso_germ f U)) s

end OpenImmersion

section Iso

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (e : X ≅ Y)

local instance : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
local instance : Nonempty (⊤ : Y.Opens) := ⟨⟨genericPoint Y, trivial⟩⟩

/-- Contravariant function-field equivalence of the given scheme isomorphism,
built from its actual map on the generic stalk. -/
def schemeIsoFunctionFieldRingEquiv : Y.functionField ≃+* X.functionField :=
  (openImmersionFunctionFieldIso e.hom).commRingCatIsoToRingEquiv

/-- The function-field equivalence respects actual pullbacks of global
regular functions. -/
theorem schemeIsoFunctionFieldRingEquiv_germ (s : Γ(Y, ⊤)) :
    schemeIsoFunctionFieldRingEquiv e (Y.germToFunctionField ⊤ s) =
      X.germToFunctionField ⊤ (e.hom.appTop s) := by
  letI : Nonempty (e.hom ⁻¹ᵁ (⊤ : Y.Opens)) := ⟨⟨genericPoint X, trivial⟩⟩
  exact openImmersionFunctionFieldIso_germ_apply e.hom ⊤ s

/-- Compatibility with constants is proved from the commuting triangle of
actual scheme morphisms. -/
theorem schemeIsoFunctionFieldRingEquiv_baseScalar {K : Type u} [Field K]
    (pX : X ⟶ Spec (CommRingCat.of K))
    (pY : Y ⟶ Spec (CommRingCat.of K)) (h : e.hom ≫ pY = pX) (r : K) :
    schemeIsoFunctionFieldRingEquiv e
        (Y.germToFunctionField ⊤ (schemeBaseScalarHom pY r)) =
      X.germToFunctionField ⊤ (schemeBaseScalarHom pX r) := by
  rw [schemeIsoFunctionFieldRingEquiv_germ]
  subst pX
  rfl

open scoped SchemeScalars

variable {K : Type u} [Field K]
    [X.Over (Spec (CommRingCat.of K))] [Y.Over (Spec (CommRingCat.of K))]
    [e.hom.IsOver (Spec (CommRingCat.of K))]

/-- An actual isomorphism of `K`-schemes induces a `K`-algebra equivalence
of their actual function fields.  Both scalar actions are the scoped
`SchemeScalars` actions induced by the given structure morphisms. -/
def schemeIsoFunctionFieldAlgEquiv : Y.functionField ≃ₐ[K] X.functionField where
  __ := schemeIsoFunctionFieldRingEquiv e
  commutes' r :=
    schemeIsoFunctionFieldRingEquiv_baseScalar e
      (X ↘ Spec (CommRingCat.of K)) (Y ↘ Spec (CommRingCat.of K))
      (comp_over e.hom (Spec (CommRingCat.of K))) r

/-- The underlying field map of the algebra equivalence remains the actual
generic-stalk map constructed above. -/
theorem schemeIsoFunctionFieldAlgEquiv_toRingEquiv :
    (schemeIsoFunctionFieldAlgEquiv (K := K) e).toRingEquiv =
      schemeIsoFunctionFieldRingEquiv e := rfl

end Iso

section Affine

variable (R : CommRingCat.{u}) [IsDomain R]

local instance : Nonempty (⊤ : (Spec R).Opens) :=
  ⟨⟨genericPoint (Spec R), trivial⟩⟩

/-- The standard affine algebra map into the function field is the generic
germ of the corresponding global section. -/
theorem affineFunctionField_algebraMap (r : R) :
    algebraMap R (Spec R).functionField r =
      (Spec R).germToFunctionField ⊤ ((Scheme.ΓSpecIso R).inv r) := rfl

/-- Constants pulled back along an actual affine structure morphism have
exactly the usual value in the affine function field.  This compares the
scheme-induced scalar action with the coordinate-ring-induced action. -/
theorem affineFunctionField_germ_baseScalar {K : Type u} [Field K]
    (f : K →+* R) (r : K) :
    (Spec R).germToFunctionField ⊤
        (schemeBaseScalarHom (Spec.map (CommRingCat.ofHom f)) r) =
      algebraMap R (Spec R).functionField (f r) := by
  rw [affineFunctionField_algebraMap]
  apply congrArg ((Spec R).germToFunctionField ⊤)
  exact DFunLike.congr_fun
    (CommRingCat.hom_ext_iff.mp
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f)).symm) r

end Affine

end EvenQuinticConic
