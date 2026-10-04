import EvenQuinticConic.ModuleGenericInjection
import Mathlib.AlgebraicGeometry.Over

/-!
# Base-field scalars induced by the actual structure morphism

For an actual scheme over `Spec K`, the structure morphism induces all scalar
structures needed for the generic-coefficient map.  The map `K → Γ(X, ⊤)`
is the composite of the actual `ΓSpecIso` and the actual pullback on global
functions.  The action on the function field then uses the actual generic
stalk map, and the action on global module sections is restriction of scalars.

The instances are scoped to `EvenQuinticConic.SchemeScalars`: downstream users
can opt in without changing unrelated algebra structures on the same rings.
No base-field actions or scalar-tower axioms are assumed in the final result.
-/

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace EvenQuinticConic

/-- Pullback of constants along an actual structure morphism to `Spec K`. -/
noncomputable def schemeBaseScalarHom
    {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of K)) : K →+* Γ(X, ⊤) :=
  f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom

namespace SchemeScalars

variable (K : Type u) [Field K] (X : Scheme.{u})
  [X.Over (Spec (CommRingCat.of K))]

/-- Constants act on global regular functions through the scheme's structure
morphism, rather than through a separately postulated algebra structure. -/
noncomputable scoped instance globalFunctionsAlgebra : Algebra K Γ(X, ⊤) :=
  (schemeBaseScalarHom (X ↘ Spec (CommRingCat.of K))).toAlgebra

/-- Restrict scalars along the actual pullback of constants to act on global
sections of an actual module sheaf. -/
noncomputable scoped instance globalSectionsModule (M : X.Modules) :
    Module K (M.val.obj (op ⊤)) :=
  Module.compHom _ (schemeBaseScalarHom (X ↘ Spec (CommRingCat.of K)))

scoped instance globalSectionsScalarTower (M : X.Modules) :
    IsScalarTower K Γ(X, ⊤) (M.val.obj (op ⊤)) := by
  apply IsScalarTower.of_algebraMap_smul
  intro r s
  rfl

variable [IsIntegral X]

local instance : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩

/-- The scalar map on the actual function field is obtained by taking the
generic germ of the pulled-back constant regular function. -/
noncomputable scoped instance functionFieldAlgebra : Algebra K X.functionField :=
  ((X.germToFunctionField ⊤).hom.comp
    (schemeBaseScalarHom (X ↘ Spec (CommRingCat.of K)))).toAlgebra

scoped instance functionFieldScalarTower :
    IsScalarTower K Γ(X, ⊤) X.functionField := by
  apply IsScalarTower.of_algebraMap_eq'
  rfl

/-- The induced scalar map is precisely the generic value of the pulled-back
constant; this records its connection to the actual structure morphism. -/
theorem algebraMap_functionField (r : K) :
    algebraMap K X.functionField r = X.germToFunctionField ⊤
      (schemeBaseScalarHom (X ↘ Spec (CommRingCat.of K)) r) := rfl

end SchemeScalars

open scoped SchemeScalars

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (CommRingCat.of K))] (M : X.Modules)

local instance : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩

/-- The generic coefficient map is canonically `K`-linear for an actual
`K`-scheme. No additional scalar-coherence hypotheses are inputs. -/
noncomputable def schemeGenericLinearMap
    (V : X.Opens) [Nonempty V] (frame : ModuleSheafFrame M V) :
    M.val.obj (op ⊤) →ₗ[K] X.functionField :=
  (moduleGlobalGenericLinearMap M V frame).restrictScalars K

/-- The canonical base-field-linear generic map is injective for a module
sheaf with coherent rank-one frames on an actual nonempty open cover. -/
theorem schemeGenericLinearMap_injective
    {ι : Type*} (U : ι → X.Opens) [∀ i, Nonempty (U i)]
    (hcover : iSup U = ⊤) (frames : ∀ i, ModuleSheafFrame M (U i))
    (V : X.Opens) [Nonempty V] (frame : ModuleSheafFrame M V) :
    Function.Injective (schemeGenericLinearMap (K := K) M V frame) :=
  moduleGlobalGenericLinearMap_injective M U hcover frames V frame

/-- Base-field independence of actual global sections is preserved under the
canonical generic-coefficient map of an actual scheme over `Spec K`.
All scalar structures are constructed from the structure morphism. -/
theorem scheme_generic_coefficients_linearIndependent
    {ι : Type*} (U : ι → X.Opens) [∀ i, Nonempty (U i)]
    (hcover : iSup U = ⊤) (frames : ∀ i, ModuleSheafFrame M (U i))
    (V : X.Opens) [Nonempty V] (frame : ModuleSheafFrame M V)
    {κ : Type*} (s : κ → M.val.obj (op ⊤)) (hs : LinearIndependent K s) :
    LinearIndependent K ((schemeGenericLinearMap (K := K) M V frame) ∘ s) :=
  hs.map_injOn (schemeGenericLinearMap (K := K) M V frame)
    (schemeGenericLinearMap_injective M U hcover frames V frame).injOn

end EvenQuinticConic
