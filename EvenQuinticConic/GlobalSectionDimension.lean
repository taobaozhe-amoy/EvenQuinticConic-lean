import EvenQuinticConic.SchemeScalarAction
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# Dimension and independence of actual global sections

An isomorphism of actual module sheaves on an actual `K`-scheme induces a
`K`-linear equivalence on global sections.  In particular their finite ranks
agree. The base-field scalar structures are constructed from the scheme's
structure morphism, using `SchemeScalars`.

A second theorem extracts two independent actual global sections from a
lower bound of two on the finite rank. No unspecified section space or
propositional replacement for the geometric objects is introduced.
-/

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open scoped EvenQuinticConic.SchemeScalars

universe u

namespace EvenQuinticConic

variable {K : Type u} [Field K] {X : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of K))] {M N : X.Modules}

/-- An actual sheaf isomorphism gives a canonical base-field-linear
equivalence on the actual modules of global sections. -/
noncomputable def schemeGlobalSectionLinearEquiv (e : M ≅ N) :
    M.val.obj (op ⊤) ≃ₗ[K] N.val.obj (op ⊤) := by
  let eΓ : M.val.obj (op ⊤) ≃ₗ[Γ(X, ⊤)] N.val.obj (op ⊤) :=
    ((SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).mapIso e).toLinearEquiv
  exact eΓ.restrictScalars K

/-- The induced equivalence acts by the given sheaf morphism on global
sections; no choice of basis or auxiliary vector space is involved. -/
@[simp]
theorem schemeGlobalSectionLinearEquiv_apply (e : M ≅ N)
    (s : M.val.obj (op ⊤)) :
    schemeGlobalSectionLinearEquiv (K := K) e s = e.hom.val.app (op ⊤) s := rfl

/-- Actual isomorphic module sheaves have the same finite rank of global
sections over the base field. -/
theorem schemeGlobalSections_finrank_eq (e : M ≅ N) :
    Module.finrank K (M.val.obj (op ⊤)) = Module.finrank K (N.val.obj (op ⊤)) :=
  (schemeGlobalSectionLinearEquiv (K := K) e).finrank_eq

/-- A lower bound of two on the dimension supplies two independent actual
global sections. Finite-dimensionality is not a separate input: the positive
finite-rank bound already supplies the required finite independent family. -/
theorem exists_independent_global_sections_of_finrank_ge_two (M : X.Modules)
    (h : 2 ≤ Module.finrank K (M.val.obj (op ⊤))) :
    ∃ s t : M.val.obj (op ⊤), LinearIndependent K ![s, t] := by
  obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_finrank h
  refine ⟨v 0, v 1, ?_⟩
  convert hv using 1
  funext i
  fin_cases i <;> rfl

end EvenQuinticConic
