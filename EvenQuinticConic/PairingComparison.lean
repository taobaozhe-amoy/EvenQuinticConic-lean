import EvenQuinticConic.ModulePairing
import EvenQuinticConic.FrameComparison

/-!
# From an actual global square-pairing identity to a sheaf isomorphism

Local unit weights are derived from the actual pairings and their local
tensor maps. Local comparison maps, overlap compatibility, and the global
isomorphism are then constructed by the preceding sheaf theorems.
-/

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace EvenQuinticConic

variable (X : Scheme.{u}) [IsIntegral X] {M N P : X.Modules}

/-- On an integral scheme with a normal affine framed cover, a global
square-pairing identity with unit scalar and nonzero source section produces
an actual isomorphism of module sheaves carrying that section to the target.
The local weights and local comparison morphisms are conclusions of the
proof; they are not input assumptions. -/
theorem exists_moduleSheafIso_of_pairing_square_eq
    (μ : ModuleSheafPairing M M P) (ν : ModuleSheafPairing N N P)
    {ι : Type*} (U : ι → X.Opens) [∀ i, Nonempty (U i)]
    (hcover : iSup U = ⊤) (hU : ∀ i, IsAffineOpen (U i))
    [∀ i, IsIntegrallyClosed Γ(X, U i)]
    (m : ∀ i, ModuleSheafFrame M (U i))
    (n : ∀ i, ModuleSheafFrame N (U i))
    (p : ∀ i, ModuleSheafFrame P (U i))
    (s : M.val.obj (op ⊤)) (a : N.val.obj (op ⊤)) (ha : a ≠ 0)
    (c : Γ(X, ⊤)ˣ)
    (h : μ.app ⊤ s s = (c : Γ(X, ⊤)) • ν.app ⊤ a a)
    (hμ : ∀ i, Function.Bijective (TensorProduct.lift (μ.app (U i))))
    (hν : ∀ i, Function.Bijective (TensorProduct.lift (ν.app (U i)))) :
    ∃ e : N ≅ M, e.hom.val.app (op ⊤) a = s := by
  choose w z hw using fun i => exists_local_unit_weights_of_pairing_square_eq
    μ ν s a c h (U i) (m i) (n i) (p i) (hμ i) (hν i)
  exact exists_moduleSheafIso_of_frame_square_relation X U hcover hU m n
    s a ha w z hw

end EvenQuinticConic
