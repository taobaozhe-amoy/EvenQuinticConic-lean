import EvenQuinticConic.SchemePushforwardKummerAtlas
import EvenQuinticConic.AffinePushforwardKummerAtlas

/-! # Chart independence of the actual pushforward trace -/
noncomputable section
set_option maxRecDepth 2048
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
universe u
namespace EvenQuinticConic

/-- The previously constructed affine ring models supply multiplicative
charts in the general scheme interface, with no additional chart hypotheses. -/
def affinePushforwardRingChart {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    {f : R} (u : (Localization.Away f)ˣ)
    (e : Localization.Away f ⊗[R] A ≃ₐ[Localization.Away f]
      KummerAlgebra (u : Localization.Away f)) :
    PushforwardKummerChart (Spec.map (CommRingCat.ofHom (algebraMap R A)))
      (PrimeSpectrum.basicOpen f) (Units.map (StructureSheaf.toBasicOpen R f).toMonoidHom u) where
  coordinate V hV := affinePushforwardKummerRingModel e V hV
  coefficient V hV := affinePushforwardKummerRingModel_coefficient e V hV
  re_restrict V W hV hW hWV := affinePushforwardKummerRingModel_re_restrict e V hV W hW hWV
  im_restrict V W hV hW hWV := affinePushforwardKummerRingModel_im_restrict e V hV W hW hWV

variable {X Y : Scheme.{u}} {f : X ⟶ Y} {ι : Type u}
    (U : ι → Y.Opens) (u : ∀ i, Γ(Y, U i)ˣ)
    (c : ∀ i, PushforwardKummerChart f (U i) (u i)) (hcover : iSup U = ⊤)

/-- The global trace also agrees with any other multiplicative chart of the
same morphism, even if that chart was not part of the chosen cover. -/
theorem pushforwardKummerAtlas_trace_on_chart {W : Y.Opens} {w : Γ(Y, W)ˣ}
    (d : PushforwardKummerChart f W w) (V : Y.Opens) (hV : V ≤ W)
    (s : (schemePushforwardStructureModule f).val.obj (op V)) :
    ((pushforwardKummerAtlas U u c).trace hcover).val.app (op V) s =
      Algebra.trace Γ(Y, V) _ (d.coordinate V hV s) := by
  let a := pushforwardKummerAtlas U u c
  apply module_eq_of_cover_restrictions U hcover V
  intro i
  trans (a.trace hcover).val.app (op (V ⊓ U i))
    (moduleRestrict (schemePushforwardStructureModule f) inf_le_left s)
  · exact (PresheafOfModules.naturality_apply (a.trace hcover).val
      (homOfLE (show V ⊓ U i ≤ V from inf_le_left)).op s).symm
  rw [a.trace_apply hcover i (V ⊓ U i) inf_le_right]
  change Algebra.trace Γ(Y, V ⊓ U i) _
    ((c i).coordinate (V ⊓ U i) inf_le_right
      (X.presheaf.map ((Opens.map f.base).map (homOfLE inf_le_left)).op s)) =
    Y.presheaf.map (homOfLE inf_le_left).op (Algebra.trace Γ(Y, V) _ (d.coordinate V hV s))
  rw [(c i).trace_coordinate_eq d (V ⊓ U i) inf_le_right (inf_le_left.trans hV),
    kummer_trace, kummer_trace, d.re_restrict V (V ⊓ U i) hV
      (inf_le_left.trans hV) inf_le_left]
  simp only [map_mul, map_ofNat]

/-- Two covering families of actual algebra charts give the same global
module-sheaf trace, without a compatibility hypothesis between the families. -/
theorem pushforwardKummerAtlas_trace_independent {κ : Type u}
    (W : κ → Y.Opens) (w : ∀ j, Γ(Y, W j)ˣ)
    (d : ∀ j, PushforwardKummerChart f (W j) (w j)) (hW : iSup W = ⊤) :
    (pushforwardKummerAtlas U u c).trace hcover =
      (pushforwardKummerAtlas W w d).trace hW := by
  apply SheafOfModules.hom_ext
  ext V s
  apply module_eq_of_cover_restrictions W hW V.unop
  intro j
  trans ((pushforwardKummerAtlas U u c).trace hcover).val.app (op (V.unop ⊓ W j))
    (moduleRestrict (schemePushforwardStructureModule f) inf_le_left s)
  · exact (PresheafOfModules.naturality_apply
      ((pushforwardKummerAtlas U u c).trace hcover).val
      (homOfLE (show V.unop ⊓ W j ≤ V.unop from inf_le_left)).op s).symm
  trans ((pushforwardKummerAtlas W w d).trace hW).val.app (op (V.unop ⊓ W j))
    (moduleRestrict (schemePushforwardStructureModule f) inf_le_left s)
  · exact (pushforwardKummerAtlas_trace_on_chart U u c hcover (d j)
      (V.unop ⊓ W j) inf_le_right _).trans
        ((pushforwardKummerAtlas W w d).trace_apply hW j
          (V.unop ⊓ W j) inf_le_right _).symm
  exact PresheafOfModules.naturality_apply
    ((pushforwardKummerAtlas W w d).trace hW).val
    (homOfLE (show V.unop ⊓ W j ≤ V.unop from inf_le_left)).op s

end EvenQuinticConic
