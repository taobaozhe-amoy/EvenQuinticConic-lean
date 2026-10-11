import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-!
# The actual sheaf of relative differentials over a base ring

For a scheme morphism `f : X ⟶ Spec K`, constants are pulled back using
`ΓSpecIso`, `f.appTop`, and restriction of regular functions.  Applying the
objectwise module of Kähler differentials to this natural transformation,
then sheafifying, defines `schemeKaehlerSheaf f`.

Its universal property is proved for derivations into actual sheaves of
modules.  No identification of its sections with ring differentials on
arbitrary opens is assumed; such an identification requires an additional
affine comparison theorem.
-/

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace EvenQuinticConic

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {K : Type u} [CommRing K] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of K))

/-- The natural map from the constant base-ring presheaf to the actual
structure presheaf, induced by the given scheme morphism. -/
noncomputable def schemeConstantsPresheafHom :
    (Functor.const X.Opensᵒᵖ).obj (CommRingCat.of K) ⟶ X.presheaf where
  app U := (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appTop ≫
    X.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op
  naturality {U V} i := by
    simp only [Functor.const_obj_map, Category.assoc,
      ← Functor.map_comp]
    rfl

/-- On every open, the constant map is the restriction of the actual
pullback of a base-ring element. -/
theorem schemeConstantsPresheafHom_app (U : X.Opens) (a : K) :
    (schemeConstantsPresheafHom f).app (op U) a =
      X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op
        (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv a)) := rfl

/-- For an actual affine morphism, the base constants are the corresponding
constant regular functions. -/
theorem schemeConstantsPresheafHom_specMap {A : Type u} [CommRing A]
    (g : K →+* A) (U : Opens (PrimeSpectrum A)) :
    (schemeConstantsPresheafHom (Spec.map (CommRingCat.ofHom g))).app (op U) =
      CommRingCat.ofHom g ≫ StructureSheaf.toOpen A U := by
  change (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
    (Spec.map (CommRingCat.ofHom g)).appTop ≫ _ = _
  rw [← Scheme.ΓSpecIso_inv_naturality_assoc]
  rfl

/-- The actual presheaf of relative Kähler differentials of regular functions. -/
noncomputable def schemeKaehlerPresheaf : X.PresheafOfModules :=
  PresheafOfModules.DifferentialsConstruction.relativeDifferentials'
    (schemeConstantsPresheafHom f)

/-- Before sheafification, evaluation is the genuine module of ring
differentials for the actual pullback of constants. -/
theorem schemeKaehlerPresheaf_obj (U : X.Opensᵒᵖ) :
    (schemeKaehlerPresheaf f).obj U =
      CommRingCat.KaehlerDifferential ((schemeConstantsPresheafHom f).app U) := rfl

/-- The relative differential sheaf, obtained by sheafifying the genuine
presheaf of ring differentials. -/
noncomputable def schemeKaehlerSheaf : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)).obj
    (schemeKaehlerPresheaf f)

/-- The actual sheafification map from ring differentials to the differential sheaf. -/
noncomputable def schemeKaehlerSheafificationMap :
    schemeKaehlerPresheaf f ⟶ (schemeKaehlerSheaf f).val :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.val)).unit.app
    (schemeKaehlerPresheaf f)

/-- The universal differential sends a regular function to its differential
in the actual sheafification. -/
noncomputable def schemeKaehlerDerivation :
    (schemeKaehlerSheaf f).val.Derivation' (schemeConstantsPresheafHom f) :=
  (PresheafOfModules.DifferentialsConstruction.derivation'
    (schemeConstantsPresheafHom f)).postcomp (schemeKaehlerSheafificationMap f)

/-- The differential on an open is the sheafification image of the ring differential. -/
theorem schemeKaehlerDerivation_apply (U : X.Opensᵒᵖ) (s : X.presheaf.obj U) :
    (schemeKaehlerDerivation f).d s =
      (schemeKaehlerSheafificationMap f).app U
        (CommRingCat.KaehlerDifferential.d s) := rfl

/-- The sheaf differential satisfies the Leibniz rule on every open. -/
theorem schemeKaehlerDerivation_mul (U : X.Opensᵒᵖ) (s t : X.presheaf.obj U) :
    (schemeKaehlerDerivation f).d (s * t) =
      s • (schemeKaehlerDerivation f).d t + t • (schemeKaehlerDerivation f).d s :=
  (schemeKaehlerDerivation f).d_mul s t

/-- The differential commutes with actual restriction of regular functions. -/
theorem schemeKaehlerDerivation_restrict {U V : X.Opensᵒᵖ}
    (i : U ⟶ V) (s : X.presheaf.obj U) :
    (schemeKaehlerDerivation f).d (X.presheaf.map i s) =
      (schemeKaehlerSheaf f).val.map i ((schemeKaehlerDerivation f).d s) :=
  (schemeKaehlerDerivation f).d_map i s

/-- Pullbacks of constants have zero relative differential on every open. -/
theorem schemeKaehlerDerivation_constant (U : X.Opensᵒᵖ) (a : K) :
    (schemeKaehlerDerivation f).d ((schemeConstantsPresheafHom f).app U a) = 0 :=
  PresheafOfModules.Derivation'.d_app (schemeKaehlerDerivation f) a

/-- The universal property of the actual differential sheaf: maps to a module
sheaf are equivalent to relative derivations into its underlying presheaf. -/
noncomputable def schemeKaehlerHomEquiv (N : X.Modules) :
    (schemeKaehlerSheaf f ⟶ N) ≃
      N.val.Derivation' (schemeConstantsPresheafHom f) where
  toFun g :=
    (PresheafOfModules.DifferentialsConstruction.derivation'
      (schemeConstantsPresheafHom f)).postcomp
        ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.val)).homEquiv
          (schemeKaehlerPresheaf f) N g)
  invFun d :=
    ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.val)).homEquiv
      (schemeKaehlerPresheaf f) N).symm
        ((PresheafOfModules.DifferentialsConstruction.isUniversal'
          (schemeConstantsPresheafHom f)).desc d)
  left_inv g := by
    apply ((PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.val)).homEquiv (schemeKaehlerPresheaf f) N).injective
    rw [Equiv.apply_symm_apply]
    apply (PresheafOfModules.DifferentialsConstruction.isUniversal'
      (schemeConstantsPresheafHom f)).postcomp_injective
    exact (PresheafOfModules.DifferentialsConstruction.isUniversal'
      (schemeConstantsPresheafHom f)).fac _
  right_inv d := by
    dsimp only
    rw [Equiv.apply_symm_apply]
    exact (PresheafOfModules.DifferentialsConstruction.isUniversal'
      (schemeConstantsPresheafHom f)).fac d

/-- The universal equivalence acts by postcomposing the genuine differential. -/
theorem schemeKaehlerHomEquiv_apply (N : X.Modules) (g : schemeKaehlerSheaf f ⟶ N) :
    schemeKaehlerHomEquiv f N g = (schemeKaehlerDerivation f).postcomp g.val := by
  change (PresheafOfModules.DifferentialsConstruction.derivation'
    (schemeConstantsPresheafHom f)).postcomp
      ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.val)).homEquiv
        (schemeKaehlerPresheaf f) N g) = _
  rw [Adjunction.homEquiv_unit]
  rfl

/-- The unique sheaf morphism induced by a sheaf-valued relative derivation. -/
noncomputable def schemeKaehlerDesc (N : X.Modules)
    (d : N.val.Derivation' (schemeConstantsPresheafHom f)) :
    schemeKaehlerSheaf f ⟶ N :=
  (schemeKaehlerHomEquiv f N).symm d

/-- The descended map sends the differential of every regular function to
its prescribed derivative. -/
theorem schemeKaehlerDesc_apply (N : X.Modules)
    (d : N.val.Derivation' (schemeConstantsPresheafHom f))
    (U : X.Opensᵒᵖ) (s : X.presheaf.obj U) :
    (schemeKaehlerDesc f N d).val.app U ((schemeKaehlerDerivation f).d s) = d.d s := by
  have h : (schemeKaehlerDerivation f).postcomp (schemeKaehlerDesc f N d).val = d := by
    rw [← schemeKaehlerHomEquiv_apply]
    exact (schemeKaehlerHomEquiv f N).apply_symm_apply d
  exact PresheafOfModules.Derivation.congr_d h s

/-- The universal correspondence is natural under maps of target sheaves. -/
theorem schemeKaehlerHomEquiv_comp (M N : X.Modules)
    (g : schemeKaehlerSheaf f ⟶ M) (h : M ⟶ N) :
    schemeKaehlerHomEquiv f N (g ≫ h) =
      (schemeKaehlerHomEquiv f M g).postcomp h.val := by
  rw [schemeKaehlerHomEquiv_apply, schemeKaehlerHomEquiv_apply]
  rfl

/-- Every sheaf-valued derivation descends to exactly one sheaf morphism. -/
theorem schemeKaehlerDerivation_existsUnique (N : X.Modules)
    (d : N.val.Derivation' (schemeConstantsPresheafHom f)) :
    ∃! g : schemeKaehlerSheaf f ⟶ N, (schemeKaehlerDerivation f).postcomp g.val = d := by
  refine ⟨(schemeKaehlerHomEquiv f N).symm d, ?_, ?_⟩
  · dsimp only
    rw [← schemeKaehlerHomEquiv_apply, Equiv.apply_symm_apply]
  · intro g hg
    apply (schemeKaehlerHomEquiv f N).injective
    rw [Equiv.apply_symm_apply, schemeKaehlerHomEquiv_apply]
    exact hg

/-- A map out of the actual differential sheaf is determined by its values
on the differentials of regular functions on all opens. -/
theorem schemeKaehlerSheaf_hom_ext (N : X.Modules)
    (g h : schemeKaehlerSheaf f ⟶ N)
    (heq : ∀ (U : X.Opensᵒᵖ) (s : X.presheaf.obj U),
      g.val.app U ((schemeKaehlerDerivation f).d s) =
        h.val.app U ((schemeKaehlerDerivation f).d s)) : g = h := by
  apply (schemeKaehlerHomEquiv f N).injective
  rw [schemeKaehlerHomEquiv_apply, schemeKaehlerHomEquiv_apply]
  ext U s
  exact heq U s

end EvenQuinticConic
