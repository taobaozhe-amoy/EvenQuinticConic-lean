import EvenQuinticConic.AffinePushforwardKummerModel
import EvenQuinticConic.AffinePushforwardModule
import EvenQuinticConic.KummerModuleAtlas
import EvenQuinticConic.PrincipalOpenKummer

/-! # Actual Kummer atlases on affine pushforward module sheaves -/
noncomputable section
set_option maxRecDepth 2048
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
namespace EvenQuinticConic
universe v
variable {R A : Type v} [CommRing R] [CommRing A] [Algebra R A]

/-- Actual section ring coordinates are linear for the genuine pushforward action. -/
def affinePushforwardKummerCoordinate {f : R} {u : Localization.Away f}
    (e : Localization.Away f ⊗[R] A ≃ₐ[Localization.Away f] KummerAlgebra u)
    (V : Opens (PrimeSpectrum.Top R)) (hV : V ≤ PrimeSpectrum.basicOpen f) :
    (affinePushforwardModule (R := R) (A := A)).val.obj (op V) ≃ₗ[(Spec.structureSheaf R).val.obj (op V)]
      KummerAlgebra (principalOpenSectionMap f V hV u) where
  __ := (affinePushforwardKummerRingModel e V hV).toAddEquiv
  map_smul' r s := by
    change affinePushforwardKummerRingModel e V hV
      (affinePushforwardCoefficientMap (A := A) V r *
        (show (Spec.structureSheaf A).val.obj (op (affinePushforwardOpen (A := A) V)) from s)) =
      r • affinePushforwardKummerRingModel e V hV s
    rw [map_mul, affinePushforwardKummerRingModel_coefficient, Algebra.smul_def]

/-- A principal algebra model supplies a coherent chart on the actual pushforward module. -/
def affinePushforwardKummerChart {f : R} (u : (Localization.Away f)ˣ)
    (e : Localization.Away f ⊗[R] A ≃ₐ[Localization.Away f] KummerAlgebra (u : Localization.Away f)) :
    KummerModuleChart (affinePushforwardModule (R := R) (A := A))
      (PrimeSpectrum.basicOpen f) (Units.map (StructureSheaf.toBasicOpen R f).toMonoidHom u) where
  coordinate V hV := affinePushforwardKummerCoordinate e V hV
  re_restrict V W hV hW hWV s := affinePushforwardKummerRingModel_re_restrict e V hV W hW hWV s
  im_restrict V W hV hW hWV s := affinePushforwardKummerRingModel_im_restrict e V hV W hW hWV s

/-- Overlap comparisons are algebra maps because both actual section models preserve scalars. -/
def affinePushforwardKummerOverlap {f g : R} {u : Localization.Away f} {w : Localization.Away g}
    (ei : Localization.Away f ⊗[R] A ≃ₐ[Localization.Away f] KummerAlgebra u)
    (ej : Localization.Away g ⊗[R] A ≃ₐ[Localization.Away g] KummerAlgebra w)
    (V : Opens (PrimeSpectrum.Top R)) (hi : V ≤ PrimeSpectrum.basicOpen f)
    (hj : V ≤ PrimeSpectrum.basicOpen g) :
    KummerAlgebra (principalOpenSectionMap g V hj w) ≃ₐ[(Spec.structureSheaf R).val.obj (op V)]
      KummerAlgebra (principalOpenSectionMap f V hi u) where
  __ := (affinePushforwardKummerRingModel ej V hj).symm.trans
    (affinePushforwardKummerRingModel ei V hi)
  commutes' r := by
    change affinePushforwardKummerRingModel ei V hi
      ((affinePushforwardKummerRingModel ej V hj).symm (algebraMap _ _ r)) = _
    have h : (affinePushforwardKummerRingModel ej V hj).symm (algebraMap _ _ r) =
        affinePushforwardCoefficientMap (A := A) V r := by
      apply (affinePushforwardKummerRingModel ej V hj).injective
      rw [RingEquiv.apply_symm_apply, affinePushforwardKummerRingModel_coefficient]
    rw [h, affinePushforwardKummerRingModel_coefficient]

/-- A family of principal algebra models builds the actual module-sheaf atlas. -/
def affinePushforwardKummerAtlas {ι : Type v} (f : ι → R)
    (u : ∀ i, (Localization.Away (f i))ˣ)
    (e : ∀ i, Localization.Away (f i) ⊗[R] A ≃ₐ[Localization.Away (f i)]
      KummerAlgebra (u i : Localization.Away (f i))) :
    KummerModuleAtlas (affinePushforwardModule (R := R) (A := A))
      (fun i => PrimeSpectrum.basicOpen (f i)) where
  parameter i := Units.map (StructureSheaf.toBasicOpen R (f i)).toMonoidHom (u i)
  chart i := affinePushforwardKummerChart (u i) (e i)
  overlap i j V hi hj := affinePushforwardKummerOverlap (e i) (e j) V hi hj
  overlap_coordinate i j V hi hj s :=
    (affinePushforwardKummerRingModel (e j) V hj).symm_apply_apply s |>
      congrArg (affinePushforwardKummerRingModel (e i) V hi)

/-- Finite presentation, flatness, formal unramifiedness and pointwise rank two
construct a covering Kummer atlas on the actual affine pushforward sheaf. -/
theorem exists_affinePushforwardKummerAtlas
    [Module.FinitePresentation R A] [Module.Flat R A] [Invertible (2 : R)]
    [Algebra.FormallyUnramified R A]
    (hrank : ∀ p : PrimeSpectrum R, Module.finrank (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime p.asIdeal ⊗[R] A) = 2) :
    ∃ f : PrimeSpectrum R → R,
      (⨆ p, PrimeSpectrum.basicOpen (f p)) = ⊤ ∧
      Nonempty (KummerModuleAtlas (affinePushforwardModule (R := R) (A := A))
        (fun p => PrimeSpectrum.basicOpen (f p))) := by
  classical
  obtain ⟨f, hf, hmodels⟩ := exists_principal_unit_kummer_cover hrank
  choose u e using hmodels
  exact ⟨f, hf, ⟨affinePushforwardKummerAtlas f u (fun p => Classical.choice (e p))⟩⟩

end EvenQuinticConic
