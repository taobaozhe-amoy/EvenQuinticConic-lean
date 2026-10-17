import EvenQuinticConic.NetIncidenceNonempty
import EvenQuinticConic.ProjectiveThreeChartRing
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-!
# An actual incidence chart over projective three-space

The coefficient ring here is the degree-zero homogeneous localization of
`K[y₀,y₁,y₂,y₃]` at an actual projective coordinate.  The linear and quadratic
rows are divided by that coordinate to powers one and two, respectively.
The quotient by the two incidence equations over a nonzero minor is shown
to be isomorphic to an actual open subscheme of `Proj K[y₀,y₁,y₂,y₃]`.
This does not yet construct or compare the global projective incidence scheme.
-/

noncomputable section

open MvPolynomial AlgebraicGeometry CategoryTheory

namespace EvenQuinticConic.Incidence

variable {K : Type*} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual projective three-space scheme with its standard grading. -/
def ProjectiveThreeScheme (K : Type*) [Field K] : Scheme :=
  Proj (homogeneousSubmodule (Fin 4) K)

/-- The actual degree-zero localization for a standard projective chart. -/
abbrev ProjectiveThreeChartRing (p : Fin 4) :=
  HomogeneousLocalization.Away (homogeneousSubmodule (Fin 4) K) (X p)

/-- A standard open in the actual projective scheme is the spectrum of a
polynomial ring in exactly three variables. The coordinate-ring isomorphism
is constructed from actual homogeneous fractions. -/
def projectiveThreeStandardChartIsoAffine (p : Fin 4) :
    (Proj.basicOpen (homogeneousSubmodule (Fin 4) K) (X p)).toScheme ≅
      Spec (CommRingCat.of (MvPolynomial (Fin 3) K)) :=
  Proj.basicOpenIsoSpec (homogeneousSubmodule (Fin 4) K) (X p)
      (isHomogeneous_X K p) (by decide) ≪≫
    Scheme.Spec.mapIso (projectiveThreeChartRingEquiv (K := K) p).symm.toCommRingCatIso.op

/-- A homogeneous polynomial, divided by the corresponding coordinate power. -/
def projectiveThreeFraction (p : Fin 4) (d : ℕ) (F : MvPolynomial (Fin 4) K)
    (hF : F.IsHomogeneous d) : ProjectiveThreeChartRing (K := K) p :=
  HomogeneousLocalization.Away.mk _ (isHomogeneous_X K p) d F (by simpa using hF)

/-- Evaluation of actual homogeneous chart fractions at a nonzero chart coordinate. -/
def projectiveThreeChartEval (p : Fin 4) (y : Fin 4 → K) (hy : y p ≠ 0) :
    ProjectiveThreeChartRing (K := K) p →+* K :=
  (Localization.awayLift (eval y) (X p)
    (isUnit_iff_exists_inv.mpr ⟨(y p)⁻¹, by simp [hy]⟩)).comp
    (algebraMap (ProjectiveThreeChartRing (K := K) p)
      (Localization.Away (X p : MvPolynomial (Fin 4) K)))

/-- The actual fraction evaluation is the expected normalized polynomial value. -/
theorem projectiveThreeChartEval_fraction (p : Fin 4) (y : Fin 4 → K) (hy : y p ≠ 0)
    (d : ℕ) (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous d) :
    projectiveThreeChartEval p y hy (projectiveThreeFraction p d F hF) =
      eval y F * (y p)⁻¹ ^ d := by
  change Localization.awayLift (eval y) (X p)
      (isUnit_iff_exists_inv.mpr ⟨(y p)⁻¹, by simp [hy]⟩)
      (Localization.mk F ⟨(X p)^d, d, rfl⟩) = _
  exact Localization.awayLift_mk _ _ _ _ (by simp [hy]) _

/-- The extracted polar row is genuinely homogeneous of degree one. -/
theorem projectiveNetLinear_homogeneous (M : Fin 3 → Matrix (Fin 5) (Fin 5) K)
    (i : Fin 3) : (netLinearRow M i).IsHomogeneous 1 :=
  coefficientLinearPolynomial_homogeneous _

/-- The extracted quadratic row is genuinely homogeneous of degree two. -/
theorem projectiveNetQuadratic_homogeneous (M : Fin 3 → Matrix (Fin 5) (Fin 5) K)
    (i : Fin 3) : (netQuadraticRow M i).IsHomogeneous 2 := by
  unfold netQuadraticRow matrixQuadraticPolynomial
  apply IsHomogeneous.sum
  intro j _
  apply IsHomogeneous.sum
  intro k _
  exact (isHomogeneous_C_mul_X _ _).mul (isHomogeneous_X K k)

/-- The actual linear incidence coefficients on a projective coordinate chart. -/
def projectiveNetLinearRow (M : Fin 3 → Matrix (Fin 5) (Fin 5) K)
    (p : Fin 4) (i j k : Fin 3) : Vec3 (ProjectiveThreeChartRing (K := K) p) :=
  ⟨projectiveThreeFraction p 1 (netLinearRow M i) (projectiveNetLinear_homogeneous M i),
   projectiveThreeFraction p 1 (netLinearRow M j) (projectiveNetLinear_homogeneous M j),
   projectiveThreeFraction p 1 (netLinearRow M k) (projectiveNetLinear_homogeneous M k)⟩

/-- The actual quadratic incidence coefficients on the same projective chart. -/
def projectiveNetQuadraticRow (M : Fin 3 → Matrix (Fin 5) (Fin 5) K)
    (p : Fin 4) (i j k : Fin 3) : Vec3 (ProjectiveThreeChartRing (K := K) p) :=
  ⟨projectiveThreeFraction p 2 (netQuadraticRow M i) (projectiveNetQuadratic_homogeneous M i),
   projectiveThreeFraction p 2 (netQuadraticRow M j) (projectiveNetQuadratic_homogeneous M j),
   projectiveThreeFraction p 2 (netQuadraticRow M k) (projectiveNetQuadratic_homogeneous M k)⟩

/-- The original minor has the correct homogeneous degree for a projective open. -/
theorem projectiveNetMinor_homogeneous (M : Fin 3 → Matrix (Fin 5) (Fin 5) K)
    (i j : Fin 3) : (netIncidenceMinor M i j).IsHomogeneous 3 :=
  ((projectiveNetLinear_homogeneous M i).mul
    (projectiveNetQuadratic_homogeneous M j)).sub
    ((projectiveNetLinear_homogeneous M j).mul (projectiveNetQuadratic_homogeneous M i))

/-- The actual minor element in the homogeneous chart ring is the cubic minor fraction. -/
theorem projectiveNetMinor_fraction (M : Fin 3 → Matrix (Fin 5) (Fin 5) K)
    (p : Fin 4) (i j k : Fin 3) :
    (cross (projectiveNetLinearRow M p i j k) (projectiveNetQuadraticRow M p i j k)).z =
      projectiveThreeFraction p 3 (netIncidenceMinor M i j)
        (projectiveNetMinor_homogeneous M i j) := by
  apply HomogeneousLocalization.val_injective
  simp only [cross, projectiveNetLinearRow, projectiveNetQuadraticRow,
    projectiveThreeFraction, HomogeneousLocalization.val_sub,
    HomogeneousLocalization.val_mul, HomogeneousLocalization.Away.val_mk,
    Localization.mk_mul, Localization.sub_mk]
  apply Localization.mk_eq_mk_iff.mpr
  rw [Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul, Submonoid.coe_mul, netIncidenceMinor]
  ring

/-- The minor on an actual projective chart is the original cubic minor divided by `yₚ³`. -/
theorem projectiveNetMinor_eval (M : Fin 3 → Matrix (Fin 5) (Fin 5) K)
    (p : Fin 4) (i j k : Fin 3) (y : Fin 4 → K) (hy : y p ≠ 0) :
    projectiveThreeChartEval p y hy
      (cross (projectiveNetLinearRow M p i j k) (projectiveNetQuadraticRow M p i j k)).z =
      eval y (netIncidenceMinor M i j) * (y p)⁻¹ ^ 3 := by
  simp only [cross, projectiveNetLinearRow, projectiveNetQuadraticRow,
    map_sub, map_mul, projectiveThreeChartEval_fraction, netIncidenceMinor]
  ring

/-- The genuine quotient scheme defined by the normalized incidence equations,
with the selected minor inverted in the actual projective chart ring. -/
def netProjectiveIncidenceChart (M : Fin 3 → Matrix (Fin 5) (Fin 5) K)
    (p : Fin 4) (i j k : Fin 3) : Scheme :=
  let a := projectiveNetLinearRow M p i j k
  let b := projectiveNetQuadraticRow M p i j k
  Spec (CommRingCat.of
    (AffineIncidenceAlgebra (localizedRow a b a) (localizedRow a b b)))

/-- Its projection, followed by the actual standard-chart inclusion into projective space. -/
def netProjectiveIncidenceToProjective (M : Fin 3 → Matrix (Fin 5) (Fin 5) K)
    (p : Fin 4) (i j k : Fin 3) :
    netProjectiveIncidenceChart M p i j k ⟶ ProjectiveThreeScheme K :=
  let a := projectiveNetLinearRow M p i j k
  let b := projectiveNetQuadraticRow M p i j k
  (localizedIncidenceBasicOpenIso a b).hom ≫
    (Scheme.Opens.ι (X := Spec (CommRingCat.of (ProjectiveThreeChartRing (K := K) p)))
      (PrimeSpectrum.basicOpen (cross a b).z)) ≫
    Proj.awayι (homogeneousSubmodule (Fin 4) K) (X p) (isHomogeneous_X K p) (by decide)

/-- Elimination identifies the actual incidence projection with an open immersion. -/
instance netProjectiveIncidenceToProjective_isOpenImmersion
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (p : Fin 4) (i j k : Fin 3) :
    IsOpenImmersion (netProjectiveIncidenceToProjective M p i j k) := by
  unfold netProjectiveIncidenceToProjective
  infer_instance

/-- The resulting actual open subset of projective three-space. -/
def netProjectiveIncidenceOpen (M : Fin 3 → Matrix (Fin 5) (Fin 5) K)
    (p : Fin 4) (i j k : Fin 3) : (ProjectiveThreeScheme K).Opens :=
  (netProjectiveIncidenceToProjective M p i j k).opensRange

/-- The image is precisely the simultaneous nonvanishing locus of the chosen
projective coordinate and the original cubic incidence minor. -/
theorem netProjectiveIncidenceOpen_eq (M : Fin 3 → Matrix (Fin 5) (Fin 5) K)
    (p : Fin 4) (i j k : Fin 3) :
    netProjectiveIncidenceOpen M p i j k =
      Proj.basicOpen (homogeneousSubmodule (Fin 4) K) (X p) ⊓
        Proj.basicOpen (homogeneousSubmodule (Fin 4) K) (netIncidenceMinor M i j) := by
  let ι := Proj.awayι (homogeneousSubmodule (Fin 4) K) (X p)
    (isHomogeneous_X K p) (by decide)
  have hpre : ι ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule (Fin 4) K)
      (netIncidenceMinor M i j) =
      PrimeSpectrum.basicOpen
        (cross (projectiveNetLinearRow M p i j k) (projectiveNetQuadraticRow M p i j k)).z := by
    rw [Proj.awayι_preimage_basicOpen _ _ _ (projectiveNetMinor_homogeneous M i j)
      (by decide : 0 < (3 : ℕ))]
    rw [projectiveNetMinor_fraction]
    congr 1
    simp only [HomogeneousLocalization.Away.isLocalizationElem, pow_one,
      projectiveThreeFraction]
  unfold netProjectiveIncidenceOpen netProjectiveIncidenceToProjective
  rw [Scheme.Hom.opensRange_comp_of_isIso, Scheme.Hom.opensRange_comp,
    Scheme.Opens.opensRange_ι]
  change ι ''ᵁ _ = _
  rw [← hpre, Scheme.Hom.image_preimage_eq_opensRange_inter,
    Proj.opensRange_awayι]

/-- The incidence chart is isomorphic to the actual open subscheme in projective space. -/
def netProjectiveIncidenceOpenIso (M : Fin 3 → Matrix (Fin 5) (Fin 5) K)
    (p : Fin 4) (i j k : Fin 3) :
    netProjectiveIncidenceChart M p i j k ≅ (netProjectiveIncidenceOpen M p i j k).toScheme :=
  IsOpenImmersion.isoOfRangeEq (netProjectiveIncidenceToProjective M p i j k)
    (netProjectiveIncidenceOpen M p i j k).ι (by
      rw [Scheme.Opens.range_ι]
      rfl)

/-- A nonzero minor value supplies a point of the actual projective incidence chart. -/
theorem netProjectiveIncidenceChart_nonempty_of_eval
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (p : Fin 4) (i j k : Fin 3)
    (y : Fin 4 → K) (hyp : y p ≠ 0) (hy : eval y (netIncidenceMinor M i j) ≠ 0) :
    Nonempty (netProjectiveIncidenceChart M p i j k) := by
  apply localizedIncidenceScheme_nonempty_of_eval (projectiveThreeChartEval p y hyp)
  rw [projectiveNetMinor_eval]
  exact mul_ne_zero hy (pow_ne_zero _ (inv_ne_zero hyp))

/-- A nonzero original minor makes the actual projective open nonempty. -/
theorem netProjectiveIncidenceOpen_nonempty_of_eval
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (p : Fin 4) (i j k : Fin 3)
    (y : Fin 4 → K) (hyp : y p ≠ 0) (hy : eval y (netIncidenceMinor M i j) ≠ 0) :
    Nonempty (netProjectiveIncidenceOpen M p i j k) := by
  obtain ⟨x⟩ := netProjectiveIncidenceChart_nonempty_of_eval M p i j k y hyp hy
  exact ⟨(netProjectiveIncidenceOpenIso M p i j k).hom.base x⟩

/-- An arbitrary common isotropic point and the actual determinant Jacobian
condition produce a nonempty actual projective open with the incidence chart
isomorphic to it. There is no supplied minor, coordinate normalization,
nonemptiness, or scheme isomorphism among the hypotheses. -/
theorem exists_nonempty_projectiveIncidenceOpen_of_common_point
    [Infinite K] (h2 : (2 : K) ≠ 0)
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (hM : ∀ i, (M i).IsSymm)
    (P : Fin 5 → K) (hP : P ≠ 0)
    (hisotropic : ∀ i, dotProduct P ((M i).mulVec P) = 0)
    (hsmooth : ∀ t : Fin 3 → K, t ≠ 0 → eval t (linearMatrixNet M).det = 0 →
      ∃ i, eval t (pderiv i (linearMatrixNet M).det) ≠ 0) :
    ∃ B : Matrix (Fin 5) (Fin 5) K, B.det ≠ 0 ∧ (∀ j, B j 0 = P j) ∧
      ∃ (p : Fin 4) (i j k : Fin 3), i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
        Nonempty (netProjectiveIncidenceOpen (matrixNetCongruence M B) p i j k) ∧
        Nonempty (netProjectiveIncidenceChart (matrixNetCongruence M B) p i j k ≅
          (netProjectiveIncidenceOpen (matrixNetCongruence M B) p i j k).toScheme) := by
  obtain ⟨B, hB, hcol, i, j, y, hij, hy0, hy⟩ :=
    exists_projective_netIncidenceMinor_after_common_point_normalization
      h2 M hM P hP hisotropic hsmooth
  have hp : ∃ p, y p ≠ 0 := by
    by_contra! h
    exact hy0 (funext h)
  obtain ⟨p, hyp⟩ := hp
  have hk : ∃ k : Fin 3, i ≠ k ∧ j ≠ k := by
    fin_cases i <;> fin_cases j <;> first | exact (hij rfl).elim | decide
  obtain ⟨k, hik, hjk⟩ := hk
  exact ⟨B, hB, hcol, p, i, j, k, hij, hik, hjk,
    netProjectiveIncidenceOpen_nonempty_of_eval (matrixNetCongruence M B) p i j k y hyp hy,
    ⟨netProjectiveIncidenceOpenIso (matrixNetCongruence M B) p i j k⟩⟩

private theorem affineOpenSpecProjection (R : CommRingCat) (U : (Spec R).Opens)
    (hU : IsAffineOpen U) :
    hU.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R Γ(Spec R, U))) = U.ι := by
  change U.toSpecΓ ≫ Spec.map
    ((Scheme.ΓSpecIso R).inv ≫ (Spec R).presheaf.map (homOfLE le_top).op) = _
  rw [Spec.map_comp, ← Category.assoc, Scheme.Opens.toSpecΓ_SpecMap_map,
    Scheme.Opens.toSpecΓ_top]
  simp only [Category.assoc, ← SpecMap_ΓSpecIso_hom, ← Spec.map_comp,
    Iso.inv_hom_id, Spec.map_id, Category.comp_id, Scheme.homOfLE_ι]

/-- The localization-to-basic-open isomorphism followed by inclusion is the
canonical spectrum map of the base-to-localization homomorphism. -/
theorem minorBasicOpenIso_inv_ι (R : CommRingCat) (a b : Vec3 R) :
    (minorBasicOpenIso R a b).inv ≫
      Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen (cross a b).z) =
    Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (cross a b).z))) := by
  rw [Iso.inv_comp_eq]
  unfold minorBasicOpenIso
  simp only [Iso.trans_hom, Category.assoc, Functor.mapIso_hom, Iso.op_hom,
    Scheme.Spec_map, Quiver.Hom.unop_op]
  rw [← Spec.map_comp]
  have hring : CommRingCat.ofHom (algebraMap R (Localization.Away (cross a b).z)) ≫
      (IsLocalization.algEquiv (Submonoid.powers (cross a b).z)
        (Localization.Away (cross a b).z)
        Γ(Spec R, PrimeSpectrum.basicOpen (cross a b).z)).toRingEquiv.toCommRingCatIso.hom =
      CommRingCat.ofHom (algebraMap R Γ(Spec R, PrimeSpectrum.basicOpen (cross a b).z)) := by
    ext r
    change (IsLocalization.algEquiv (Submonoid.powers (cross a b).z)
      (Localization.Away (cross a b).z) Γ(Spec R, PrimeSpectrum.basicOpen (cross a b).z))
      (algebraMap R (Localization.Away (cross a b).z) r) = _
    exact AlgEquiv.commutes _ r
  rw [hring]
  exact (affineOpenSpecProjection _ _ _).symm

/-- The incidence open isomorphism followed by inclusion is the original
coefficient projection of the quotient algebra. -/
theorem localizedIncidenceBasicOpenIso_hom_ι {R : Type*} [CommRing R] (a b : Vec3 R) :
    (localizedIncidenceBasicOpenIso a b).hom ≫
      Scheme.Opens.ι (X := Spec (CommRingCat.of R)) (PrimeSpectrum.basicOpen (cross a b).z) =
    Spec.map (CommRingCat.ofHom
      ((algebraMap (Localization.Away (cross a b).z)
        (AffineIncidenceAlgebra (localizedRow a b a) (localizedRow a b b))).comp
        (algebraMap R (Localization.Away (cross a b).z)))) := by
  unfold localizedIncidenceBasicOpenIso
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [minorBasicOpenIso_inv_ι (CommRingCat.of R) a b]
  change Spec.map (CommRingCat.ofHom
      (algebraMap (Localization.Away (cross a b).z)
        (AffineIncidenceAlgebra (localizedRow a b a) (localizedRow a b b)))) ≫
    Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (cross a b).z))) = _
  rw [← Spec.map_comp]
  rfl


/-- The projective chart morphism is exactly the canonical incidence
projection followed by the actual projective coordinate-chart inclusion. -/
theorem netProjectiveIncidenceToProjective_eq_SpecMap
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (p : Fin 4) (i j k : Fin 3) :
    let a := projectiveNetLinearRow M p i j k
    let b := projectiveNetQuadraticRow M p i j k
    netProjectiveIncidenceToProjective M p i j k =
      Spec.map (CommRingCat.ofHom
        ((algebraMap (Localization.Away (cross a b).z)
          (AffineIncidenceAlgebra (localizedRow a b a) (localizedRow a b b))).comp
          (algebraMap (ProjectiveThreeChartRing (K := K) p)
            (Localization.Away (cross a b).z)))) ≫
        Proj.awayι (homogeneousSubmodule (Fin 4) K) (X p)
          (isHomogeneous_X K p) (by decide) := by
  dsimp only
  unfold netProjectiveIncidenceToProjective
  rw [← Category.assoc, localizedIncidenceBasicOpenIso_hom_ι]


/-- The actual structure morphism of projective three-space over its coefficient field. -/
def projectiveThreeStructure (K : Type*) [Field K] :
    ProjectiveThreeScheme K ⟶ Spec (CommRingCat.of K) :=
  Proj.toSpecZero (homogeneousSubmodule (Fin 4) K) ≫
    Spec.map (CommRingCat.ofHom (algebraMap K (homogeneousSubmodule (Fin 4) K 0)))

/-- Compatibility with the original coefficient field: the projective
structure map pulls constants back by the actual quotient coefficient map. -/
theorem netProjectiveIncidenceToProjective_comp_structure
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (p : Fin 4) (i j k : Fin 3) :
    let a := projectiveNetLinearRow M p i j k
    let b := projectiveNetQuadraticRow M p i j k
    netProjectiveIncidenceToProjective M p i j k ≫ projectiveThreeStructure K =
      Spec.map (CommRingCat.ofHom
        (((algebraMap (Localization.Away (cross a b).z)
          (AffineIncidenceAlgebra (localizedRow a b a) (localizedRow a b b))).comp
          (algebraMap (ProjectiveThreeChartRing (K := K) p)
            (Localization.Away (cross a b).z))).comp (threeChartConstants p))) := by
  dsimp only
  rw [netProjectiveIncidenceToProjective_eq_SpecMap]
  unfold projectiveThreeStructure
  rw [Category.assoc, ← Category.assoc (Proj.awayι _ _ _ _),
    Proj.awayι_toSpecZero, ← Spec.map_comp, ← Spec.map_comp]
  rfl

end EvenQuinticConic.Incidence
