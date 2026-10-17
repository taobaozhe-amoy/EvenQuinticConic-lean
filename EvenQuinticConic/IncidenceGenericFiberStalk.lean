import EvenQuinticConic.IncidenceGenericFiberFunctionField
import EvenQuinticConic.SchemeFunctionFieldIso

/-!
# The actual generic incidence fibre's scheme function field

The generic stalk of the categorical generic fibre is identified with the
spatial rational function field through the actual scheme isomorphism and
its map on stalks.  The parameter action comes from the actual second
projection of the pullback.
-/

noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
namespace EvenQuinticConic.Incidence
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u
variable {K : Type u} [Field K]
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4)
    (h : (cross (segreChartRow (netLinearRow M) k p)
      (segreChartRow (netQuadraticRow M) k p)).z ≠ 0)
    (hinj : Function.Injective (incidenceParameterChartMap M k p))

/-- The affine generic stalk is the fraction field of its coordinate ring. -/
def incidenceGenericFiberAffineStalkEquiv :
    letI := incidenceGenericFiberRing_isDomain_of_injective M k p h hinj
    letI := globalIncidenceOpenGenericFiber_isIntegral_of_injective M k p h hinj
    letI : Algebra (IncidenceGenericFiberRing M k p)
        (Spec (CommRingCat.of (IncidenceGenericFiberRing M k p))).functionField :=
      AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec
        (CommRingCat.of (IncidenceGenericFiberRing M k p))
    (Spec (CommRingCat.of (IncidenceGenericFiberRing M k p))).functionField
      ≃ₐ[IncidenceGenericFiberRing M k p] FractionRing (IncidenceGenericFiberRing M k p) := by
  letI := incidenceGenericFiberRing_isDomain_of_injective M k p h hinj
  letI := globalIncidenceOpenGenericFiber_isIntegral_of_injective M k p h hinj
  letI : Nonempty (⊤ : (GlobalIncidenceOpenGenericFiber M k p h).Opens) :=
    ⟨⟨genericPoint _, trivial⟩⟩
  letI : Nonempty (⊤ : (Spec (CommRingCat.of (IncidenceGenericFiberRing M k p))).Opens) :=
    ⟨⟨genericPoint _, trivial⟩⟩
  letI : Algebra (IncidenceGenericFiberRing M k p)
      (Spec (CommRingCat.of (IncidenceGenericFiberRing M k p))).functionField :=
    AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec
      (CommRingCat.of (IncidenceGenericFiberRing M k p))
  letI : IsFractionRing (IncidenceGenericFiberRing M k p)
      (Spec (CommRingCat.of (IncidenceGenericFiberRing M k p))).functionField :=
    functionField_isFractionRing_of_affine (CommRingCat.of (IncidenceGenericFiberRing M k p))
  exact IsLocalization.algEquiv (nonZeroDivisors (IncidenceGenericFiberRing M k p))
    (Spec (CommRingCat.of (IncidenceGenericFiberRing M k p))).functionField
    (FractionRing (IncidenceGenericFiberRing M k p))

/-- The actual scheme function field, via the actual scheme isomorphism. -/
def globalIncidenceOpenGenericFiberStalkRingEquiv :
    letI := incidenceGenericFiberRing_isDomain_of_injective M k p h hinj
    letI := globalIncidenceOpenGenericFiber_isIntegral_of_injective M k p h hinj
    (GlobalIncidenceOpenGenericFiber M k p h).functionField ≃+*
      IncidenceSpatialFunctionField K := by
  letI := incidenceGenericFiberRing_isDomain_of_injective M k p h hinj
  letI := globalIncidenceOpenGenericFiber_isIntegral_of_injective M k p h hinj
  letI : Algebra (IncidenceGenericFiberRing M k p)
      (Spec (CommRingCat.of (IncidenceGenericFiberRing M k p))).functionField :=
    AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec
      (CommRingCat.of (IncidenceGenericFiberRing M k p))
  letI : Nonempty (⊤ : (GlobalIncidenceOpenGenericFiber M k p h).Opens) :=
    ⟨⟨genericPoint _, trivial⟩⟩
  letI : Nonempty (⊤ : (Spec (CommRingCat.of (IncidenceGenericFiberRing M k p))).Opens) :=
    ⟨⟨genericPoint _, trivial⟩⟩
  exact ((schemeIsoFunctionFieldRingEquiv
    (globalIncidenceOpenGenericFiberIso M k p h).symm).trans
      (incidenceGenericFiberAffineStalkEquiv M k p h hinj).toRingEquiv).trans
        (incidenceGenericFiberFractionFieldEquiv M k p h hinj).toRingEquiv

/-- Rational parameters act by actual pullback followed by the generic germ. -/
def globalIncidenceOpenGenericFiberStalkParameterMap :
    letI := incidenceGenericFiberRing_isDomain_of_injective M k p h hinj
    letI := globalIncidenceOpenGenericFiber_isIntegral_of_injective M k p h hinj
    IncidenceParameterChartField (K := K) k →+*
      (GlobalIncidenceOpenGenericFiber M k p h).functionField := by
  letI := incidenceGenericFiberRing_isDomain_of_injective M k p h hinj
  letI := globalIncidenceOpenGenericFiber_isIntegral_of_injective M k p h hinj
  letI : Nonempty (⊤ : (GlobalIncidenceOpenGenericFiber M k p h).Opens) :=
    ⟨⟨genericPoint _, trivial⟩⟩
  letI : Nonempty (⊤ : (Spec (CommRingCat.of (IncidenceGenericFiberRing M k p))).Opens) :=
    ⟨⟨genericPoint _, trivial⟩⟩
  exact ((GlobalIncidenceOpenGenericFiber M k p h).germToFunctionField ⊤).hom.comp
    (schemeBaseScalarHom (pullback.snd
      (globalIncidenceMinorParameterProjection M k p h)
      (incidenceParameterGenericPoint (K := K) k)))

/-- The parameter action is induced by the actual second projection. -/
def globalIncidenceOpenGenericFiberStalkParameterAlgebra :
    letI := incidenceGenericFiberRing_isDomain_of_injective M k p h hinj
    letI := globalIncidenceOpenGenericFiber_isIntegral_of_injective M k p h hinj
    Algebra (IncidenceParameterChartField (K := K) k)
      (GlobalIncidenceOpenGenericFiber M k p h).functionField := by
  letI := incidenceGenericFiberRing_isDomain_of_injective M k p h hinj
  letI := globalIncidenceOpenGenericFiber_isIntegral_of_injective M k p h hinj
  letI : Nonempty (⊤ : (GlobalIncidenceOpenGenericFiber M k p h).Opens) :=
    ⟨⟨genericPoint _, trivial⟩⟩
  letI : Nonempty (⊤ : (Spec (CommRingCat.of (IncidenceGenericFiberRing M k p))).Opens) :=
    ⟨⟨genericPoint _, trivial⟩⟩
  exact (globalIncidenceOpenGenericFiberStalkParameterMap M k p h hinj).toAlgebra

/-- Rational parameters retain their actual structural value after the
stalk map and the affine fraction-field comparison. -/
theorem globalIncidenceOpenGenericFiberStalkParameter_affine
    (z : IncidenceParameterChartField (K := K) k) :
    letI := incidenceGenericFiberRing_isDomain_of_injective M k p h hinj
    letI := globalIncidenceOpenGenericFiber_isIntegral_of_injective M k p h hinj
    (incidenceGenericFiberAffineStalkEquiv M k p h hinj)
        (schemeIsoFunctionFieldRingEquiv
          (globalIncidenceOpenGenericFiberIso M k p h).symm
          (globalIncidenceOpenGenericFiberStalkParameterMap M k p h hinj z)) =
      algebraMap (IncidenceGenericFiberRing M k p)
        (FractionRing (IncidenceGenericFiberRing M k p))
        (affineGenericFiberFractionMap (ProjectiveCoordinateQuotient (K := K) k)
          (SegreIncidenceMinorLocalization M k p) z) := by
  letI := incidenceGenericFiberRing_isDomain_of_injective M k p h hinj
  letI := globalIncidenceOpenGenericFiber_isIntegral_of_injective M k p h hinj
  letI : Algebra (IncidenceGenericFiberRing M k p)
      (Spec (CommRingCat.of (IncidenceGenericFiberRing M k p))).functionField :=
    AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec
      (CommRingCat.of (IncidenceGenericFiberRing M k p))
  letI : Nonempty (⊤ : (GlobalIncidenceOpenGenericFiber M k p h).Opens) :=
    ⟨⟨genericPoint _, trivial⟩⟩
  letI : Nonempty (⊤ : (Spec (CommRingCat.of (IncidenceGenericFiberRing M k p))).Opens) :=
    ⟨⟨genericPoint _, trivial⟩⟩
  change (incidenceGenericFiberAffineStalkEquiv M k p h hinj)
    (schemeIsoFunctionFieldRingEquiv
      (globalIncidenceOpenGenericFiberIso M k p h).symm
      ((GlobalIncidenceOpenGenericFiber M k p h).germToFunctionField ⊤
        (schemeBaseScalarHom (pullback.snd _ _) z))) = _
  rw [schemeIsoFunctionFieldRingEquiv_baseScalar
    (globalIncidenceOpenGenericFiberIso M k p h).symm
    (incidenceGenericFiberToParameter M k p) (pullback.snd _ _)
    (globalIncidenceOpenGenericFiberIso_inv_snd M k p h)]
  rw [show incidenceGenericFiberToParameter M k p =
    Spec.map (CommRingCat.ofHom
      (affineGenericFiberFractionMap (ProjectiveCoordinateQuotient (K := K) k)
        (SegreIncidenceMinorLocalization M k p))) from rfl]
  rw [affineFunctionField_germ_baseScalar]
  exact (incidenceGenericFiberAffineStalkEquiv M k p h hinj).commutes _

/-- The equivalence preserves the already computed actual parameter map. -/
theorem globalIncidenceOpenGenericFiberStalkRingEquiv_parameter
    (z : IncidenceParameterChartField (K := K) k) :
    letI := incidenceGenericFiberRing_isDomain_of_injective M k p h hinj
    letI := globalIncidenceOpenGenericFiber_isIntegral_of_injective M k p h hinj
    letI := incidenceSpatialParameterAlgebra M k p h hinj
    globalIncidenceOpenGenericFiberStalkRingEquiv M k p h hinj
        (globalIncidenceOpenGenericFiberStalkParameterMap M k p h hinj z) =
      algebraMap (IncidenceParameterChartField (K := K) k)
        (IncidenceSpatialFunctionField K) z := by
  letI := incidenceGenericFiberRing_isDomain_of_injective M k p h hinj
  letI := globalIncidenceOpenGenericFiber_isIntegral_of_injective M k p h hinj
  letI : Nonempty (⊤ : (GlobalIncidenceOpenGenericFiber M k p h).Opens) :=
    ⟨⟨genericPoint _, trivial⟩⟩
  letI : Nonempty (⊤ : (Spec (CommRingCat.of (IncidenceGenericFiberRing M k p))).Opens) :=
    ⟨⟨genericPoint _, trivial⟩⟩
  letI := incidenceSpatialParameterAlgebra M k p h hinj
  change incidenceGenericFiberFractionFieldEquiv M k p h hinj
    ((incidenceGenericFiberAffineStalkEquiv M k p h hinj)
      (schemeIsoFunctionFieldRingEquiv
        (globalIncidenceOpenGenericFiberIso M k p h).symm
        (globalIncidenceOpenGenericFiberStalkParameterMap M k p h hinj z))) = _
  rw [globalIncidenceOpenGenericFiberStalkParameter_affine]
  exact RingHom.congr_fun (incidenceGenericFiberFractionFieldEquiv_parameter M k p h hinj) z

/-- The actual scheme function field is identified over the actual parameter
field; this does not assert rationality over that parameter field. -/
def globalIncidenceOpenGenericFiberStalkEquiv_overParameter :
    letI := incidenceGenericFiberRing_isDomain_of_injective M k p h hinj
    letI := globalIncidenceOpenGenericFiber_isIntegral_of_injective M k p h hinj
    letI := globalIncidenceOpenGenericFiberStalkParameterAlgebra M k p h hinj
    letI := incidenceSpatialParameterAlgebra M k p h hinj
    (GlobalIncidenceOpenGenericFiber M k p h).functionField
      ≃ₐ[IncidenceParameterChartField (K := K) k] IncidenceSpatialFunctionField K := by
  letI := incidenceGenericFiberRing_isDomain_of_injective M k p h hinj
  letI := globalIncidenceOpenGenericFiber_isIntegral_of_injective M k p h hinj
  letI : Nonempty (⊤ : (GlobalIncidenceOpenGenericFiber M k p h).Opens) :=
    ⟨⟨genericPoint _, trivial⟩⟩
  letI : Nonempty (⊤ : (Spec (CommRingCat.of (IncidenceGenericFiberRing M k p))).Opens) :=
    ⟨⟨genericPoint _, trivial⟩⟩
  letI := globalIncidenceOpenGenericFiberStalkParameterAlgebra M k p h hinj
  letI := incidenceSpatialParameterAlgebra M k p h hinj
  refine { globalIncidenceOpenGenericFiberStalkRingEquiv M k p h hinj with
    commutes' := ?_ }
  exact globalIncidenceOpenGenericFiberStalkRingEquiv_parameter M k p h hinj

/-- The ground-field structure is the actual second projection followed
by the structural morphism of the parameter field. -/
def globalIncidenceOpenGenericFiberGroundStructure :
    GlobalIncidenceOpenGenericFiber M k p h ⟶ Spec (CommRingCat.of K) :=
  pullback.snd (globalIncidenceMinorParameterProjection M k p h)
    (incidenceParameterGenericPoint (K := K) k) ≫
      Spec.map (CommRingCat.ofHom
        (algebraMap K (IncidenceParameterChartField (K := K) k)))

/-- The ground-field map also comes directly from its structure morphism. -/
def globalIncidenceOpenGenericFiberStalkGroundMap :
    letI := incidenceGenericFiberRing_isDomain_of_injective M k p h hinj
    letI := globalIncidenceOpenGenericFiber_isIntegral_of_injective M k p h hinj
    K →+* (GlobalIncidenceOpenGenericFiber M k p h).functionField := by
  letI := incidenceGenericFiberRing_isDomain_of_injective M k p h hinj
  letI := globalIncidenceOpenGenericFiber_isIntegral_of_injective M k p h hinj
  letI : Nonempty (⊤ : (GlobalIncidenceOpenGenericFiber M k p h).Opens) :=
    ⟨⟨genericPoint _, trivial⟩⟩
  letI : Nonempty (⊤ : (Spec (CommRingCat.of (IncidenceGenericFiberRing M k p))).Opens) :=
    ⟨⟨genericPoint _, trivial⟩⟩
  exact ((GlobalIncidenceOpenGenericFiber M k p h).germToFunctionField ⊤).hom.comp
    (schemeBaseScalarHom (globalIncidenceOpenGenericFiberGroundStructure M k p h))

/-- Actual structure morphisms give the expected restriction of scalars. -/
theorem globalIncidenceOpenGenericFiberStalkGroundMap_eq_parameter (c : K) :
    letI := incidenceGenericFiberRing_isDomain_of_injective M k p h hinj
    letI := globalIncidenceOpenGenericFiber_isIntegral_of_injective M k p h hinj
    globalIncidenceOpenGenericFiberStalkGroundMap M k p h hinj c =
      globalIncidenceOpenGenericFiberStalkParameterMap M k p h hinj
        (algebraMap K (IncidenceParameterChartField (K := K) k) c) := by
  letI := incidenceGenericFiberRing_isDomain_of_injective M k p h hinj
  letI := globalIncidenceOpenGenericFiber_isIntegral_of_injective M k p h hinj
  letI : Nonempty (⊤ : (GlobalIncidenceOpenGenericFiber M k p h).Opens) :=
    ⟨⟨genericPoint _, trivial⟩⟩
  letI : Nonempty (⊤ : (Spec (CommRingCat.of (IncidenceGenericFiberRing M k p))).Opens) :=
    ⟨⟨genericPoint _, trivial⟩⟩
  change (GlobalIncidenceOpenGenericFiber M k p h).germToFunctionField ⊤
    ((pullback.snd (globalIncidenceMinorParameterProjection M k p h)
      (incidenceParameterGenericPoint (K := K) k)).appTop
      ((Spec.map (CommRingCat.ofHom
        (algebraMap K (IncidenceParameterChartField (K := K) k)))).appTop
          ((Scheme.ΓSpecIso (CommRingCat.of K)).inv c))) =
    (GlobalIncidenceOpenGenericFiber M k p h).germToFunctionField ⊤
      ((pullback.snd (globalIncidenceMinorParameterProjection M k p h)
      (incidenceParameterGenericPoint (K := K) k)).appTop
        ((Scheme.ΓSpecIso (CommRingCat.of
          (IncidenceParameterChartField (K := K) k))).inv
          (algebraMap K (IncidenceParameterChartField (K := K) k) c)))
  apply congrArg ((GlobalIncidenceOpenGenericFiber M k p h).germToFunctionField ⊤)
  apply congrArg (pullback.snd (globalIncidenceMinorParameterProjection M k p h)
      (incidenceParameterGenericPoint (K := K) k)).appTop
  exact DFunLike.congr_fun (CommRingCat.hom_ext_iff.mp
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom
      (algebraMap K (IncidenceParameterChartField (K := K) k)))).symm) c

/-- The actual parameter action on the spatial field extends its given
ground-field action. -/
theorem incidenceSpatialParameterAlgebra_ground (c : K) :
    letI := incidenceSpatialParameterAlgebra M k p h hinj
    algebraMap (IncidenceParameterChartField (K := K) k)
      (IncidenceSpatialFunctionField K)
      (algebraMap K (IncidenceParameterChartField (K := K) k) c) =
        algebraMap K (IncidenceSpatialFunctionField K) c := by
  letI := segreIncidenceMinorLocalization_isDomain M k p h
  letI := incidenceSpatialParameterAlgebra M k p h hinj
  change segreIncidenceMinorFractionFieldEquiv M k p h
    (parameterFractionFieldMap (ProjectiveCoordinateQuotient (K := K) k)
      (SegreIncidenceMinorLocalization M k p) hinj
      (algebraMap K (IncidenceParameterChartField (K := K) k) c)) = _
  rw [IsScalarTower.algebraMap_apply K (ProjectiveCoordinateQuotient (K := K) k)
    (IncidenceParameterChartField (K := K) k), parameterFractionFieldMap_algebraMap]
  rw [← IsScalarTower.algebraMap_apply K (ProjectiveCoordinateQuotient (K := K) k)
    (SegreIncidenceMinorLocalization M k p)]
  rw [← IsScalarTower.algebraMap_apply K (SegreIncidenceMinorLocalization M k p)
    (FractionRing (SegreIncidenceMinorLocalization M k p))]
  exact (segreIncidenceMinorFractionFieldEquiv M k p h).commutes c

/-- Ground-field scalars act through the actual ground structure morphism. -/
def globalIncidenceOpenGenericFiberStalkGroundAlgebra :
    letI := incidenceGenericFiberRing_isDomain_of_injective M k p h hinj
    letI := globalIncidenceOpenGenericFiber_isIntegral_of_injective M k p h hinj
    Algebra K (GlobalIncidenceOpenGenericFiber M k p h).functionField := by
  letI := incidenceGenericFiberRing_isDomain_of_injective M k p h hinj
  letI := globalIncidenceOpenGenericFiber_isIntegral_of_injective M k p h hinj
  letI : Nonempty (⊤ : (GlobalIncidenceOpenGenericFiber M k p h).Opens) :=
    ⟨⟨genericPoint _, trivial⟩⟩
  letI : Nonempty (⊤ : (Spec (CommRingCat.of (IncidenceGenericFiberRing M k p))).Opens) :=
    ⟨⟨genericPoint _, trivial⟩⟩
  exact (globalIncidenceOpenGenericFiberStalkGroundMap M k p h hinj).toAlgebra

/-- The actual generic stalk is a three-variable rational function field
over the original ground field, compatibly with its structure morphism. -/
def globalIncidenceOpenGenericFiberStalkEquiv_overGround :
    letI := incidenceGenericFiberRing_isDomain_of_injective M k p h hinj
    letI := globalIncidenceOpenGenericFiber_isIntegral_of_injective M k p h hinj
    letI := globalIncidenceOpenGenericFiberStalkGroundAlgebra M k p h hinj
    (GlobalIncidenceOpenGenericFiber M k p h).functionField ≃ₐ[K]
      IncidenceSpatialFunctionField K := by
  letI := incidenceGenericFiberRing_isDomain_of_injective M k p h hinj
  letI := globalIncidenceOpenGenericFiber_isIntegral_of_injective M k p h hinj
  letI : Nonempty (⊤ : (GlobalIncidenceOpenGenericFiber M k p h).Opens) :=
    ⟨⟨genericPoint _, trivial⟩⟩
  letI : Nonempty (⊤ : (Spec (CommRingCat.of (IncidenceGenericFiberRing M k p))).Opens) :=
    ⟨⟨genericPoint _, trivial⟩⟩
  letI := globalIncidenceOpenGenericFiberStalkGroundAlgebra M k p h hinj
  refine { globalIncidenceOpenGenericFiberStalkRingEquiv M k p h hinj with
    commutes' := ?_ }
  intro c
  change globalIncidenceOpenGenericFiberStalkRingEquiv M k p h hinj
    (globalIncidenceOpenGenericFiberStalkGroundMap M k p h hinj c) = _
  rw [globalIncidenceOpenGenericFiberStalkGroundMap_eq_parameter,
    globalIncidenceOpenGenericFiberStalkRingEquiv_parameter]
  exact incidenceSpatialParameterAlgebra_ground M k p h hinj c

/-- Geometric matrix-net hypotheses supply injectivity internally.  The
conclusion concerns the actual generic stalk with its actual second-
projection parameter action, without an injectivity hypothesis. -/
def globalIncidenceOpenGenericFiberStalkEquiv_of_geometricJacobian
    [Infinite K] (h2 : (2 : K) ≠ 0) (hM : ∀ i, (M i).IsSymm)
    (hbase : ∀ i, M i 0 0 = 0)
    (hCert : ProjectiveJacobianCertificate (linearMatrixNet M).det) :
    let hInjective := incidenceParameterChartMap_injective_of_geometricJacobian
      h2 M hM hbase hCert k p h
    letI := globalIncidenceOpenGenericFiber_isIntegral_of_injective M k p h hInjective
    letI := globalIncidenceOpenGenericFiberStalkParameterAlgebra M k p h hInjective
    letI := incidenceSpatialParameterAlgebra M k p h hInjective
    (GlobalIncidenceOpenGenericFiber M k p h).functionField
      ≃ₐ[IncidenceParameterChartField (K := K) k] IncidenceSpatialFunctionField K := by
  let hInjective := incidenceParameterChartMap_injective_of_geometricJacobian
    h2 M hM hbase hCert k p h
  exact globalIncidenceOpenGenericFiberStalkEquiv_overParameter M k p h hInjective

/-- The same geometric hypotheses give rationality over the original ground
field for the actual generic incidence open's scheme function field. -/
def globalIncidenceOpenGenericFiberStalkEquiv_overGround_of_geometricJacobian
    [Infinite K] (h2 : (2 : K) ≠ 0) (hM : ∀ i, (M i).IsSymm)
    (hbase : ∀ i, M i 0 0 = 0)
    (hCert : ProjectiveJacobianCertificate (linearMatrixNet M).det) :
    let hInjective := incidenceParameterChartMap_injective_of_geometricJacobian
      h2 M hM hbase hCert k p h
    letI := globalIncidenceOpenGenericFiber_isIntegral_of_injective M k p h hInjective
    letI := globalIncidenceOpenGenericFiberStalkGroundAlgebra M k p h hInjective
    (GlobalIncidenceOpenGenericFiber M k p h).functionField ≃ₐ[K]
      IncidenceSpatialFunctionField K := by
  let hInjective := incidenceParameterChartMap_injective_of_geometricJacobian
    h2 M hM hbase hCert k p h
  exact globalIncidenceOpenGenericFiberStalkEquiv_overGround M k p h hInjective

end EvenQuinticConic.Incidence
