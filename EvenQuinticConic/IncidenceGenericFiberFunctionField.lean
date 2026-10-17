import EvenQuinticConic.IncidenceGenericFiberScheme
import EvenQuinticConic.LocalizationFractionField
import EvenQuinticConic.GlobalDominantIncidenceChart

/-!
# Function fields of the actual generic incidence open

The parameter-localized algebra is the coordinate algebra of the actual
generic base change constructed in IncidenceGenericFiberScheme. Injectivity
comes from the geometric matrix-net hypotheses. Its fraction field remains
the three-variable rational function field over K, with the actual parameter
function-field embedding preserved. No rationality over the parameter field
is asserted.
-/

noncomputable section
namespace EvenQuinticConic.Incidence
open MvPolynomial AlgebraicGeometry CategoryTheory

variable {K : Type*} [Field K]

/-- The two independently constructed localization presentations have
literally the same parameter denominator monoid. -/
theorem incidenceGenericFiberRing_eq_parameterLocalization
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4) :
    IncidenceGenericFiberRing M k p =
      ParameterLocalization (ProjectiveCoordinateQuotient (K := K) k)
        (SegreIncidenceMinorLocalization M k p) := rfl

/-- Injectivity of the actual parameter pullback proves integrality of the
actual generic-fiber coordinate ring. -/
theorem incidenceGenericFiberRing_isDomain_of_injective
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4)
    (h : (cross (segreChartRow (netLinearRow M) k p)
      (segreChartRow (netQuadraticRow M) k p)).z ≠ 0)
    (hinj : Function.Injective (incidenceParameterChartMap M k p)) :
    IsDomain (IncidenceGenericFiberRing M k p) := by
  letI := segreIncidenceMinorLocalization_isDomain M k p h
  exact parameterLocalization_isDomain (ProjectiveCoordinateQuotient (K := K) k)
    (SegreIncidenceMinorLocalization M k p) hinj

/-- The genuine categorical generic base change is nonempty. -/
theorem globalIncidenceOpenGenericFiber_nonempty_of_injective
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4)
    (h : (cross (segreChartRow (netLinearRow M) k p)
      (segreChartRow (netQuadraticRow M) k p)).z ≠ 0)
    (hinj : Function.Injective (incidenceParameterChartMap M k p)) :
    Nonempty (GlobalIncidenceOpenGenericFiber M k p h) := by
  letI := incidenceGenericFiberRing_isDomain_of_injective M k p h hinj
  exact Nonempty.map (globalIncidenceOpenGenericFiberIso M k p h).inv.base inferInstance

/-- The same actual generic base change is integral. -/
theorem globalIncidenceOpenGenericFiber_isIntegral_of_injective
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4)
    (h : (cross (segreChartRow (netLinearRow M) k p)
      (segreChartRow (netQuadraticRow M) k p)).z ≠ 0)
    (hinj : Function.Injective (incidenceParameterChartMap M k p)) :
    IsIntegral (GlobalIncidenceOpenGenericFiber M k p h) := by
  letI := incidenceGenericFiberRing_isDomain_of_injective M k p h hinj
  letI := globalIncidenceOpenGenericFiber_nonempty_of_injective M k p h hinj
  exact isIntegral_of_isOpenImmersion (globalIncidenceOpenGenericFiberIso M k p h).hom

/-- Passing to the actual generic parameter does not change the total
function field as an algebra over the original ground field. -/
def incidenceGenericFiberFractionFieldEquiv
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4)
    (h : (cross (segreChartRow (netLinearRow M) k p)
      (segreChartRow (netQuadraticRow M) k p)).z ≠ 0)
    (hinj : Function.Injective (incidenceParameterChartMap M k p)) :
    FractionRing (IncidenceGenericFiberRing M k p) ≃ₐ[K]
      IncidenceSpatialFunctionField K := by
  let A := ProjectiveCoordinateQuotient (K := K) k
  let B := SegreIncidenceMinorLocalization M k p
  let D := IncidenceGenericFiberRing M k p
  letI : IsDomain B := segreIncidenceMinorLocalization_isDomain M k p h
  let e : FractionRing D ≃+* FractionRing B :=
    parameterLocalizationFractionFieldEquiv A B hinj
  let eK : FractionRing D ≃ₐ[K] FractionRing B :=
    { e with
      commutes' := by
        intro c
        change e (algebraMap D (FractionRing D) (algebraMap K D c)) =
          algebraMap K (FractionRing B) c
        rw [IsScalarTower.algebraMap_apply K B D,
          IsScalarTower.algebraMap_apply K B (FractionRing B)]
        exact parameterLocalizationFractionFieldEquiv_coordinate A B hinj (algebraMap K B c) }
  exact eK.trans (segreIncidenceMinorFractionFieldEquiv M k p h)

/-- Every original incidence coordinate has the same value after passing
through the generic-fiber fraction field and its rationality equivalence. -/
@[simp] theorem incidenceGenericFiberFractionFieldEquiv_coordinate
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4)
    (h : (cross (segreChartRow (netLinearRow M) k p)
      (segreChartRow (netQuadraticRow M) k p)).z ≠ 0)
    (hinj : Function.Injective (incidenceParameterChartMap M k p))
    (b : SegreIncidenceMinorLocalization M k p) :
    incidenceGenericFiberFractionFieldEquiv M k p h hinj
      (algebraMap (IncidenceGenericFiberRing M k p)
        (FractionRing (IncidenceGenericFiberRing M k p))
        (algebraMap (SegreIncidenceMinorLocalization M k p) (IncidenceGenericFiberRing M k p) b)) =
      segreIncidenceMinorFractionFieldEquiv M k p h
        (algebraMap (SegreIncidenceMinorLocalization M k p)
          (FractionRing (SegreIncidenceMinorLocalization M k p)) b) := by
  letI := segreIncidenceMinorLocalization_isDomain M k p h
  change segreIncidenceMinorFractionFieldEquiv M k p h
    (parameterLocalizationFractionFieldEquiv
      (ProjectiveCoordinateQuotient (K := K) k) (SegreIncidenceMinorLocalization M k p) hinj _) = _
  exact congrArg (segreIncidenceMinorFractionFieldEquiv M k p h)
    (parameterLocalizationFractionFieldEquiv_coordinate
      (ProjectiveCoordinateQuotient (K := K) k) (SegreIncidenceMinorLocalization M k p) hinj b)

/-- Preservation extends to every rational parameter, using the exact
fraction-field action defining the actual base change. -/
theorem incidenceGenericFiberFractionFieldEquiv_parameter
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4)
    (h : (cross (segreChartRow (netLinearRow M) k p)
      (segreChartRow (netQuadraticRow M) k p)).z ≠ 0)
    (hinj : Function.Injective (incidenceParameterChartMap M k p)) :
    letI := segreIncidenceMinorLocalization_isDomain M k p h
    (incidenceGenericFiberFractionFieldEquiv M k p h hinj).toRingHom.comp
      ((algebraMap (IncidenceGenericFiberRing M k p)
        (FractionRing (IncidenceGenericFiberRing M k p))).comp
        (affineGenericFiberFractionMap (ProjectiveCoordinateQuotient (K := K) k)
          (SegreIncidenceMinorLocalization M k p))) =
      (segreIncidenceMinorFractionFieldEquiv M k p h).toRingHom.comp
        (parameterFractionFieldMap (ProjectiveCoordinateQuotient (K := K) k)
          (SegreIncidenceMinorLocalization M k p) hinj) := by
  letI := segreIncidenceMinorLocalization_isDomain M k p h
  apply IsFractionRing.ringHom_ext (A := ProjectiveCoordinateQuotient (K := K) k)
  intro a
  simp only [RingHom.comp_apply, affineGenericFiberFractionMap_algebraMap,
    parameterFractionFieldMap_algebraMap]
  exact incidenceGenericFiberFractionFieldEquiv_coordinate M k p h hinj
    (incidenceParameterChartMap M k p a)

/-- The parameter field acts on the actual generic-fiber ring by the
same structural map used in its categorical base change. -/
abbrev incidenceGenericFiberParameterAlgebra
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4) :
    Algebra (IncidenceParameterChartField (K := K) k) (IncidenceGenericFiberRing M k p) :=
  (affineGenericFiberFractionMap (ProjectiveCoordinateQuotient (K := K) k)
    (SegreIncidenceMinorLocalization M k p)).toAlgebra

/-- The spatial rational field carries the actual pulled-back parameter
action, through the original incidence coordinate fraction field. -/
def incidenceSpatialParameterAlgebra
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4)
    (h : (cross (segreChartRow (netLinearRow M) k p)
      (segreChartRow (netQuadraticRow M) k p)).z ≠ 0)
    (hinj : Function.Injective (incidenceParameterChartMap M k p)) :
    Algebra (IncidenceParameterChartField (K := K) k) (IncidenceSpatialFunctionField K) := by
  letI := segreIncidenceMinorLocalization_isDomain M k p h
  exact ((segreIncidenceMinorFractionFieldEquiv M k p h).toRingHom.comp
    (parameterFractionFieldMap (ProjectiveCoordinateQuotient (K := K) k)
      (SegreIncidenceMinorLocalization M k p) hinj)).toAlgebra

/-- The function-field identification is an equivalence over the actual
parameter field, with its action inherited from the actual generic fibre.
This is not a claim that the conic is rational over that parameter field. -/
def incidenceGenericFiberFractionFieldEquiv_overParameter
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4)
    (h : (cross (segreChartRow (netLinearRow M) k p)
      (segreChartRow (netQuadraticRow M) k p)).z ≠ 0)
    (hinj : Function.Injective (incidenceParameterChartMap M k p)) :
    letI := incidenceGenericFiberParameterAlgebra M k p
    letI := incidenceSpatialParameterAlgebra M k p h hinj
    FractionRing (IncidenceGenericFiberRing M k p) ≃ₐ[IncidenceParameterChartField (K := K) k]
      IncidenceSpatialFunctionField K := by
  letI := incidenceGenericFiberParameterAlgebra M k p
  letI := incidenceSpatialParameterAlgebra M k p h hinj
  refine { (incidenceGenericFiberFractionFieldEquiv M k p h hinj).toRingEquiv with
    commutes' := ?_ }
  intro z
  exact RingHom.congr_fun (incidenceGenericFiberFractionFieldEquiv_parameter M k p h hinj) z

/-- Matrix-net hypotheses supply the actual nonempty integral generic
base change and its rational total function field without an injectivity input. -/
theorem incidenceGenericFiber_of_geometricJacobian [Infinite K]
    (h2 : (2 : K) ≠ 0)
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (hM : ∀ i, (M i).IsSymm)
    (hbase : ∀ i, M i 0 0 = 0)
    (hCert : ProjectiveJacobianCertificate (linearMatrixNet M).det)
    (k : Fin 3) (p : Fin 4)
    (h : (cross (segreChartRow (netLinearRow M) k p)
      (segreChartRow (netQuadraticRow M) k p)).z ≠ 0) :
    Nonempty (GlobalIncidenceOpenGenericFiber M k p h) ∧
    IsIntegral (GlobalIncidenceOpenGenericFiber M k p h) ∧
    IsDomain (IncidenceGenericFiberRing M k p) ∧
    Nonempty (FractionRing (IncidenceGenericFiberRing M k p) ≃ₐ[K]
      IncidenceSpatialFunctionField K) := by
  have hinj := incidenceParameterChartMap_injective_of_geometricJacobian
    h2 M hM hbase hCert k p h
  exact ⟨globalIncidenceOpenGenericFiber_nonempty_of_injective M k p h hinj,
    globalIncidenceOpenGenericFiber_isIntegral_of_injective M k p h hinj,
    incidenceGenericFiberRing_isDomain_of_injective M k p h hinj,
    ⟨incidenceGenericFiberFractionFieldEquiv M k p h hinj⟩⟩

/-- Starting at an arbitrary actual common isotropic point, construct a
nonempty integral generic base change of the actual global incidence open.
The matrix normalization, nonzero minor, dominance, integrality and rational
total function field are all conclusions. -/
theorem exists_integral_genericFiber_of_common_point
    [Infinite K] (h2 : (2 : K) ≠ 0)
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (hM : ∀ i, (M i).IsSymm)
    (P : Fin 5 → K) (hP : P ≠ 0)
    (hisotropic : ∀ i, dotProduct P ((M i).mulVec P) = 0)
    (hCert : ProjectiveJacobianCertificate (linearMatrixNet M).det) :
    ∃ B : Matrix (Fin 5) (Fin 5) K, B.det ≠ 0 ∧ (∀ j, B j 0 = P j) ∧
      ∃ (k : Fin 3) (p : Fin 4),
        ∃ h : (cross (segreChartRow (netLinearRow (matrixNetCongruence M B)) k p)
          (segreChartRow (netQuadraticRow (matrixNetCongruence M B)) k p)).z ≠ 0,
        IsDominant (globalIncidenceMinorParameterProjection (matrixNetCongruence M B) k p h) ∧
        Nonempty (GlobalIncidenceOpenGenericFiber (matrixNetCongruence M B) k p h) ∧
        IsIntegral (GlobalIncidenceOpenGenericFiber (matrixNetCongruence M B) k p h) ∧
        IsDomain (IncidenceGenericFiberRing (matrixNetCongruence M B) k p) ∧
        Nonempty (FractionRing (IncidenceGenericFiberRing (matrixNetCongruence M B) k p) ≃ₐ[K]
          IncidenceSpatialFunctionField K) := by
  obtain ⟨B, hB, hcol, k, p, h, _, _, hdom, _, _⟩ :=
    exists_dominant_rational_globalIncidenceOpen_of_common_point
      h2 M hM P hP hisotropic hCert
  have hbase : ∀ i, matrixNetCongruence M B i 0 0 = 0 := by
    intro i
    rw [matrixNetCongruence_zero_zero M B P hcol i, hisotropic i]
  refine ⟨B, hB, hcol, k, p, h, hdom, ?_⟩
  exact incidenceGenericFiber_of_geometricJacobian h2
    (matrixNetCongruence M B) (matrixNetCongruence_isSymm M hM B) hbase
    (linearMatrixNet_congruence_jacobianCertificate M B hB hCert) k p h

end EvenQuinticConic.Incidence
