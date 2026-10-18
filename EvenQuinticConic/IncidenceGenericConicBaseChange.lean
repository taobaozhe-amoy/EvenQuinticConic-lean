import EvenQuinticConic.TernaryConicBaseChange
import EvenQuinticConic.IncidenceGenericConicEndpoint

/-!
# Actual field extensions of the generic incidence conic

Every extension of the actual parameter field gives an integral categorical
base change of the same projective conic. Smoothness of relative dimension
one also holds for its actual projection to the extended field. The common
point endpoint retains the original parameter and ground-field actions on
the function field and the previously constructed nonempty open immersion.
-/

noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace EvenQuinticConic.Incidence

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

variable {K : Type} [Field K]

section Normalized

variable [Infinite K] (h2 : (2 : K) ≠ 0)
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (hM : ∀ i, (M i).IsSymm)
    (hbase : ∀ i, M i 0 0 = 0)
    (hCert : ProjectiveJacobianCertificate (linearMatrixNet M).det)
    (k : Fin 3) (p : Fin 4)
    (h : (cross (segreChartRow (netLinearRow M) k p)
      (segreChartRow (netQuadraticRow M) k p)).z ≠ 0)
    (q : Fin 3) (hq : incidenceGenericMatrix M k p h (p.succAbove q).succ 0 ≠ 0)
    {L : Type} [Field L] [Algebra (incidenceParameterSubfield M k p h) L]

include h2 hM hbase hCert hq in
/-- Integrality after every actual extension of the actual parameter field
is deduced from the original matrix net's geometric Jacobian certificate. -/
theorem incidenceGenericConicFieldBaseChange_isIntegral :
    IsIntegral (PlaneCurveFieldBaseChange L
      (incidenceGenericConicPolynomial M k p h q)) := by
  exact ternaryConicFieldBaseChange_isIntegral (L := L)
    (incidenceParameterSubfield_two_ne_zero h2 M k p h) _
    (incidenceGenericConicMatrix_isSymm M hM k p h (p.succAbove q))
    (incidenceGenericConicMatrix_det_ne_zero_of_geometricJacobian
      h2 M hM hbase hCert k p h q hq)

include h2 hM hbase hCert hq in
/-- The actual extended conic is smooth of relative dimension one over
the actual extension field, by stability of the original smooth morphism. -/
theorem incidenceGenericConicFieldBaseChange_isSmoothOfRelativeDimension :
    IsSmoothOfRelativeDimension 1
      (pullback.snd
        (planeCurveStructure (incidenceGenericConicPolynomial M k p h q))
        (Spec.map (CommRingCat.ofHom
          (algebraMap (incidenceParameterSubfield M k p h) L)))) := by
  letI := isSmoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
  exact MorphismProperty.pullback_snd (P := @IsSmoothOfRelativeDimension 1) _ _
    (incidenceGenericConicStructure_isSmoothOfRelativeDimension
      h2 M hM hbase hCert k p h q hq)

end Normalized

/-- The original common point produces one actual generic conic whose
categorical pullback is integral over every extension of its actual parameter
field. Its smooth structure, two function-field actions and actual incidence
open immersion are retained in the same conclusion. -/
theorem exists_fieldExtension_integral_smooth_genericConic_of_common_point
    [Infinite K] (h2 : (2 : K) ≠ 0)
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (hM : ∀ i, (M i).IsSymm)
    (P : Fin 5 → K) (hP : P ≠ 0)
    (hisotropic : ∀ i, dotProduct P ((M i).mulVec P) = 0)
    (hCert : ProjectiveJacobianCertificate (linearMatrixNet M).det) :
    ∃ B : Matrix (Fin 5) (Fin 5) K, B.det ≠ 0 ∧ (∀ j, B j 0 = P j) ∧
      ∃ (k : Fin 3) (p : Fin 4),
        ∃ h : (cross (segreChartRow (netLinearRow (matrixNetCongruence M B)) k p)
          (segreChartRow (netQuadraticRow (matrixNetCongruence M B)) k p)).z ≠ 0,
        ∃ q : Fin 3,
          (incidenceGenericConicMatrix (matrixNetCongruence M B) k p h
            (p.succAbove q)).IsSymm ∧
          (incidenceGenericConicMatrix (matrixNetCongruence M B) k p h
            (p.succAbove q)).det ≠ 0 ∧
          (∀ (L : Type) [Field L]
              [Algebra (incidenceParameterSubfield (matrixNetCongruence M B) k p h) L],
            IsIntegral (PlaneCurveFieldBaseChange L
              (incidenceGenericConicPolynomial (matrixNetCongruence M B) k p h q))) ∧
          IsSmoothOfRelativeDimension 1
            (planeCurveStructure
              (incidenceGenericConicPolynomial (matrixNetCongruence M B) k p h q)) ∧
          ∃ hIntegral : IsIntegral
              (IncidenceGenericConicScheme (matrixNetCongruence M B) k p h q),
            letI := hIntegral
            letI := incidenceGenericConicFunctionFieldGroundAlgebra
              (matrixNetCongruence M B) k p h q
            letI := incidenceGenericConicFunctionFieldParameterAlgebra
              (matrixNetCongruence M B) k p h q
            Nonempty
              ((IncidenceGenericConicScheme (matrixNetCongruence M B) k p h q).functionField
                ≃ₐ[incidenceParameterSubfield (matrixNetCongruence M B) k p h]
                  IncidenceSpatialFunctionField K) ∧
            Nonempty
              ((IncidenceGenericConicScheme (matrixNetCongruence M B) k p h q).functionField
                ≃ₐ[K] IncidenceSpatialFunctionField K) ∧
            ∃ f : GlobalIncidenceOpenGenericFiber (matrixNetCongruence M B) k p h ⟶
              IncidenceGenericConicScheme (matrixNetCongruence M B) k p h q,
            ∃ hf : IsOpenImmersion f,
              letI := hf
              Nonempty f.opensRange ∧
              Nonempty (GlobalIncidenceOpenGenericFiber (matrixNetCongruence M B) k p h ≅
                f.opensRange.toScheme) := by
  obtain ⟨B, hB, hcol, k, p, h, q, hsymm, hdet, hSmooth, hIntegral, hrest⟩ :=
    exists_integral_smooth_genericConic_of_common_point h2 M hM P hP hisotropic hCert
  refine ⟨B, hB, hcol, k, p, h, q, hsymm, hdet, ?_, hSmooth, hIntegral, hrest⟩
  intro L _ _
  exact ternaryConicFieldBaseChange_isIntegral (L := L)
    (incidenceParameterSubfield_two_ne_zero h2 (matrixNetCongruence M B) k p h)
    _ hsymm hdet

end EvenQuinticConic.Incidence
