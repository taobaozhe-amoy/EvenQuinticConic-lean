import EvenQuinticConic.IncidenceGenericConicSmooth
import EvenQuinticConic.IncidenceGenericConicFunctionField

/-!
# The whole generic conic constructed from a common point

Starting from the original symmetric matrix net, a nonzero common isotropic
point and the geometric Jacobian certificate, this endpoint chooses the
normalization, affine charts, nonzero minor and polar elimination coordinate.
The resulting actual whole projective conic is integral and smooth of
relative dimension one over its actual parameter field. Its actual function
field is the three-variable rational function field over the original ground
field, and the actual generic incidence fibre is a nonempty open of it.

The parameter-field action on that rational function field remains the actual
Cramer action. This does not assert rationality over the parameter field.
-/

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace EvenQuinticConic.Incidence

open AlgebraicGeometry CategoryTheory

variable {K : Type} [Field K]

/-- All geometry of the actual whole generic conic is derived from the
original common point and the original geometric Jacobian certificate.
Neither integrality, smoothness, a conic rational point nor a function-field
comparison is an additional hypothesis. -/
theorem exists_integral_smooth_genericConic_of_common_point
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
  obtain ⟨B, hB, hcol, k, p, h, _, _, _, _, _⟩ :=
    exists_dominant_rational_globalIncidenceOpen_of_common_point
      h2 M hM P hP hisotropic hCert
  have hbase : ∀ i, matrixNetCongruence M B i 0 0 = 0 := by
    intro i
    rw [matrixNetCongruence_zero_zero M B P hcol i, hisotropic i]
  have hSymm := matrixNetCongruence_isSymm M hM B
  have hJac := linearMatrixNet_congruence_jacobianCertificate M B hB hCert
  obtain ⟨q, hq, hsymm, hdet, hopen, hnonempty, hiso, _⟩ :=
    exists_globalIncidenceGenericConicChart h2 (matrixNetCongruence M B)
      hSymm hbase hJac k p h
  have hIntegral := incidenceGenericConicScheme_isIntegral h2 (matrixNetCongruence M B)
    hSymm hbase hJac k p h q hq
  have hSmooth := incidenceGenericConicStructure_isSmoothOfRelativeDimension h2
    (matrixNetCongruence M B) hSymm hbase hJac k p h q hq
  refine ⟨B, hB, hcol, k, p, h, q, hsymm, hdet, hSmooth, hIntegral, ?_⟩
  exact ⟨⟨incidenceGenericConicFunctionFieldEquiv_overParameter_of_geometricJacobian h2
      (matrixNetCongruence M B) hSymm hbase hJac k p h q hq⟩,
    ⟨incidenceGenericConicFunctionFieldEquiv_overGround_of_geometricJacobian h2
      (matrixNetCongruence M B) hSymm hbase hJac k p h q hq⟩,
    globalIncidenceGenericConicChartMap h2 (matrixNetCongruence M B)
      hSymm hbase hJac k p h q hq,
    hopen, hnonempty, hiso⟩

end EvenQuinticConic.Incidence
