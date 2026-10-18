import EvenQuinticConic.IncidenceCliffordNormalization
import EvenQuinticConic.IncidenceGenericConicBaseChange

/-!
# One common-point endpoint for the actual generic conic and Clifford transport

The normalization, affine chart, polar pivot and ternary conic are chosen once.
For those same choices, the actual whole conic is integral, smooth and integral
under every field extension; its two actual function-field actions and nonempty
incidence open are retained. The actual generic quadratic form is isometric to
the hyperbolic sum with that exact ternary form. The induced equivalence compares
the actual even Clifford algebras over the same actual parameter field.
Both the normalized and original net matrices are compared, using the exact
same Cramer parameters and the proved original coordinate change.

This isometry-induced equivalence does not assert a matrix-algebra description
of the hyperbolic sum's even Clifford algebra or a Brauer-class comparison.
-/

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

namespace EvenQuinticConic.Incidence

open AlgebraicGeometry CategoryTheory

variable {K : Type} [Field K]

/-- The original common point and geometric Jacobian certificate produce one
actual generic conic with all the previous geometric and function-field
conclusions, together with its explicit hyperbolic quadratic-space and even
Clifford comparisons. No isometry or Clifford equivalence is an extra input. -/
theorem exists_fieldExtension_integral_smooth_genericConic_clifford_of_common_point
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
          Nonempty
            ((matrixQuadraticForm (incidenceHyperbolicSumMatrix
              (incidenceGenericConicMatrix (matrixNetCongruence M B) k p h
                (p.succAbove q)))).IsometryEquiv
                  (matrixQuadraticForm
                    (incidenceGenericMatrix (matrixNetCongruence M B) k p h))) ∧
          Nonempty
            (CliffordAlgebra.even (matrixQuadraticForm (incidenceHyperbolicSumMatrix
              (incidenceGenericConicMatrix (matrixNetCongruence M B) k p h
                (p.succAbove q))))
              ≃ₐ[incidenceParameterSubfield (matrixNetCongruence M B) k p h]
                CliffordAlgebra.even (matrixQuadraticForm
                  (incidenceGenericMatrix (matrixNetCongruence M B) k p h))) ∧
          Nonempty
            ((matrixQuadraticForm (incidenceHyperbolicSumMatrix
              (incidenceGenericConicMatrix (matrixNetCongruence M B) k p h
                (p.succAbove q)))).IsometryEquiv
                  (matrixQuadraticForm (incidenceOriginalGenericMatrix M B k p h))) ∧
          Nonempty
            (CliffordAlgebra.even (matrixQuadraticForm (incidenceHyperbolicSumMatrix
              (incidenceGenericConicMatrix (matrixNetCongruence M B) k p h
                (p.succAbove q))))
              ≃ₐ[incidenceParameterSubfield (matrixNetCongruence M B) k p h]
                CliffordAlgebra.even
                  (matrixQuadraticForm (incidenceOriginalGenericMatrix M B k p h))) ∧
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
  refine ⟨B, hB, hcol, k, p, h, q, hsymm, hdet, ?_, hSmooth,
    ⟨incidenceGenericQuadraticIsometry h2 (matrixNetCongruence M B)
      hSymm hbase k p h (p.succAbove q) hq⟩,
    ⟨incidenceGenericEvenCliffordEquiv h2 (matrixNetCongruence M B)
      hSymm hbase k p h (p.succAbove q) hq⟩,
    ⟨incidenceOriginalGenericQuadraticIsometry M B k p h h2 hM hB hbase
      (p.succAbove q) hq⟩,
    ⟨incidenceOriginalGenericEvenCliffordEquiv M B k p h h2 hM hB hbase
      (p.succAbove q) hq⟩, hIntegral, ?_⟩
  · intro L _ _
    exact incidenceGenericConicFieldBaseChange_isIntegral (L := L)
      h2 (matrixNetCongruence M B) hSymm hbase hJac k p h q hq
  · exact ⟨⟨incidenceGenericConicFunctionFieldEquiv_overParameter_of_geometricJacobian h2
        (matrixNetCongruence M B) hSymm hbase hJac k p h q hq⟩,
      ⟨incidenceGenericConicFunctionFieldEquiv_overGround_of_geometricJacobian h2
        (matrixNetCongruence M B) hSymm hbase hJac k p h q hq⟩,
      globalIncidenceGenericConicChartMap h2 (matrixNetCongruence M B)
        hSymm hbase hJac k p h q hq,
      hopen, hnonempty, hiso⟩

end EvenQuinticConic.Incidence
