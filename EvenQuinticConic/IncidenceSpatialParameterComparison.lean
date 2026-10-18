import EvenQuinticConic.IncidenceGenericFiberFunctionField
import EvenQuinticConic.IncidenceParameterFieldIdentification

/-! The original parameter-fraction action equals the actual Cramer inclusion. -/
noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 120000
set_option Elab.async false

namespace EvenQuinticConic.Incidence



variable {K : Type*} [Field K] [Infinite K]
    (h2 : (2 : K) ≠ 0)
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (hM : ∀ i, (M i).IsSymm)
    (hbase : ∀ i, M i 0 0 = 0)
    (hCert : ProjectiveJacobianCertificate (linearMatrixNet M).det)
    (k : Fin 3) (p : Fin 4)
    (h : (cross (segreChartRow (netLinearRow M) k p)
      (segreChartRow (netQuadraticRow M) k p)).z ≠ 0)

/-- The field action used by the actual generic fibre agrees, on every
rational parameter, with the inclusion of the actual Cramer subfield. -/
theorem incidenceSpatialParameterMap_eq_actual :
    let hInjective := incidenceParameterChartMap_injective_of_geometricJacobian
      h2 M hM hbase hCert k p h
    letI := segreIncidenceMinorLocalization_isDomain M k p h
    (segreIncidenceMinorFractionFieldEquiv M k p h).toRingHom.comp
        (parameterFractionFieldMap (ProjectiveCoordinateQuotient (K := K) k)
          (SegreIncidenceMinorLocalization M k p) hInjective) =
      (incidenceParameterSubfield M k p h).val.toRingHom.comp
        (incidenceParameterChartFieldEquiv h2 M hM hbase hCert k p h).toRingHom := by
  let hInjective := incidenceParameterChartMap_injective_of_geometricJacobian
    h2 M hM hbase hCert k p h
  letI := segreIncidenceMinorLocalization_isDomain M k p h
  apply IsFractionRing.ringHom_ext (A := ProjectiveCoordinateQuotient (K := K) k)
  intro a
  simp only [RingHom.comp_apply]
  conv_lhs =>
    arg 2
    rw [parameterFractionFieldMap_algebraMap]
  simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    AlgEquiv.coe_ringEquiv', AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    IntermediateField.coe_val]
  have hb := incidenceParameterChartFieldEquiv_algebraMap h2 M hM hbase hCert k p h a
  simp only [IntermediateField.algebraMap_apply] at hb
  rw [hb]
  simp only [segreIncidenceMinorFractionFieldEquiv, AlgEquiv.trans_apply]
  rw [IsFractionRing.algEquivOfAlgEquiv_algebraMap]
  change localizedIncidenceFractionRingEquiv _ _ h
    (algebraMap _ _ ((segreIncidenceMinorLocalizationAlgEquiv M k p)
      (incidenceParameterChartMap M k p a))) = _
  rw [localizedIncidenceFractionRingEquiv_algebraMap]
  rfl

/-- The same comparison on every actual rational parameter, expressed with
its original generic-fibre algebra action. -/
theorem incidenceSpatialParameterAlgebra_eq_actual
    (t : IncidenceParameterChartField (K := K) k) :
    let hInjective := incidenceParameterChartMap_injective_of_geometricJacobian
      h2 M hM hbase hCert k p h
    letI := incidenceSpatialParameterAlgebra M k p h hInjective
    algebraMap (IncidenceParameterChartField (K := K) k) (IncidenceSpatialFunctionField K) t =
      algebraMap (incidenceParameterSubfield M k p h) (IncidenceSpatialFunctionField K)
        (incidenceParameterChartFieldEquiv h2 M hM hbase hCert k p h t) := by
  exact RingHom.congr_fun
    (incidenceSpatialParameterMap_eq_actual h2 M hM hbase hCert k p h) t

end EvenQuinticConic.Incidence
