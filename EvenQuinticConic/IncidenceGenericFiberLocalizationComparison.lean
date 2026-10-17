import EvenQuinticConic.IncidenceGenericFiberScheme
import EvenQuinticConic.IncidenceGenericFiberPresentation

/-!
# The actual generic fibre and its localized equation presentation

The coordinate ring of the already constructed generic fibre is compared
with the previous tensor-product equation presentation.  Both the parameter
field and the original incidence coordinates are retained.
-/

noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

namespace EvenQuinticConic.Incidence
open MvPolynomial TensorProduct
open scoped nonZeroDivisors

namespace ParameterTensorAway

variable (P S C B : Type*) [CommRing P] [CommRing S] [CommRing C] [CommRing B]
  [Algebra P S] [Algebra P C] [Algebra C B] [Algebra P B] [IsScalarTower P C B]
attribute [local instance] Algebra.TensorProduct.rightAlgebra

def tensorSwap : (S ⊗[P] C) ≃ₐ[C] C ⊗[P] S :=
  AlgEquiv.ofRingEquiv (f := (Algebra.TensorProduct.comm P S C).toRingEquiv) (by intro c; rfl)

def tensorCancel : ((S ⊗[P] C) ⊗[C] B) ≃+* S ⊗[P] B :=
  (Algebra.TensorProduct.comm C (S ⊗[P] C) B).toRingEquiv.trans <|
    (Algebra.TensorProduct.congr (AlgEquiv.refl : B ≃ₐ[C] B) (tensorSwap P S C)).toRingEquiv.trans <|
      (Algebra.TensorProduct.cancelBaseChange P C B B S).toRingEquiv.trans <|
        (Algebra.TensorProduct.comm P B S).toRingEquiv

@[simp] theorem tensorCancel_tmul (s : S) (c : C) (b : B) :
    tensorCancel P S C B ((s ⊗ₜ[P] c) ⊗ₜ[C] b) = s ⊗ₜ[P] (algebraMap C B c * b) := by
  simp [tensorCancel, tensorSwap, Algebra.smul_def]

@[simp] theorem tensorCancel_symm_tmul (s : S) (b : B) :
    (tensorCancel P S C B).symm (s ⊗ₜ[P] b) = (s ⊗ₜ[P] (1 : C)) ⊗ₜ[C] b := by
  apply (tensorCancel P S C B).injective
  simp

variable (r : C) [IsLocalization.Away r B]

def tensorAwayRingEquiv : S ⊗[P] B ≃+*
    Localization.Away ((1 : S) ⊗ₜ[P] r) :=
  (tensorCancel P S C B).symm.trans
    (IsLocalization.Away.tensorEquiv (S ⊗[P] C) r B).toRingEquiv

@[simp] theorem tensorAwayRingEquiv_tmul_algebraMap (s : S) (c : C) :
    tensorAwayRingEquiv P S C B r (s ⊗ₜ[P] algebraMap C B c) =
      algebraMap (S ⊗[P] C) (Localization.Away ((1 : S) ⊗ₜ[P] r)) (s ⊗ₜ[P] c) := by
  have h : (tensorCancel P S C B).symm (s ⊗ₜ[P] algebraMap C B c) =
      (s ⊗ₜ[P] c) ⊗ₜ[C] (1 : B) := by
    apply (tensorCancel P S C B).injective
    simp
  change IsLocalization.Away.tensorEquiv (S ⊗[P] C) r B
    ((tensorCancel P S C B).symm (s ⊗ₜ[P] algebraMap C B c)) = _
  rw [h]
  exact (IsLocalization.Away.tensorEquiv (S ⊗[P] C) r B).commutes (s ⊗ₜ[P] c)

def tensorAwayAlgEquiv : S ⊗[P] B ≃ₐ[S]
    Localization.Away ((1 : S) ⊗ₜ[P] r) :=
  AlgEquiv.ofRingEquiv (f := tensorAwayRingEquiv P S C B r) (by
    intro s
    change tensorAwayRingEquiv P S C B r (s ⊗ₜ[P] (1 : B)) = _
    rw [← map_one (algebraMap C B), tensorAwayRingEquiv_tmul_algebraMap]
    rfl)

@[simp] theorem tensorAwayAlgEquiv_tmul_algebraMap (s : S) (c : C) :
    tensorAwayAlgEquiv P S C B r (s ⊗ₜ[P] algebraMap C B c) =
      algebraMap (S ⊗[P] C) (Localization.Away ((1 : S) ⊗ₜ[P] r)) (s ⊗ₜ[P] c) :=
  tensorAwayRingEquiv_tmul_algebraMap P S C B r s c


end ParameterTensorAway

section Denominators
variable {P A B : Type*} [CommRing P] [CommRing A] [CommRing B]
  [Algebra P B] [Algebra A B]

/-- Changing the presentation of the base by the specified ring isomorphism
does not change the actual parameter denominator monoid. -/
theorem parameterDenominators_eq_of_equiv (e : P ≃+* A)
    (hc : ∀ p, algebraMap P B p = algebraMap A B (e p)) :
    Algebra.algebraMapSubmonoid B P⁰ = Algebra.algebraMapSubmonoid B A⁰ := by
  change P⁰.map (algebraMap P B).toMonoidHom = A⁰.map (algebraMap A B).toMonoidHom
  have he : P⁰.map e.toMonoidHom = A⁰ := MulEquivClass.map_nonZeroDivisors e
  rw [← he, Submonoid.map_map]
  congr 1
  exact MonoidHom.ext hc

end Denominators

variable {K : Type*} [Field K]

/-- The parameter-polynomial action on the original minor localization uses
the same parameter chart map as the actual scheme projection. -/
def incidenceMinorPolynomialAlgebra
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4) :
    Algebra (IncidenceParameterPolynomialRing K) (SegreIncidenceMinorLocalization M k p) :=
  letI := incidenceUnlocalizedParameterAlgebra M k p
  inferInstance

/-- The normalized quotient chart and its two polynomial coordinates give
exactly the same denominators in the actual incidence algebra. -/
theorem incidenceGenericFiberDenominators_eq_polynomial
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4) :
    letI := incidenceUnlocalizedParameterAlgebra M k p
    letI := incidenceMinorPolynomialAlgebra M k p
    affineGenericFiberDenominators (ProjectiveCoordinateQuotient (K := K) k)
        (SegreIncidenceMinorLocalization M k p) =
      Algebra.algebraMapSubmonoid (SegreIncidenceMinorLocalization M k p)
        (IncidenceParameterPolynomialRing K)⁰ := by
  letI := incidenceUnlocalizedParameterAlgebra M k p
  letI := incidenceMinorPolynomialAlgebra M k p
  exact (parameterDenominators_eq_of_equiv
    (incidenceParameterPolynomialChartAlgEquiv (K := K) k).toRingEquiv
    (fun f => incidenceParameterUnlocalizedPolynomialMap_localization M k p f)).symm

/-- The polynomial action also agrees with the unlocalized chart action
followed by inversion of its actual selected minor. -/
def incidenceMinorPolynomialScalarTower
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4) :
    letI := incidenceUnlocalizedParameterAlgebra M k p
    letI := incidenceMinorPolynomialAlgebra M k p
    IsScalarTower (IncidenceParameterPolynomialRing K)
      (SegreIncidenceChartAlgebra M k p) (SegreIncidenceMinorLocalization M k p) := by
  letI := incidenceUnlocalizedParameterAlgebra M k p
  letI := incidenceMinorPolynomialAlgebra M k p
  infer_instance

section ActualParameterField
variable [Infinite K] (h2 : (2 : K) ≠ 0)
  (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (hM : ∀ i, (M i).IsSymm)
  (hbase : ∀ i, M i 0 0 = 0)
  (hCert : ProjectiveJacobianCertificate (linearMatrixNet M).det)
  (k : Fin 3) (p : Fin 4)
  (h : (cross (segreChartRow (netLinearRow M) k p)
    (segreChartRow (netQuadraticRow M) k p)).z ≠ 0)

/-- The existing parameter field identification respects its literal
two-variable coefficient map, before any spatial base change. -/
def incidenceParameterFieldEquivOverPolynomial :
    letI := incidenceParameterSubfieldPolynomialAlgebra M k p h
    IncidenceRationalParameterField K ≃ₐ[IncidenceParameterPolynomialRing K]
      incidenceParameterSubfield M k p h := by
  letI := incidenceParameterSubfieldPolynomialAlgebra M k p h
  exact { (incidenceParameterFieldEquiv h2 M hM hbase hCert k p h).toRingEquiv with
    commutes' := incidenceParameterFieldEquiv_aeval_affine h2 M hM hbase hCert k p h }

include h2 hM hbase hCert in
/-- The actual parameter subfield is a fraction field of the actual
polynomial parameter ring, using the already fixed coefficient action. -/
theorem incidenceParameterSubfield_isFractionRing :
    letI := incidenceParameterSubfieldPolynomialAlgebra M k p h
    IsFractionRing (IncidenceParameterPolynomialRing K)
      (incidenceParameterSubfield M k p h) := by
  letI := incidenceParameterSubfieldPolynomialAlgebra M k p h
  exact IsLocalization.isLocalization_of_algEquiv (IncidenceParameterPolynomialRing K)⁰
    (incidenceParameterFieldEquivOverPolynomial h2 M hM hbase hCert k p h)

/-- The original generic-fibre ring is the actual coefficient base change
of the original minor localization to its actual parameter field. -/
def incidenceGenericFiberTensorEquiv :
    letI := incidenceUnlocalizedParameterAlgebra M k p
    letI := incidenceMinorPolynomialAlgebra M k p
    letI := incidenceParameterSubfieldPolynomialAlgebra M k p h
    IncidenceGenericFiberRing M k p ≃ₐ[SegreIncidenceMinorLocalization M k p]
      (SegreIncidenceMinorLocalization M k p) ⊗[IncidenceParameterPolynomialRing K]
        incidenceParameterSubfield M k p h := by
  letI := incidenceUnlocalizedParameterAlgebra M k p
  letI := incidenceMinorPolynomialAlgebra M k p
  letI := incidenceParameterSubfieldPolynomialAlgebra M k p h
  letI := incidenceParameterSubfield_isFractionRing h2 M hM hbase hCert k p h
  letI : IsLocalization
      (Algebra.algebraMapSubmonoid (SegreIncidenceMinorLocalization M k p)
        (IncidenceParameterPolynomialRing K)⁰) (IncidenceGenericFiberRing M k p) := by
    rw [← incidenceGenericFiberDenominators_eq_polynomial M k p]
    infer_instance
  exact IsLocalization.algEquiv
    (Algebra.algebraMapSubmonoid (SegreIncidenceMinorLocalization M k p)
      (IncidenceParameterPolynomialRing K)⁰) _ _

@[simp] theorem incidenceGenericFiberTensorEquiv_algebraMap
    (b : SegreIncidenceMinorLocalization M k p) :
    letI := incidenceUnlocalizedParameterAlgebra M k p
    letI := incidenceMinorPolynomialAlgebra M k p
    letI := incidenceParameterSubfieldPolynomialAlgebra M k p h
    incidenceGenericFiberTensorEquiv h2 M hM hbase hCert k p h
      (algebraMap (SegreIncidenceMinorLocalization M k p) (IncidenceGenericFiberRing M k p) b) =
        b ⊗ₜ[IncidenceParameterPolynomialRing K] (1 : incidenceParameterSubfield M k p h) := by
  letI := incidenceUnlocalizedParameterAlgebra M k p
  letI := incidenceMinorPolynomialAlgebra M k p
  letI := incidenceParameterSubfieldPolynomialAlgebra M k p h
  exact (incidenceGenericFiberTensorEquiv h2 M hM hbase hCert k p h).commutes b

/-- The fraction-field comparison also preserves polynomial parameters
inside the actual generated subfield, not just after embedding in a larger field. -/
theorem incidenceParameterChartFieldEquiv_polynomial
    (f : IncidenceParameterPolynomialRing K) :
    letI := incidenceParameterSubfieldPolynomialAlgebra M k p h
    incidenceParameterChartFieldEquiv h2 M hM hbase hCert k p h
      (algebraMap (ProjectiveCoordinateQuotient (K := K) k)
        (IncidenceParameterChartField (K := K) k) (incidenceParameterPolynomialChartMap k f)) =
      algebraMap (IncidenceParameterPolynomialRing K) (incidenceParameterSubfield M k p h) f := by
  letI := incidenceParameterSubfieldPolynomialAlgebra M k p h
  apply Subtype.ext
  exact (incidenceParameterChartFieldEquiv_algebraMap h2 M hM hbase hCert k p h _).trans
    (incidenceParameterSubfieldPolynomialAlgebra_compatibility M k p h f).symm

/-- Both presentations retain the actual fraction-field structural map. -/
theorem incidenceGenericFiberTensorEquiv_parameter :
    letI := incidenceUnlocalizedParameterAlgebra M k p
    letI := incidenceMinorPolynomialAlgebra M k p
    letI := incidenceParameterSubfieldPolynomialAlgebra M k p h
    (incidenceGenericFiberTensorEquiv h2 M hM hbase hCert k p h).toRingHom.comp
      (affineGenericFiberFractionMap (ProjectiveCoordinateQuotient (K := K) k)
        (SegreIncidenceMinorLocalization M k p)) =
    (Algebra.TensorProduct.includeRight (R := IncidenceParameterPolynomialRing K)
      (A := SegreIncidenceMinorLocalization M k p)
      (B := incidenceParameterSubfield M k p h)).toRingHom.comp
        (incidenceParameterChartFieldEquiv h2 M hM hbase hCert k p h).toRingHom := by
  letI := incidenceUnlocalizedParameterAlgebra M k p
  letI := incidenceMinorPolynomialAlgebra M k p
  letI := incidenceParameterSubfieldPolynomialAlgebra M k p h
  apply IsLocalization.ringHom_ext (ProjectiveCoordinateQuotient (K := K) k)⁰
  apply RingHom.ext
  intro a
  change incidenceGenericFiberTensorEquiv h2 M hM hbase hCert k p h
      (affineGenericFiberFractionMap (ProjectiveCoordinateQuotient (K := K) k)
        (SegreIncidenceMinorLocalization M k p)
          (algebraMap (ProjectiveCoordinateQuotient (K := K) k)
            (IncidenceParameterChartField (K := K) k) a)) =
    (1 : SegreIncidenceMinorLocalization M k p) ⊗ₜ[IncidenceParameterPolynomialRing K]
      incidenceParameterChartFieldEquiv h2 M hM hbase hCert k p h
        (algebraMap (ProjectiveCoordinateQuotient (K := K) k)
          (IncidenceParameterChartField (K := K) k) a)
  rw [affineGenericFiberFractionMap_algebraMap,
    incidenceGenericFiberTensorEquiv_algebraMap]
  obtain ⟨f, rfl⟩ := (incidenceParameterPolynomialChartAlgEquiv (K := K) k).surjective a
  rw [incidenceParameterPolynomialChartAlgEquiv_apply,
    incidenceParameterChartFieldEquiv_polynomial]
  change incidenceParameterChartMap M k p (incidenceParameterPolynomialChartMap k f) ⊗ₜ[_] 1 = _
  rw [← incidenceParameterUnlocalizedPolynomialMap_localization]
  exact Algebra.TensorProduct.tmul_one_eq_one_tmul f

/-- The actual generated parameter field acts on the original generic-fibre
ring through its existing fraction-field structural map. -/
def incidenceGenericFiberActualParameterAlgebra :
    Algebra (incidenceParameterSubfield M k p h) (IncidenceGenericFiberRing M k p) :=
  ((affineGenericFiberFractionMap (ProjectiveCoordinateQuotient (K := K) k)
    (SegreIncidenceMinorLocalization M k p)).comp
      (incidenceParameterChartFieldEquiv h2 M hM hbase hCert k p h).symm.toRingHom).toAlgebra

@[simp] theorem incidenceGenericFiberActualParameterAlgebra_algebraMap
    (s : incidenceParameterSubfield M k p h) :
    letI := incidenceGenericFiberActualParameterAlgebra h2 M hM hbase hCert k p h
    algebraMap (incidenceParameterSubfield M k p h) (IncidenceGenericFiberRing M k p) s =
      affineGenericFiberFractionMap (ProjectiveCoordinateQuotient (K := K) k)
        (SegreIncidenceMinorLocalization M k p)
        ((incidenceParameterChartFieldEquiv h2 M hM hbase hCert k p h).symm s) := rfl

/-- With that specified parameter action, the same comparison is an
isomorphism over the actual parameter field. -/
def incidenceGenericFiberTensorLeftEquiv :
    letI := incidenceUnlocalizedParameterAlgebra M k p
    letI := incidenceMinorPolynomialAlgebra M k p
    letI := incidenceParameterSubfieldPolynomialAlgebra M k p h
    letI := incidenceGenericFiberActualParameterAlgebra h2 M hM hbase hCert k p h
    IncidenceGenericFiberRing M k p ≃ₐ[incidenceParameterSubfield M k p h]
      (incidenceParameterSubfield M k p h) ⊗[IncidenceParameterPolynomialRing K]
        SegreIncidenceMinorLocalization M k p := by
  letI := incidenceUnlocalizedParameterAlgebra M k p
  letI := incidenceMinorPolynomialAlgebra M k p
  letI := incidenceParameterSubfieldPolynomialAlgebra M k p h
  letI := incidenceGenericFiberActualParameterAlgebra h2 M hM hbase hCert k p h
  refine { (incidenceGenericFiberTensorEquiv h2 M hM hbase hCert k p h).toRingEquiv.trans
      (Algebra.TensorProduct.comm (IncidenceParameterPolynomialRing K)
        (SegreIncidenceMinorLocalization M k p) (incidenceParameterSubfield M k p h)).toRingEquiv with
    commutes' := ?_ }
  intro s
  change Algebra.TensorProduct.comm (IncidenceParameterPolynomialRing K)
      (SegreIncidenceMinorLocalization M k p) (incidenceParameterSubfield M k p h)
      (incidenceGenericFiberTensorEquiv h2 M hM hbase hCert k p h
        (affineGenericFiberFractionMap (ProjectiveCoordinateQuotient (K := K) k)
          (SegreIncidenceMinorLocalization M k p)
          ((incidenceParameterChartFieldEquiv h2 M hM hbase hCert k p h).symm s))) = _
  rw [show incidenceGenericFiberTensorEquiv h2 M hM hbase hCert k p h
      (affineGenericFiberFractionMap (ProjectiveCoordinateQuotient (K := K) k)
        (SegreIncidenceMinorLocalization M k p)
        ((incidenceParameterChartFieldEquiv h2 M hM hbase hCert k p h).symm s)) =
      (1 : SegreIncidenceMinorLocalization M k p) ⊗ₜ[IncidenceParameterPolynomialRing K] s by
    have he := RingHom.congr_fun
      (incidenceGenericFiberTensorEquiv_parameter h2 M hM hbase hCert k p h)
      ((incidenceParameterChartFieldEquiv h2 M hM hbase hCert k p h).symm s)
    change incidenceGenericFiberTensorEquiv h2 M hM hbase hCert k p h
      (affineGenericFiberFractionMap (ProjectiveCoordinateQuotient (K := K) k)
        (SegreIncidenceMinorLocalization M k p)
        ((incidenceParameterChartFieldEquiv h2 M hM hbase hCert k p h).symm s)) =
      (1 : SegreIncidenceMinorLocalization M k p) ⊗ₜ[IncidenceParameterPolynomialRing K]
        (incidenceParameterChartFieldEquiv h2 M hM hbase hCert k p h)
          ((incidenceParameterChartFieldEquiv h2 M hM hbase hCert k p h).symm s) at he
    simpa only [AlgEquiv.apply_symm_apply] using he]
  simp only [Algebra.TensorProduct.comm_tmul]
  rfl

@[simp] theorem incidenceGenericFiberTensorLeftEquiv_algebraMap
    (b : SegreIncidenceMinorLocalization M k p) :
    letI := incidenceUnlocalizedParameterAlgebra M k p
    letI := incidenceMinorPolynomialAlgebra M k p
    letI := incidenceParameterSubfieldPolynomialAlgebra M k p h
    letI := incidenceGenericFiberActualParameterAlgebra h2 M hM hbase hCert k p h
    incidenceGenericFiberTensorLeftEquiv h2 M hM hbase hCert k p h
      (algebraMap (SegreIncidenceMinorLocalization M k p) (IncidenceGenericFiberRing M k p) b) =
      (1 : incidenceParameterSubfield M k p h) ⊗ₜ[IncidenceParameterPolynomialRing K] b := by
  letI := incidenceUnlocalizedParameterAlgebra M k p
  letI := incidenceMinorPolynomialAlgebra M k p
  letI := incidenceParameterSubfieldPolynomialAlgebra M k p h
  letI := incidenceGenericFiberActualParameterAlgebra h2 M hM hbase hCert k p h
  change Algebra.TensorProduct.comm (IncidenceParameterPolynomialRing K)
      (SegreIncidenceMinorLocalization M k p) (incidenceParameterSubfield M k p h)
      (incidenceGenericFiberTensorEquiv h2 M hM hbase hCert k p h
        (algebraMap (SegreIncidenceMinorLocalization M k p) (IncidenceGenericFiberRing M k p) b)) = _
  rw [incidenceGenericFiberTensorEquiv_algebraMap, Algebra.TensorProduct.comm_tmul]

/-- The actual generic-fibre ring is the previous explicit equation quotient
localized at precisely its original selected minor, over its actual parameter field. -/
def incidenceGenericFiberPresentationLocalizationEquiv :
    letI := incidenceParameterSubfieldPolynomialAlgebra M k p h
    letI := incidenceGenericFiberActualParameterAlgebra h2 M hM hbase hCert k p h
    IncidenceGenericFiberRing M k p ≃ₐ[incidenceParameterSubfield M k p h]
      Localization.Away (incidenceBaseChangedMinor (incidenceParameterSubfield M k p h) M k p) := by
  letI := incidenceUnlocalizedParameterAlgebra M k p
  letI := incidenceMinorPolynomialAlgebra M k p
  letI := incidenceMinorPolynomialScalarTower M k p
  letI := incidenceParameterSubfieldPolynomialAlgebra M k p h
  letI := incidenceGenericFiberActualParameterAlgebra h2 M hM hbase hCert k p h
  exact (incidenceGenericFiberTensorLeftEquiv h2 M hM hbase hCert k p h).trans
    ((ParameterTensorAway.tensorAwayAlgEquiv (IncidenceParameterPolynomialRing K)
      (incidenceParameterSubfield M k p h) (SegreIncidenceChartAlgebra M k p)
      (SegreIncidenceMinorLocalization M k p) (segreIncidenceChartMinor M k p)).trans
        (incidenceChartBaseChangeMinorLocalizationEquiv
          (incidenceParameterSubfield M k p h) M k p))

/-- Compatibility with every original chart element, before specializing
to individual parameter or spatial coordinates. -/
theorem incidenceGenericFiberPresentationLocalizationEquiv_chart
    (c : SegreIncidenceChartAlgebra M k p) :
    letI := incidenceUnlocalizedParameterAlgebra M k p
    letI := incidenceParameterSubfieldPolynomialAlgebra M k p h
    letI := incidenceGenericFiberActualParameterAlgebra h2 M hM hbase hCert k p h
    incidenceGenericFiberPresentationLocalizationEquiv h2 M hM hbase hCert k p h
      (algebraMap (SegreIncidenceMinorLocalization M k p) (IncidenceGenericFiberRing M k p)
        (algebraMap (SegreIncidenceChartAlgebra M k p) (SegreIncidenceMinorLocalization M k p) c)) =
      algebraMap (IncidenceBaseChangedAlgebra (incidenceParameterSubfield M k p h) M k p)
        (Localization.Away (incidenceBaseChangedMinor (incidenceParameterSubfield M k p h) M k p))
        (incidenceChartBaseChangeEquiv (incidenceParameterSubfield M k p h) M k p
          ((1 : incidenceParameterSubfield M k p h) ⊗ₜ[IncidenceParameterPolynomialRing K] c)) := by
  letI := incidenceUnlocalizedParameterAlgebra M k p
  letI := incidenceMinorPolynomialAlgebra M k p
  letI := incidenceMinorPolynomialScalarTower M k p
  letI := incidenceParameterSubfieldPolynomialAlgebra M k p h
  letI := incidenceGenericFiberActualParameterAlgebra h2 M hM hbase hCert k p h
  simp only [incidenceGenericFiberPresentationLocalizationEquiv, AlgEquiv.trans_apply,
    incidenceGenericFiberTensorLeftEquiv_algebraMap,
    ParameterTensorAway.tensorAwayAlgEquiv_tmul_algebraMap,
    incidenceChartBaseChangeMinorLocalizationEquiv_algebraMap]

/-- Every original nonpivot spatial coordinate becomes the corresponding
variable in the displayed localized equation ring. -/
@[simp] theorem incidenceGenericFiberPresentationLocalizationEquiv_spatialCoordinate
    (j : Fin 3) :
    letI := incidenceParameterSubfieldPolynomialAlgebra M k p h
    letI := incidenceGenericFiberActualParameterAlgebra h2 M hM hbase hCert k p h
    incidenceGenericFiberPresentationLocalizationEquiv h2 M hM hbase hCert k p h
      (algebraMap (SegreIncidenceMinorLocalization M k p) (IncidenceGenericFiberRing M k p)
        (algebraMap (SegreIncidenceChartAlgebra M k p) (SegreIncidenceMinorLocalization M k p)
          (Ideal.Quotient.mk _ (X (k, p.succAbove j))))) =
      algebraMap (IncidenceBaseChangedAlgebra (incidenceParameterSubfield M k p h) M k p)
        (Localization.Away (incidenceBaseChangedMinor (incidenceParameterSubfield M k p h) M k p))
        (Ideal.Quotient.mk _ (X j)) := by
  letI := incidenceUnlocalizedParameterAlgebra M k p
  letI := incidenceParameterSubfieldPolynomialAlgebra M k p h
  letI := incidenceGenericFiberActualParameterAlgebra h2 M hM hbase hCert k p h
  rw [incidenceGenericFiberPresentationLocalizationEquiv_chart,
    incidenceChartBaseChangeEquiv_spatialCoordinate]

/-- The final equation presentation preserves the original fraction-field
point and its canonical pullback to the actual generic fibre. -/
theorem incidenceGenericFiberPresentationLocalizationEquiv_parameter
    (t : IncidenceParameterChartField (K := K) k) :
    letI := incidenceParameterSubfieldPolynomialAlgebra M k p h
    letI := incidenceGenericFiberActualParameterAlgebra h2 M hM hbase hCert k p h
    incidenceGenericFiberPresentationLocalizationEquiv h2 M hM hbase hCert k p h
      (affineGenericFiberFractionMap (ProjectiveCoordinateQuotient (K := K) k)
        (SegreIncidenceMinorLocalization M k p) t) =
      algebraMap (incidenceParameterSubfield M k p h)
        (Localization.Away (incidenceBaseChangedMinor (incidenceParameterSubfield M k p h) M k p))
        (incidenceParameterChartFieldEquiv h2 M hM hbase hCert k p h t) := by
  letI := incidenceParameterSubfieldPolynomialAlgebra M k p h
  letI := incidenceGenericFiberActualParameterAlgebra h2 M hM hbase hCert k p h
  have ht : algebraMap (incidenceParameterSubfield M k p h) (IncidenceGenericFiberRing M k p)
      (incidenceParameterChartFieldEquiv h2 M hM hbase hCert k p h t) =
      affineGenericFiberFractionMap (ProjectiveCoordinateQuotient (K := K) k)
        (SegreIncidenceMinorLocalization M k p) t := by
    rw [incidenceGenericFiberActualParameterAlgebra_algebraMap, AlgEquiv.symm_apply_apply]
  rw [← ht]
  exact (incidenceGenericFiberPresentationLocalizationEquiv h2 M hM hbase hCert k p h).commutes _

end ActualParameterField
end EvenQuinticConic.Incidence
