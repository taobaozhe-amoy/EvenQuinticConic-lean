import EvenQuinticConic.PlaneConicAffineChart
import EvenQuinticConic.IncidenceGenericFiberLocalizationComparison
import EvenQuinticConic.IncidenceGenericFiberElimination
import EvenQuinticConic.IncidenceConicDehomogenization
import EvenQuinticConic.IncidenceGenericFiberFunctionField

/-!
# The actual generic incidence fibre as an open of its plane conic

The equations, coefficient-field identification, linear elimination, selected
minor, and actual projective affine chart are composed here.  Reducedness is
derived only for the actual localized equation algebra, from the already
proved integrality of the actual generic fibre.  The two presentations of the
parameter field remain distinct and their scheme isomorphism is explicit.
-/

noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace EvenQuinticConic.Incidence

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial

variable {K : Type*} [Field K]

section Equations

variable (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4)
    (h : (cross (segreChartRow (netLinearRow M) k p)
      (segreChartRow (netQuadraticRow M) k p)).z ≠ 0) (q : Fin 3)

/-- The actual homogeneous ternary polynomial after eliminating the chosen
polar coordinate, over the actual Cramer-generated parameter subfield. -/
def incidenceGenericConicPolynomial :
    PlanePolynomial (incidenceParameterSubfield M k p h) :=
  matrixQuadraticPolynomial (incidenceGenericConicMatrix M k p h (p.succAbove q))

/-- The projective conic is the actual reduced projective plane locus of
the displayed ternary polynomial. -/
abbrev IncidenceGenericConicScheme :=
  PlaneCurveScheme (incidenceGenericConicPolynomial M k p h q)

/-- The actual selected incidence minor after the same affine elimination. -/
def incidenceGenericConicMinorPolynomial :
    MvPolynomial (Fin 2) (incidenceParameterSubfield M k p h) :=
  affineEliminationSubstitution (incidenceGenericAffineLinearCoefficients M k p h)
    (incidenceGenericAffineLinearConstant M k p h) q
    (MvPolynomial.map (algebraMap K (incidenceParameterSubfield M k p h))
      (netDehomogenizedMinor M p (k.succAbove 0) (k.succAbove 1)))

/-- The residual equation is literally the chosen standard affine equation
of the actual ternary conic, in the retained coordinates' original order. -/
theorem incidenceGenericResidualPolynomial_eq_conicDehomogenization :
    incidenceGenericResidualPolynomial M k p h q =
      dehomogenizeAt (q.predAbove p) (incidenceGenericConicPolynomial M k p h q) := by
  exact incidenceGenericConicMatrix_dehomogenize M k p h q

/-- The residual quotient and the displayed affine conic quotient differ
only by the proved equality of their equations. -/
def incidenceGenericResidualConicQuotientEquiv :
    IncidenceGenericResidualAlgebra M k p h q
      ≃ₐ[incidenceParameterSubfield M k p h]
        (MvPolynomial (Fin 2) (incidenceParameterSubfield M k p h) ⧸
          Ideal.span {dehomogenizeAt (q.predAbove p)
            (incidenceGenericConicPolynomial M k p h q)}) :=
  Ideal.quotientEquivAlgOfEq _ (by
    rw [incidenceGenericResidualPolynomial_eq_conicDehomogenization])

/-- The polynomial identity also preserves the literal selected minor. -/
@[simp] theorem incidenceGenericResidualConicQuotientEquiv_minor :
    incidenceGenericResidualConicQuotientEquiv M k p h q
        (incidenceGenericResidualMinor M k p h q) =
      Ideal.Quotient.mk _ (incidenceGenericConicMinorPolynomial M k p h q) :=
  Ideal.quotientEquivAlgOfEq_mk _ _ _

/-- The actual minor localizations agree by the same equation identity. -/
private def conicAwayAlgEquivOfElementEq
    {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (e : A ≃ₐ[R] B) (a : A) (b : B) (he : e a = b) :
    Localization.Away a ≃ₐ[R] Localization.Away b :=
  IsLocalization.algEquivOfAlgEquiv
    (M := Submonoid.powers a) (T := Submonoid.powers b)
    (Localization.Away a) (Localization.Away b) e
    ((Submonoid.map_powers e a).trans (congrArg Submonoid.powers he))

/-- The actual minor localizations agree by the same equation identity. -/
def incidenceGenericResidualConicMinorEquiv :
    Localization.Away (incidenceGenericResidualMinor M k p h q)
      ≃ₐ[incidenceParameterSubfield M k p h]
        PlaneEquationMinorAlgebra (incidenceGenericConicPolynomial M k p h q)
          (q.predAbove p) (incidenceGenericConicMinorPolynomial M k p h q) := by
  exact conicAwayAlgEquivOfElementEq
    (incidenceGenericResidualConicQuotientEquiv M k p h q)
    (incidenceGenericResidualMinor M k p h q)
    (Ideal.Quotient.mk _ (incidenceGenericConicMinorPolynomial M k p h q))
    (incidenceGenericResidualConicQuotientEquiv_minor M k p h q)

end Equations

private theorem conicIsReducedOfDomain (R : Type*) [CommRing R] (hR : IsDomain R) :
    _root_.IsReduced R := by
  letI := hR
  infer_instance

section Geometric

variable [Infinite K] (h2 : (2 : K) ≠ 0)
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (hM : ∀ i, (M i).IsSymm)
    (hbase : ∀ i, M i 0 0 = 0)
    (hCert : ProjectiveJacobianCertificate (linearMatrixNet M).det)
    (k : Fin 3) (p : Fin 4)
    (h : (cross (segreChartRow (netLinearRow M) k p)
      (segreChartRow (netQuadraticRow M) k p)).z ≠ 0)
    (q : Fin 3) (hq : incidenceGenericMatrix M k p h (p.succAbove q).succ 0 ≠ 0)

/-- The two actual parameter fields are related by their proved field
isomorphism; they are not identified by a change of notation. -/
def incidenceParameterChartToActualSpecIso :
    Spec (CommRingCat.of (IncidenceParameterChartField (K := K) k)) ≅
      Spec (CommRingCat.of (incidenceParameterSubfield M k p h)) :=
  Scheme.Spec.mapIso (incidenceParameterChartFieldEquiv
    h2 M hM hbase hCert k p h).symm.toRingEquiv.toCommRingCatIso.op

/-- The original generic-fibre ring is the literal localized standard
affine equation algebra of the actual ternary conic, over its actual
parameter subfield. -/
def incidenceGenericFiberConicAlgebraEquiv :
    letI := incidenceGenericFiberActualParameterAlgebra h2 M hM hbase hCert k p h
    IncidenceGenericFiberRing M k p ≃ₐ[incidenceParameterSubfield M k p h]
      PlaneEquationMinorAlgebra (incidenceGenericConicPolynomial M k p h q)
        (q.predAbove p) (incidenceGenericConicMinorPolynomial M k p h q) := by
  letI := incidenceParameterSubfieldPolynomialAlgebra M k p h
  letI := incidenceGenericFiberActualParameterAlgebra h2 M hM hbase hCert k p h
  exact (incidenceGenericFiberPresentationLocalizationEquiv h2 M hM hbase hCert k p h).trans
    ((incidenceGenericFiberEliminationMinorEquiv M k p h q hq).trans
      (incidenceGenericResidualConicMinorEquiv M k p h q))

include h2 hM hbase hCert hq in
/-- Integrality is transferred from the actual generic fibre. No global
irreducibility or radicality of the projective equation is an input. -/
theorem incidenceGenericConicMinorAlgebra_isDomain :
    IsDomain (PlaneEquationMinorAlgebra (incidenceGenericConicPolynomial M k p h q)
      (q.predAbove p) (incidenceGenericConicMinorPolynomial M k p h q)) := by
  let hInjective := incidenceParameterChartMap_injective_of_geometricJacobian
    h2 M hM hbase hCert k p h
  letI := incidenceGenericFiberRing_isDomain_of_injective M k p h hInjective
  letI := incidenceGenericFiberActualParameterAlgebra h2 M hM hbase hCert k p h
  exact Function.Injective.isDomain
    (incidenceGenericFiberConicAlgebraEquiv h2 M hM hbase hCert k p h q hq).symm
    (incidenceGenericFiberConicAlgebraEquiv h2 M hM hbase hCert k p h q hq).symm.injective

/-- The actual localization spectrum maps into the actual projective conic
by the specified equation chart. -/
def incidenceGenericFiberConicChartMap :
    Spec (CommRingCat.of (IncidenceGenericFiberRing M k p)) ⟶
      IncidenceGenericConicScheme M k p h q := by
  letI := incidenceGenericFiberActualParameterAlgebra h2 M hM hbase hCert k p h
  letI := incidenceGenericConicMinorAlgebra_isDomain h2 M hM hbase hCert k p h q hq
  letI := conicIsReducedOfDomain _
    (incidenceGenericConicMinorAlgebra_isDomain h2 M hM hbase hCert k p h q hq)
  exact (Scheme.Spec.mapIso
    (incidenceGenericFiberConicAlgebraEquiv h2 M hM hbase hCert k p h q hq).symm.toRingEquiv.toCommRingCatIso.op).hom ≫
    planeEquationMinorChartMap (incidenceGenericConicPolynomial M k p h q) 2
      (matrixQuadraticPolynomial_homogeneous _) (by decide) (q.predAbove p)
      (incidenceGenericConicMinorPolynomial M k p h q)

instance incidenceGenericFiberConicChartMap_isOpenImmersion :
    IsOpenImmersion (incidenceGenericFiberConicChartMap h2 M hM hbase hCert k p h q hq) := by
  letI := incidenceGenericFiberActualParameterAlgebra h2 M hM hbase hCert k p h
  letI := incidenceGenericConicMinorAlgebra_isDomain h2 M hM hbase hCert k p h q hq
  letI := conicIsReducedOfDomain _
    (incidenceGenericConicMinorAlgebra_isDomain h2 M hM hbase hCert k p h q hq)
  unfold incidenceGenericFiberConicChartMap
  infer_instance

/-- On the affine model the structure map is the original generic-fibre
parameter map composed with the inverse of the actual field equivalence. -/
@[reassoc]
theorem incidenceGenericFiberConicChartMap_comp_structure :
    incidenceGenericFiberConicChartMap h2 M hM hbase hCert k p h q hq ≫
        planeCurveStructure (incidenceGenericConicPolynomial M k p h q) =
      Spec.map (CommRingCat.ofHom
        ((affineGenericFiberFractionMap (ProjectiveCoordinateQuotient (K := K) k)
          (SegreIncidenceMinorLocalization M k p)).comp
          (incidenceParameterChartFieldEquiv h2 M hM hbase hCert k p h).symm.toRingHom)) := by
  letI := incidenceGenericFiberActualParameterAlgebra h2 M hM hbase hCert k p h
  letI := incidenceGenericConicMinorAlgebra_isDomain h2 M hM hbase hCert k p h q hq
  letI := conicIsReducedOfDomain _
    (incidenceGenericConicMinorAlgebra_isDomain h2 M hM hbase hCert k p h q hq)
  change (Spec.map (CommRingCat.ofHom
      (incidenceGenericFiberConicAlgebraEquiv h2 M hM hbase hCert k p h q hq).symm.toRingHom) ≫
    planeEquationMinorChartMap (incidenceGenericConicPolynomial M k p h q) 2
      (matrixQuadraticPolynomial_homogeneous _) (by decide) (q.predAbove p)
      (incidenceGenericConicMinorPolynomial M k p h q)) ≫ _ = _
  rw [Category.assoc, planeEquationMinorChartMap_comp_structure, ← Spec.map_comp]
  congr 1
  ext z
  exact (incidenceGenericFiberConicAlgebraEquiv h2 M hM hbase hCert k p h q hq).symm.commutes z

/-- The actual categorical generic fibre maps to the conic through its
already proved actual affine-model isomorphism. -/
def globalIncidenceGenericConicChartMap :
    GlobalIncidenceOpenGenericFiber M k p h ⟶ IncidenceGenericConicScheme M k p h q :=
  (globalIncidenceOpenGenericFiberIso M k p h).hom ≫
    incidenceGenericFiberConicChartMap h2 M hM hbase hCert k p h q hq

instance globalIncidenceGenericConicChartMap_isOpenImmersion :
    IsOpenImmersion (globalIncidenceGenericConicChartMap h2 M hM hbase hCert k p h q hq) := by
  letI := incidenceGenericFiberConicChartMap_isOpenImmersion h2 M hM hbase hCert k p h q hq
  unfold globalIncidenceGenericConicChartMap
  infer_instance

/-- The actual second projection of the generic fibre is retained.  The
explicit `Spec` isomorphism changes from the quotient-chart parameter field
to the Cramer-generated field used in the conic equation. -/
@[reassoc]
theorem globalIncidenceGenericConicChartMap_comp_structure :
    globalIncidenceGenericConicChartMap h2 M hM hbase hCert k p h q hq ≫
        planeCurveStructure (incidenceGenericConicPolynomial M k p h q) =
      pullback.snd (globalIncidenceMinorParameterProjection M k p h)
        (incidenceParameterGenericPoint (K := K) k) ≫
        (incidenceParameterChartToActualSpecIso h2 M hM hbase hCert k p h).hom := by
  rw [globalIncidenceGenericConicChartMap, Category.assoc,
    incidenceGenericFiberConicChartMap_comp_structure]
  change (globalIncidenceOpenGenericFiberIso M k p h).hom ≫
    Spec.map (CommRingCat.ofHom
      ((affineGenericFiberFractionMap (ProjectiveCoordinateQuotient (K := K) k)
        (SegreIncidenceMinorLocalization M k p)).comp
        (incidenceParameterChartFieldEquiv h2 M hM hbase hCert k p h).symm.toRingHom)) = _
  rw [show CommRingCat.ofHom
      ((affineGenericFiberFractionMap (ProjectiveCoordinateQuotient (K := K) k)
        (SegreIncidenceMinorLocalization M k p)).comp
        (incidenceParameterChartFieldEquiv h2 M hM hbase hCert k p h).symm.toRingHom) =
      CommRingCat.ofHom (incidenceParameterChartFieldEquiv h2 M hM hbase hCert k p h).symm.toRingHom ≫
        CommRingCat.ofHom (affineGenericFiberFractionMap
          (ProjectiveCoordinateQuotient (K := K) k) (SegreIncidenceMinorLocalization M k p)) from rfl,
    Spec.map_comp, ← Category.assoc]
  change ((globalIncidenceOpenGenericFiberIso M k p h).hom ≫
    incidenceGenericFiberToParameter M k p) ≫ _ = _
  rw [← globalIncidenceOpenGenericFiberIso_inv_snd, Iso.hom_inv_id_assoc]
  rfl

/-- Returning from the conic coefficient field to the original chart field
recovers the actual original second projection exactly. -/
@[reassoc]
theorem globalIncidenceGenericConicChartMap_comp_originalParameter :
    globalIncidenceGenericConicChartMap h2 M hM hbase hCert k p h q hq ≫
      planeCurveStructure (incidenceGenericConicPolynomial M k p h q) ≫
      (incidenceParameterChartToActualSpecIso h2 M hM hbase hCert k p h).inv =
        pullback.snd (globalIncidenceMinorParameterProjection M k p h)
          (incidenceParameterGenericPoint (K := K) k) := by
  rw [← Category.assoc, globalIncidenceGenericConicChartMap_comp_structure,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- Its actual image is a genuine open subscheme of the actual conic. -/
def globalIncidenceGenericConicOpen : (IncidenceGenericConicScheme M k p h q).Opens :=
  (globalIncidenceGenericConicChartMap h2 M hM hbase hCert k p h q hq).opensRange

/-- The actual generic fibre is isomorphic to this specific conic open. -/
def globalIncidenceGenericConicOpenIso :
    GlobalIncidenceOpenGenericFiber M k p h ≅
      (globalIncidenceGenericConicOpen h2 M hM hbase hCert k p h q hq).toScheme := by
  letI := globalIncidenceGenericConicChartMap_isOpenImmersion h2 M hM hbase hCert k p h q hq
  exact (globalIncidenceGenericConicChartMap h2 M hM hbase hCert k p h q hq).isoOpensRange

/-- The isomorphism to the actual open respects its actual inclusion in
the conic, rather than merely giving an abstract affine isomorphism. -/
@[reassoc]
theorem globalIncidenceGenericConicOpenIso_hom_ι :
    (globalIncidenceGenericConicOpenIso h2 M hM hbase hCert k p h q hq).hom ≫
      (globalIncidenceGenericConicOpen h2 M hM hbase hCert k p h q hq).ι =
        globalIncidenceGenericConicChartMap h2 M hM hbase hCert k p h q hq :=
  Scheme.Hom.isoOpensRange_hom_ι _

theorem globalIncidenceGenericConicOpen_nonempty :
    Nonempty (globalIncidenceGenericConicOpen h2 M hM hbase hCert k p h q hq) := by
  let hInjective := incidenceParameterChartMap_injective_of_geometricJacobian
    h2 M hM hbase hCert k p h
  have hX := globalIncidenceOpenGenericFiber_nonempty_of_injective M k p h hInjective
  exact Nonempty.map (globalIncidenceGenericConicOpenIso h2 M hM hbase hCert k p h q hq).hom.base hX

/-- The geometric hypotheses supply the affine polar pivot, the actual
nonsingular ternary matrix, and the actual nonempty conic open isomorphic
to the genuine generic fibre. No reducedness, integrality, pivot or
comparison isomorphism is an additional hypothesis. -/
theorem exists_globalIncidenceGenericConicChart :
    ∃ q : Fin 3,
      ∃ hq : incidenceGenericMatrix M k p h (p.succAbove q).succ 0 ≠ 0,
        (incidenceGenericConicMatrix M k p h (p.succAbove q)).IsSymm ∧
        (incidenceGenericConicMatrix M k p h (p.succAbove q)).det ≠ 0 ∧
        IsOpenImmersion (globalIncidenceGenericConicChartMap h2 M hM hbase hCert k p h q hq) ∧
        Nonempty (globalIncidenceGenericConicOpen h2 M hM hbase hCert k p h q hq) ∧
        Nonempty (GlobalIncidenceOpenGenericFiber M k p h ≅
          (globalIncidenceGenericConicOpen h2 M hM hbase hCert k p h q hq).toScheme) ∧
        globalIncidenceGenericConicChartMap h2 M hM hbase hCert k p h q hq ≫
            planeCurveStructure (incidenceGenericConicPolynomial M k p h q) =
          pullback.snd (globalIncidenceMinorParameterProjection M k p h)
            (incidenceParameterGenericPoint (K := K) k) ≫
            (incidenceParameterChartToActualSpecIso h2 M hM hbase hCert k p h).hom := by
  obtain ⟨q, hq, hsymm, hdet⟩ := exists_incidenceGenericConicMatrix_nondegenerate_affine
    h2 M hM hbase hCert k p h
  exact ⟨q, hq, hsymm, hdet, inferInstance,
    globalIncidenceGenericConicOpen_nonempty h2 M hM hbase hCert k p h q hq,
    ⟨globalIncidenceGenericConicOpenIso h2 M hM hbase hCert k p h q hq⟩,
    globalIncidenceGenericConicChartMap_comp_structure h2 M hM hbase hCert k p h q hq⟩

end Geometric

/-- Starting with an arbitrary nonzero actual common isotropic point, the
normalization, parameter/spatial charts, nonzero minor, nonsingular ternary
conic, and nonempty open-immersion comparison are all constructed. -/
theorem exists_genericConicOpen_of_common_point
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
          (incidenceGenericConicMatrix (matrixNetCongruence M B) k p h (p.succAbove q)).IsSymm ∧
          (incidenceGenericConicMatrix (matrixNetCongruence M B) k p h (p.succAbove q)).det ≠ 0 ∧
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
  exact ⟨B, hB, hcol, k, p, h, q, hsymm, hdet,
    globalIncidenceGenericConicChartMap h2 (matrixNetCongruence M B)
      hSymm hbase hJac k p h q hq,
    hopen, hnonempty, hiso⟩

end EvenQuinticConic.Incidence
