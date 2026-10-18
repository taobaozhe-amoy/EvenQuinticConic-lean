import EvenQuinticConic.IncidenceGenericConicGeometry
import EvenQuinticConic.IncidenceGenericFiberStalk
import EvenQuinticConic.IncidenceSpatialParameterComparison

/-!
# Function field of the actual generic plane conic

The comparison uses the actual generic-stalk map of the already constructed
open immersion. Its coefficient-field action is induced by the actual
projective structure map, and becomes the original Cramer subfield inclusion.
No rationality over the two-variable parameter field is asserted.
-/

noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option Elab.async false

namespace EvenQuinticConic

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

/-- Pullback of constants followed by a generic germ respects an actual open
immersion and an actual commuting triangle of structure maps. -/
theorem openImmersionFunctionFieldIso_baseScalar
    {K : Type*} [Field K] {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsOpenImmersion f]
    (pX : X ⟶ Spec (CommRingCat.of K))
    (pY : Y ⟶ Spec (CommRingCat.of K)) (hf : f ≫ pY = pX) (r : K) :
    letI : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
    letI : Nonempty (⊤ : Y.Opens) := ⟨⟨genericPoint Y, trivial⟩⟩
    (openImmersionFunctionFieldIso f).hom
        (Y.germToFunctionField ⊤ (schemeBaseScalarHom pY r)) =
      X.germToFunctionField ⊤ (schemeBaseScalarHom pX r) := by
  letI : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
  letI : Nonempty (⊤ : Y.Opens) := ⟨⟨genericPoint Y, trivial⟩⟩
  letI : Nonempty (f ⁻¹ᵁ (⊤ : Y.Opens)) := ⟨⟨genericPoint X, trivial⟩⟩
  rw [openImmersionFunctionFieldIso_germ_apply]
  subst pX
  rfl

/-- Composition with an actual affine field morphism restricts constants
by its displayed ring homomorphism. -/
theorem schemeBaseScalarHom_comp_spec
    {K L : Type u} [Field K] [Field L] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of L)) (g : K →+* L) (c : K) :
    schemeBaseScalarHom (K := K) (f ≫ Spec.map (CommRingCat.ofHom g)) c =
      schemeBaseScalarHom (K := L) f (g c) := by
  change f.appTop ((Spec.map (CommRingCat.ofHom g)).appTop
    ((Scheme.ΓSpecIso (CommRingCat.of K)).inv c)) =
    f.appTop ((Scheme.ΓSpecIso (CommRingCat.of L)).inv (g c))
  apply congrArg f.appTop
  exact DFunLike.congr_fun (CommRingCat.hom_ext_iff.mp
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom g)).symm) c

namespace Incidence

variable {K : Type*} [Field K] [Infinite K]
    (h2 : (2 : K) ≠ 0)
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (hM : ∀ i, (M i).IsSymm)
    (hbase : ∀ i, M i 0 0 = 0)
    (hCert : ProjectiveJacobianCertificate (linearMatrixNet M).det)
    (k : Fin 3) (p : Fin 4)
    (h : (cross (segreChartRow (netLinearRow M) k p)
      (segreChartRow (netQuadraticRow M) k p)).z ≠ 0)



variable (q : Fin 3) (hq : incidenceGenericMatrix M k p h (p.succAbove q).succ 0 ≠ 0)
    [hIntegral : IsIntegral (IncidenceGenericConicScheme M k p h q)]

local instance : Nonempty (⊤ : (IncidenceGenericConicScheme M k p h q).Opens) :=
  ⟨⟨genericPoint _, trivial⟩⟩

/-- The actual generic stalk of the whole conic maps through the actual affine
open immersion, then through the proved generic-fibre fraction-field map. -/
def incidenceGenericConicFunctionFieldRingEquiv :
    (IncidenceGenericConicScheme M k p h q).functionField ≃+*
      IncidenceSpatialFunctionField K := by
  let hInjective := incidenceParameterChartMap_injective_of_geometricJacobian
    h2 M hM hbase hCert k p h
  letI := globalIncidenceOpenGenericFiber_isIntegral_of_injective M k p h hInjective
  exact (openImmersionFunctionFieldIso
    (globalIncidenceGenericConicChartMap h2 M hM hbase hCert k p h q hq)).commRingCatIsoToRingEquiv.trans
      (globalIncidenceOpenGenericFiberStalkRingEquiv M k p h hInjective)

/-- The parameter field acts by its actual projective structure morphism. -/
def incidenceGenericConicFunctionFieldParameterMap :
    incidenceParameterSubfield M k p h →+*
      (IncidenceGenericConicScheme M k p h q).functionField :=
  ((IncidenceGenericConicScheme M k p h q).germToFunctionField ⊤).hom.comp
    (schemeBaseScalarHom (planeCurveStructure (incidenceGenericConicPolynomial M k p h q)))

/-- The parameter algebra structure is defined by pullback of constants to
the whole conic and passage to its actual generic stalk. -/
def incidenceGenericConicFunctionFieldParameterAlgebra :
    Algebra (incidenceParameterSubfield M k p h)
      (IncidenceGenericConicScheme M k p h q).functionField :=
  (incidenceGenericConicFunctionFieldParameterMap M k p h q).toAlgebra

/-- Compatibility first with the actual original parameter-chart field. -/
theorem incidenceGenericConicFunctionFieldRingEquiv_chartParameter
    (s : incidenceParameterSubfield M k p h) :
    let hInjective := incidenceParameterChartMap_injective_of_geometricJacobian
      h2 M hM hbase hCert k p h
    letI := incidenceSpatialParameterAlgebra M k p h hInjective
    incidenceGenericConicFunctionFieldRingEquiv h2 M hM hbase hCert k p h q hq
        (incidenceGenericConicFunctionFieldParameterMap M k p h q s) =
      algebraMap (IncidenceParameterChartField (K := K) k) (IncidenceSpatialFunctionField K)
        ((incidenceParameterChartFieldEquiv h2 M hM hbase hCert k p h).symm s) := by
  let hInjective := incidenceParameterChartMap_injective_of_geometricJacobian
    h2 M hM hbase hCert k p h
  letI := globalIncidenceOpenGenericFiber_isIntegral_of_injective M k p h hInjective
  letI : Nonempty (⊤ : (GlobalIncidenceOpenGenericFiber M k p h).Opens) :=
    ⟨⟨genericPoint _, trivial⟩⟩
  change globalIncidenceOpenGenericFiberStalkRingEquiv M k p h hInjective
    ((openImmersionFunctionFieldIso
      (globalIncidenceGenericConicChartMap h2 M hM hbase hCert k p h q hq)).hom
      ((IncidenceGenericConicScheme M k p h q).germToFunctionField ⊤
        (schemeBaseScalarHom (planeCurveStructure
          (incidenceGenericConicPolynomial M k p h q)) s))) = _
  rw [openImmersionFunctionFieldIso_baseScalar _ _ _
    (globalIncidenceGenericConicChartMap_comp_structure h2 M hM hbase hCert k p h q hq)]
  have he : schemeBaseScalarHom
      (pullback.snd (globalIncidenceMinorParameterProjection M k p h)
        (incidenceParameterGenericPoint (K := K) k) ≫
        (incidenceParameterChartToActualSpecIso h2 M hM hbase hCert k p h).hom) s =
      schemeBaseScalarHom
        (pullback.snd (globalIncidenceMinorParameterProjection M k p h)
          (incidenceParameterGenericPoint (K := K) k))
        ((incidenceParameterChartFieldEquiv h2 M hM hbase hCert k p h).symm s) := by
    exact schemeBaseScalarHom_comp_spec
      (pullback.snd (globalIncidenceMinorParameterProjection M k p h)
        (incidenceParameterGenericPoint (K := K) k))
      (incidenceParameterChartFieldEquiv h2 M hM hbase hCert k p h).symm.toRingHom s

  rw [he]
  change globalIncidenceOpenGenericFiberStalkRingEquiv M k p h hInjective
    (globalIncidenceOpenGenericFiberStalkParameterMap M k p h hInjective
      ((incidenceParameterChartFieldEquiv h2 M hM hbase hCert k p h).symm s)) = _
  exact globalIncidenceOpenGenericFiberStalkRingEquiv_parameter M k p h hInjective _

/-- The generic-stalk comparison sends every parameter constant to its
actual Cramer value in the spatial rational function field. -/
theorem incidenceGenericConicFunctionFieldRingEquiv_parameter
    (s : incidenceParameterSubfield M k p h) :
    incidenceGenericConicFunctionFieldRingEquiv h2 M hM hbase hCert k p h q hq
        (incidenceGenericConicFunctionFieldParameterMap M k p h q s) =
      algebraMap (incidenceParameterSubfield M k p h) (IncidenceSpatialFunctionField K) s := by
  rw [incidenceGenericConicFunctionFieldRingEquiv_chartParameter h2 M hM hbase hCert k p h q hq s,
    incidenceSpatialParameterAlgebra_eq_actual h2 M hM hbase hCert k p h,
    AlgEquiv.apply_symm_apply]

/-- This is an equivalence over the actual Cramer parameter subfield. It
asserts no one-variable rational parametrization over that field. -/
def incidenceGenericConicFunctionFieldEquiv_overParameter :
    letI := incidenceGenericConicFunctionFieldParameterAlgebra M k p h q
    (IncidenceGenericConicScheme M k p h q).functionField
      ≃ₐ[incidenceParameterSubfield M k p h] IncidenceSpatialFunctionField K := by
  letI := incidenceGenericConicFunctionFieldParameterAlgebra M k p h q
  refine { incidenceGenericConicFunctionFieldRingEquiv h2 M hM hbase hCert k p h q hq with
    commutes' := ?_ }
  exact incidenceGenericConicFunctionFieldRingEquiv_parameter h2 M hM hbase hCert k p h q hq

/-- The original ground structure of the actual projective conic. -/
def incidenceGenericConicGroundStructure :
    IncidenceGenericConicScheme M k p h q ⟶ Spec (CommRingCat.of K) :=
  planeCurveStructure (incidenceGenericConicPolynomial M k p h q) ≫
    Spec.map (CommRingCat.ofHom (algebraMap K (incidenceParameterSubfield M k p h)))

/-- Ground scalars also use their actual scheme structure morphism. -/
def incidenceGenericConicFunctionFieldGroundMap :
    K →+* (IncidenceGenericConicScheme M k p h q).functionField :=
  ((IncidenceGenericConicScheme M k p h q).germToFunctionField ⊤).hom.comp
    (schemeBaseScalarHom (incidenceGenericConicGroundStructure M k p h q))

omit [Infinite K] in
/-- The actual ground-field map is the restriction of the actual parameter map. -/
theorem incidenceGenericConicFunctionFieldGroundMap_eq_parameter (c : K) :
    incidenceGenericConicFunctionFieldGroundMap M k p h q c =
      incidenceGenericConicFunctionFieldParameterMap M k p h q
        (algebraMap K (incidenceParameterSubfield M k p h) c) := by
  unfold incidenceGenericConicFunctionFieldGroundMap
    incidenceGenericConicFunctionFieldParameterMap
  simp only [RingHom.comp_apply, incidenceGenericConicGroundStructure,
    schemeBaseScalarHom_comp_spec]

/-- The ground-field algebra structure is induced by the actual structure. -/
def incidenceGenericConicFunctionFieldGroundAlgebra :
    Algebra K (IncidenceGenericConicScheme M k p h q).functionField :=
  (incidenceGenericConicFunctionFieldGroundMap M k p h q).toAlgebra

/-- The whole actual conic has the same three-variable rational function
field over the original ground field as its actual nonempty incidence open. -/
def incidenceGenericConicFunctionFieldEquiv_overGround :
    letI := incidenceGenericConicFunctionFieldGroundAlgebra M k p h q
    (IncidenceGenericConicScheme M k p h q).functionField ≃ₐ[K]
      IncidenceSpatialFunctionField K := by
  letI := incidenceGenericConicFunctionFieldGroundAlgebra M k p h q
  refine { incidenceGenericConicFunctionFieldRingEquiv h2 M hM hbase hCert k p h q hq with
    commutes' := ?_ }
  intro c
  change incidenceGenericConicFunctionFieldRingEquiv h2 M hM hbase hCert k p h q hq
    (incidenceGenericConicFunctionFieldGroundMap M k p h q c) = _
  rw [incidenceGenericConicFunctionFieldGroundMap_eq_parameter,
    incidenceGenericConicFunctionFieldRingEquiv_parameter]
  exact (IsScalarTower.algebraMap_apply K (incidenceParameterSubfield M k p h)
    (IncidenceSpatialFunctionField K) c).symm


omit hIntegral in
/-- Matrix-net geometry supplies integrality internally. The actual whole
conic's generic stalk is identified over its actual Cramer parameter field. -/
def incidenceGenericConicFunctionFieldEquiv_overParameter_of_geometricJacobian :
    letI := incidenceGenericConicScheme_isIntegral h2 M hM hbase hCert k p h q hq
    letI := incidenceGenericConicFunctionFieldParameterAlgebra M k p h q
    (IncidenceGenericConicScheme M k p h q).functionField
      ≃ₐ[incidenceParameterSubfield M k p h] IncidenceSpatialFunctionField K := by
  letI := incidenceGenericConicScheme_isIntegral h2 M hM hbase hCert k p h q hq
  exact incidenceGenericConicFunctionFieldEquiv_overParameter h2 M hM hbase hCert k p h q hq

omit hIntegral in
/-- The actual whole conic's function field is rational over the original
K. Both its integrality and the field comparison are proved, not inputs. -/
def incidenceGenericConicFunctionFieldEquiv_overGround_of_geometricJacobian :
    letI := incidenceGenericConicScheme_isIntegral h2 M hM hbase hCert k p h q hq
    letI := incidenceGenericConicFunctionFieldGroundAlgebra M k p h q
    (IncidenceGenericConicScheme M k p h q).functionField ≃ₐ[K]
      IncidenceSpatialFunctionField K := by
  letI := incidenceGenericConicScheme_isIntegral h2 M hM hbase hCert k p h q hq
  exact incidenceGenericConicFunctionFieldEquiv_overGround h2 M hM hbase hCert k p h q hq

end Incidence
end EvenQuinticConic
