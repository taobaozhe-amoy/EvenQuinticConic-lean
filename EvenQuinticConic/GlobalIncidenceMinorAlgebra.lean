import EvenQuinticConic.GlobalIncidenceChartIdeal
import EvenQuinticConic.SegreIncidenceLocalization
import EvenQuinticConic.QuotientLocalization

/-!
# The global minor-open equation algebra

The global normalized equation ideal and the Segre chart ideal are equal.
This equality also identifies their localizations at the literal cubic
minor. Composing with quotient-localization commutation gives the exact
algebra needed for the global projective minor open, over the original
coefficient field and without a radical-identification hypothesis.
-/

noncomputable section
namespace EvenQuinticConic.Incidence

open MvPolynomial

variable {K : Type*} [Field K]

/-- The global normalized quotient and the displayed Segre quotient differ
only by the already proved equality of their generator ideals. -/
def globalNormalizedToSegreChartAlgEquiv
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4) :
    GlobalNormalizedIncidenceAlgebra M k p ≃ₐ[K] SegreIncidenceChartAlgebra M k p :=
  Ideal.quotientEquivAlgOfEq K (globalNormalizedIncidenceIdeal_eq M k p)

@[simp] theorem globalNormalizedToSegreChartAlgEquiv_mk
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4)
    (f : MvPolynomial SegreIndex K) :
    globalNormalizedToSegreChartAlgEquiv M k p
      (Ideal.Quotient.mk (globalNormalizedIncidenceIdeal M k p) f) =
      Ideal.Quotient.mk _ f :=
  Ideal.quotientEquivAlgOfEq_mk K (globalNormalizedIncidenceIdeal_eq M k p) f

/-- The selected cubic minor in the normalized global equation algebra. -/
def globalNormalizedIncidenceMinor
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4) :
    GlobalNormalizedIncidenceAlgebra M k p :=
  Ideal.Quotient.mk (globalNormalizedIncidenceIdeal M k p)
    (globalIncidenceMinor M (k.succAbove 0) (k.succAbove 1) k)

/-- The principal localization of the literal global normalized quotient. -/
abbrev GlobalNormalizedIncidenceMinorLocalization
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4) :=
  Localization.Away (globalNormalizedIncidenceMinor M k p)

@[simp] theorem globalNormalizedToSegreChartAlgEquiv_minor
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4) :
    globalNormalizedToSegreChartAlgEquiv M k p (globalNormalizedIncidenceMinor M k p) =
      segreIncidenceChartMinor M k p :=
  globalNormalizedToSegreChartAlgEquiv_mk M k p _

/-- The actual selected-minor submonoids correspond under the quotient map. -/
theorem globalNormalizedToSegreChartAlgEquiv_minor_powers
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4) :
    (Submonoid.powers (globalNormalizedIncidenceMinor M k p)).map
      (globalNormalizedToSegreChartAlgEquiv M k p) =
      Submonoid.powers (segreIncidenceChartMinor M k p) := by
  rw [Submonoid.map_powers, globalNormalizedToSegreChartAlgEquiv_minor]

/-- The normalized global minor-open algebra is the Segre incidence
minor-open algebra, through a coefficient-field algebra isomorphism. -/
def globalNormalizedIncidenceMinorLocalizationAlgEquiv
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4) :
    GlobalNormalizedIncidenceMinorLocalization M k p ≃ₐ[K]
      SegreIncidenceMinorLocalization M k p :=
  IsLocalization.algEquivOfAlgEquiv _ _ (globalNormalizedToSegreChartAlgEquiv M k p)
    (globalNormalizedToSegreChartAlgEquiv_minor_powers M k p)

/-- The localized algebra comparison retains the original polynomial
representatives after the canonical quotient and localization maps. -/
@[simp] theorem globalNormalizedIncidenceMinorLocalizationAlgEquiv_mk
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4)
    (f : MvPolynomial SegreIndex K) :
    globalNormalizedIncidenceMinorLocalizationAlgEquiv M k p
      (algebraMap (GlobalNormalizedIncidenceAlgebra M k p)
        (GlobalNormalizedIncidenceMinorLocalization M k p)
        (Ideal.Quotient.mk _ f)) =
      algebraMap (SegreIncidenceChartAlgebra M k p)
        (SegreIncidenceMinorLocalization M k p) (Ideal.Quotient.mk _ f) := by
  rw [globalNormalizedIncidenceMinorLocalizationAlgEquiv,
    IsLocalization.algEquivOfAlgEquiv_eq, globalNormalizedToSegreChartAlgEquiv_mk]

/-- The ambient projective chart, localized at the selected minor and
then quotiented by the actual global equation ideal. -/
abbrev GlobalIncidenceAmbientMinorQuotient
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4) :=
  Localization.Away
    (Ideal.Quotient.mk (projectiveCoordinateIdeal (K := K) (k, p))
      (globalIncidenceMinor M (k.succAbove 0) (k.succAbove 1) k)) ⧸
    normalizedLocalizedEquationIdeal (Ideal.span (segreIncidenceEquationSet M))
      (projectiveCoordinateIdeal (K := K) (k, p))
      (globalIncidenceMinor M (k.succAbove 0) (k.succAbove 1) k)

/-- The actual ambient localized quotient agrees with the concrete Segre
minor algebra. Neither radicalness nor a geometric comparison is assumed. -/
def globalIncidenceAmbientMinorQuotientAlgEquiv
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4) :
    GlobalIncidenceAmbientMinorQuotient M k p ≃ₐ[K]
      SegreIncidenceMinorLocalization M k p :=
  (normalizedQuotientLocalizationAlgEquiv K (Ideal.span (segreIncidenceEquationSet M))
    (projectiveCoordinateIdeal (K := K) (k, p))
    (globalIncidenceMinor M (k.succAbove 0) (k.succAbove 1) k)).trans
      (globalNormalizedIncidenceMinorLocalizationAlgEquiv M k p)

end EvenQuinticConic.Incidence
