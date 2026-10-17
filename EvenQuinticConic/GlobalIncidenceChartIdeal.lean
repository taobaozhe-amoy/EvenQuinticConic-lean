import EvenQuinticConic.GlobalIncidenceScheme
import EvenQuinticConic.SegreIncidenceChartAlgebra
import EvenQuinticConic.ProjectiveCoordinateQuotient

/-!
# The global incidence equations in a normalized Segre chart

This compares the literal homogeneous generators of the global projective
incidence with the actual quotient algebra obtained by setting `z_(k,p)=1`.
No radical is inserted or discarded: the displayed algebra isomorphism
retains the scheme structure of the generated ideal.
-/

noncomputable section
namespace EvenQuinticConic.Incidence

open MvPolynomial SegreChart

variable {K : Type*} [Field K]

/-- The global homogeneous equations are precisely all Segre minors
together with the one linear and three quadratic incidence equations. -/
theorem segreIncidenceEquationSet_eq
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) :
    segreIncidenceEquationSet M =
      Set.range (fun q : (Fin 3 × Fin 3) × (Fin 4 × Fin 4) =>
        segreMinor K q.1.1 q.1.2 q.2.1 q.2.2) ∪ segreExtraIncidenceEquationSet M := by
  ext f
  constructor
  · rintro ⟨e, rfl⟩
    cases e with
    | minor i j a b => exact Or.inl ⟨((i, j), (a, b)), rfl⟩
    | linear => exact Or.inr (Or.inl (Set.mem_singleton _))
    | quad k => exact Or.inr (Or.inr ⟨k, rfl⟩)
  · rintro (⟨⟨⟨i, j⟩, a, b⟩, rfl⟩ | h)
    · exact ⟨.minor i j a b, rfl⟩
    · rcases h with h | ⟨k, rfl⟩
      · rcases Set.mem_singleton_iff.mp h with rfl
        exact ⟨.linear, rfl⟩
      · exact ⟨.quad k, rfl⟩

/-- Normalizing one projective coordinate in the literal global equations. -/
def globalNormalizedIncidenceIdeal (M : Fin 3 → Matrix (Fin 5) (Fin 5) K)
    (k : Fin 3) (p : Fin 4) : Ideal (MvPolynomial SegreIndex K) :=
  Ideal.span (segreIncidenceEquationSet M) ⊔ Ideal.span {X (k, p) - 1}

/-- The normalized global generators equal the chart ideal used by the
explicit coordinate isomorphism. This is an equality of ideals, not radicals. -/
theorem globalNormalizedIncidenceIdeal_eq
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4) :
    globalNormalizedIncidenceIdeal M k p =
      segreChartIdeal K k p ⊔ Ideal.span (segreExtraIncidenceEquationSet M) := by
  rw [globalNormalizedIncidenceIdeal, segreIncidenceEquationSet_eq,
    segreChartIdeal, Ideal.span_union, Ideal.span_union]
  ac_rfl

/-- The normalized quotient by all global incidence equations. -/
abbrev GlobalNormalizedIncidenceAlgebra
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4) :=
  MvPolynomial SegreIndex K ⧸ globalNormalizedIncidenceIdeal M k p

/-- The literal normalized global equation algebra is the two-equation
incidence algebra in two variables over the three-coordinate base chart. -/
def globalNormalizedIncidenceAlgEquiv
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4) :
    GlobalNormalizedIncidenceAlgebra M k p ≃ₐ[K]
      AffineIncidenceAlgebra (segreChartRow (netLinearRow M) k p)
        (segreChartRow (netQuadraticRow M) k p) :=
  (Ideal.quotientEquivAlgOfEq K (globalNormalizedIncidenceIdeal_eq M k p)).trans
    (segreIncidenceChartAlgEquiv M k p)

/-- On a polynomial representative the ideal comparison does not change
the input of the explicit Segre incidence chart isomorphism. -/
theorem globalNormalizedIncidenceAlgEquiv_mk_eq
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4)
    (f : MvPolynomial SegreIndex K) :
    globalNormalizedIncidenceAlgEquiv M k p
      (Ideal.Quotient.mk (globalNormalizedIncidenceIdeal M k p) f) =
    segreIncidenceChartAlgEquiv M k p (Ideal.Quotient.mk _ f) := by
  unfold globalNormalizedIncidenceAlgEquiv
  rw [AlgEquiv.trans_apply, Ideal.quotientEquivAlgOfEq_mk]


/-- The literal global equations in the actual standard projective chart,
whose coefficient ring is obtained by imposing the pivot relation. -/
def globalProjectiveChartEquationIdeal
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4) :
    Ideal (ProjectiveCoordinateQuotient (K := K) (k, p)) :=
  (Ideal.span (segreIncidenceEquationSet M)).map
    (Ideal.Quotient.mk (projectiveCoordinateIdeal (K := K) (k, p)))

/-- Taking the projective chart first and then imposing the global equations
gives exactly the same normalized quotient as imposing both sets at once. -/
def globalProjectiveChartQuotientAlgEquiv
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4) :
    (ProjectiveCoordinateQuotient (K := K) (k, p) ⧸
      globalProjectiveChartEquationIdeal M k p) ≃ₐ[K]
      GlobalNormalizedIncidenceAlgebra M k p :=
  (DoubleQuot.quotQuotEquivQuotSupₐ K (projectiveCoordinateIdeal (K := K) (k, p))
    (Ideal.span (segreIncidenceEquationSet M))).trans
      (Ideal.quotientEquivAlgOfEq K (sup_comm _ _))

/-- The double-quotient comparison keeps the original homogeneous polynomial
representative. -/
@[simp] theorem globalProjectiveChartQuotientAlgEquiv_mk_mk
    (M : Fin 3 → Matrix (Fin 5) (Fin 5) K) (k : Fin 3) (p : Fin 4)
    (f : MvPolynomial SegreIndex K) :
    globalProjectiveChartQuotientAlgEquiv M k p
      (Ideal.Quotient.mk (globalProjectiveChartEquationIdeal M k p)
        (Ideal.Quotient.mk (projectiveCoordinateIdeal (K := K) (k, p)) f)) =
      Ideal.Quotient.mk (globalNormalizedIncidenceIdeal M k p) f := by
  change (Ideal.quotientEquivAlgOfEq K (sup_comm
      (projectiveCoordinateIdeal (K := K) (k, p))
      (Ideal.span (segreIncidenceEquationSet M))))
    (DoubleQuot.quotQuotEquivQuotSup (projectiveCoordinateIdeal (K := K) (k, p))
      (Ideal.span (segreIncidenceEquationSet M))
      (DoubleQuot.quotQuotMk (projectiveCoordinateIdeal (K := K) (k, p))
        (Ideal.span (segreIncidenceEquationSet M)) f)) = _
  rw [DoubleQuot.quotQuotEquivQuotSup_quotQuotMk, Ideal.quotientEquivAlgOfEq_mk]
  rfl

end EvenQuinticConic.Incidence
