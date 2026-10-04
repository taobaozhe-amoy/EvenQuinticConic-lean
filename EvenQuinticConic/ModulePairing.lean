import EvenQuinticConic.ModuleGenericInjection
import EvenQuinticConic.RankOnePairing

/-!
# Natural bilinear pairings on actual module sheaves

A pairing is given on actual modules of sections and commutes with the
actual restriction maps. Local tensor-perfectness will be used only on
framed opens, not asserted for the tensor product of global sections.
-/

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace EvenQuinticConic

variable {X : Scheme.{u}}

local instance [IsIntegral X] : Nonempty (⊤ : X.Opens) :=
  ⟨⟨genericPoint X, trivial⟩⟩

/-- A natural bilinear pairing of actual module sheaves. -/
structure ModuleSheafPairing (M N P : X.Modules) where
  app : ∀ U : X.Opens, M.val.obj (op U) →ₗ[Γ(X, U)]
    N.val.obj (op U) →ₗ[Γ(X, U)] P.val.obj (op U)
  naturality : ∀ (U V : X.Opens) (hVU : V ≤ U)
    (s : M.val.obj (op U)) (t : N.val.obj (op U)),
    P.val.map (homOfLE hVU).op (app U s t) =
      app V (M.val.map (homOfLE hVU).op s) (N.val.map (homOfLE hVU).op t)

namespace ModuleSheafPairing

variable {M N P : X.Modules} (μ : ModuleSheafPairing M N P)

/-- Applying a natural pairing to genuine compatible section families gives
another genuine compatible section family. -/
def sections (s : M.sections) (t : N.sections) : P.sections :=
  PresheafOfModules.sectionsMk
    (fun U => μ.app U.unop (s.eval U) (t.eval U)) (by
      intro U V f
      change P.val.map f (μ.app U.unop (s.eval U) (t.eval U)) =
        μ.app V.unop (s.eval V) (t.eval V)
      have hf : (homOfLE f.unop.le).op = f := Subsingleton.elim _ _
      have h := μ.naturality U.unop V.unop f.unop.le (s.eval U) (t.eval U)
      simpa only [hf, PresheafOfModules.sections_property] using h)

@[simp]
theorem sections_eval (s : M.sections) (t : N.sections) (U : X.Opens) :
    (μ.sections s t).eval (op U) = μ.app U (s.eval (op U)) (t.eval (op U)) := rfl

end ModuleSheafPairing

section SquarePairing

variable {M P : X.Modules} (μ : ModuleSheafPairing M M P)

/-- A local frame coordinate, explicitly viewed in the actual structure ring. -/
noncomputable def moduleFrameCoordinate {Q : X.Modules} (U : X.Opens)
    (e : ModuleSheafFrame Q U) (s : Q.val.obj (op U)) : Γ(X, U) :=
  e.coordinate U le_rfl s

/-- The coefficient of a square pairing in actual local frames. -/
noncomputable def modulePairingCoefficient (U : X.Opens)
    (m : ModuleSheafFrame M U) (p : ModuleSheafFrame P U) : Γ(X, U) :=
  p.coordinate U le_rfl (μ.app U
    ((m.coordinate U le_rfl).symm 1) ((m.coordinate U le_rfl).symm 1))

/-- The actual bilinear pairing becomes multiplication by its computed
coefficient in rank-one coordinates. -/
theorem modulePairing_apply (U : X.Opens)
    (m : ModuleSheafFrame M U) (p : ModuleSheafFrame P U)
    (s t : M.val.obj (op U)) :
    moduleFrameCoordinate U p (μ.app U s t) =
      modulePairingCoefficient μ U m p * moduleFrameCoordinate U m s *
        moduleFrameCoordinate U m t :=
  rankOnePairing_apply (A := Γ(X, U)) (m.coordinate U le_rfl) (p.coordinate U le_rfl) (μ.app U) s t

/-- The computed coefficient is a unit if the genuine local tensor map of
the pairing is bijective. This is a local condition on a framed open. -/
theorem modulePairingCoefficient_isUnit (U : X.Opens)
    (m : ModuleSheafFrame M U) (p : ModuleSheafFrame P U)
    (hμ : Function.Bijective (TensorProduct.lift (μ.app U))) :
    IsUnit (modulePairingCoefficient μ U m p) :=
  rankOnePairing_coefficient_isUnit (A := Γ(X, U))
    (m.coordinate U le_rfl) (p.coordinate U le_rfl) (μ.app U) hμ

variable [IsIntegral X]

/-- Generic coefficients of the actual product of two sections are the
product of their generic coefficients with the one computed pairing factor.
The same factor therefore works for all three products `s²`, `s*t`, `t²`. -/
theorem moduleGenericCoefficient_pairing (U : X.Opens) [Nonempty U]
    (m : ModuleSheafFrame M U) (p : ModuleSheafFrame P U)
    (s t : M.sections) :
    moduleGenericCoefficient P U p (μ.sections s t) =
      X.germToFunctionField U (modulePairingCoefficient μ U m p) *
        moduleGenericCoefficient M U m s * moduleGenericCoefficient M U m t := by
  change X.germToFunctionField U
      (moduleFrameCoordinate U p (μ.app U (s.eval (op U)) (t.eval (op U)))) = _
  rw [modulePairing_apply μ U m p, map_mul, map_mul]
  rfl

/-- The same coefficient formula on the actual module of global sections,
using the actual restriction maps and naturality of the pairing. -/
theorem moduleGlobalGenericLinearMap_pairing (U : X.Opens) [Nonempty U]
    (m : ModuleSheafFrame M U) (p : ModuleSheafFrame P U)
    (s t : M.val.obj (op ⊤)) :
    moduleGlobalGenericLinearMap P U p (μ.app ⊤ s t) =
      X.germToFunctionField U (modulePairingCoefficient μ U m p) *
        moduleGlobalGenericLinearMap M U m s * moduleGlobalGenericLinearMap M U m t := by
  change X.germToFunctionField U (p.coordinate U le_rfl
      (P.val.map (homOfLE (show U ≤ ⊤ from le_top)).op (μ.app ⊤ s t))) =
    X.germToFunctionField U (modulePairingCoefficient μ U m p) *
      X.germToFunctionField U (m.coordinate U le_rfl
        (M.val.map (homOfLE (show U ≤ ⊤ from le_top)).op s)) *
      X.germToFunctionField U (m.coordinate U le_rfl
        (M.val.map (homOfLE (show U ≤ ⊤ from le_top)).op t))
  rw [μ.naturality]
  change X.germToFunctionField U (moduleFrameCoordinate U p (μ.app U _ _)) = _
  rw [modulePairing_apply μ U m p, map_mul, map_mul]
  rfl

/-- Local tensor-perfectness gives a nonzero common multiplier in the
actual function field. -/
theorem modulePairingCoefficient_generic_ne_zero (U : X.Opens) [Nonempty U]
    (m : ModuleSheafFrame M U) (p : ModuleSheafFrame P U)
    (hμ : Function.Bijective (TensorProduct.lift (μ.app U))) :
    X.germToFunctionField U (modulePairingCoefficient μ U m p) ≠ 0 :=
  ((modulePairingCoefficient_isUnit μ U m p hμ).map
    (X.germToFunctionField U).hom).ne_zero

end SquarePairing

section ComparePairings

variable {M N P : X.Modules}
    (μ : ModuleSheafPairing M M P) (ν : ModuleSheafPairing N N P)

/-- A genuine global square identity gives its weighted local-coordinate
identity by actual restriction and pairing naturality. The local identity
is a conclusion, not an independently assumed relation. -/
theorem pairing_square_eq_in_local_coordinates
    (s : M.val.obj (op ⊤)) (a : N.val.obj (op ⊤)) (c : Γ(X, ⊤))
    (h : μ.app ⊤ s s = c • ν.app ⊤ a a)
    (U : X.Opens) (m : ModuleSheafFrame M U)
    (n : ModuleSheafFrame N U) (p : ModuleSheafFrame P U) :
    modulePairingCoefficient μ U m p *
        (moduleFrameCoordinate U m
          (M.val.map (homOfLE (show U ≤ ⊤ from le_top)).op s)) ^ 2 =
      X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op c *
        modulePairingCoefficient ν U n p *
        (moduleFrameCoordinate U n
          (N.val.map (homOfLE (show U ≤ ⊤ from le_top)).op a)) ^ 2 := by
  have hlocal := congrArg (fun z => p.coordinate U le_rfl
    (P.val.map (homOfLE (show U ≤ ⊤ from le_top)).op z)) h
  dsimp only at hlocal
  rw [μ.naturality, P.val.map_smul, ν.naturality, map_smul] at hlocal
  change moduleFrameCoordinate U p (μ.app U _ _) =
    X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op c *
      moduleFrameCoordinate U p (ν.app U _ _) at hlocal
  rw [modulePairing_apply μ U m p, modulePairing_apply ν U n p] at hlocal
  simpa only [pow_two, mul_assoc] using hlocal

variable [IsIntegral X]

/-- A global identity of actual paired sections yields the weighted square
identity in the actual function field in every chosen common framed open. -/
theorem pairing_square_eq_in_generic_coefficients
    (s : M.val.obj (op ⊤)) (a : N.val.obj (op ⊤)) (c : Γ(X, ⊤))
    (h : μ.app ⊤ s s = c • ν.app ⊤ a a)
    (U : X.Opens) [Nonempty U] (m : ModuleSheafFrame M U)
    (n : ModuleSheafFrame N U) (p : ModuleSheafFrame P U) :
    X.germToFunctionField U (modulePairingCoefficient μ U m p) *
        (moduleGlobalGenericLinearMap M U m s) ^ 2 =
      X.germToFunctionField ⊤ c *
        X.germToFunctionField U (modulePairingCoefficient ν U n p) *
        (moduleGlobalGenericLinearMap N U n a) ^ 2 := by
  have hg := congrArg (moduleGlobalGenericLinearMap P U p) h
  rw [map_smul, moduleGlobalGenericLinearMap_pairing μ U m p,
    moduleGlobalGenericLinearMap_pairing ν U n p] at hg
  change X.germToFunctionField U (modulePairingCoefficient μ U m p) *
      moduleGlobalGenericLinearMap M U m s * moduleGlobalGenericLinearMap M U m s =
    X.germToFunctionField ⊤ c *
      (X.germToFunctionField U (modulePairingCoefficient ν U n p) *
        moduleGlobalGenericLinearMap N U n a * moduleGlobalGenericLinearMap N U n a) at hg
  simpa only [pow_two, mul_assoc] using hg

/-- A genuine global square identity with a unit scalar produces actual
local unit weights for the square-ratio comparison theorem. The weights
are constructed from the pairings; the target weighted equation is proved. -/
theorem exists_local_unit_weights_of_pairing_square_eq
    (s : M.val.obj (op ⊤)) (a : N.val.obj (op ⊤)) (c : Γ(X, ⊤)ˣ)
    (h : μ.app ⊤ s s = (c : Γ(X, ⊤)) • ν.app ⊤ a a)
    (U : X.Opens) [Nonempty U] (m : ModuleSheafFrame M U)
    (n : ModuleSheafFrame N U) (p : ModuleSheafFrame P U)
    (hμ : Function.Bijective (TensorProduct.lift (μ.app U)))
    (hν : Function.Bijective (TensorProduct.lift (ν.app U))) :
    ∃ u v : Γ(X, U)ˣ,
      X.germToFunctionField U (u : Γ(X, U)) *
          (moduleGlobalGenericLinearMap M U m s) ^ 2 =
        X.germToFunctionField U (v : Γ(X, U)) *
          (moduleGlobalGenericLinearMap N U n a) ^ 2 := by
  obtain ⟨u, hu⟩ := modulePairingCoefficient_isUnit μ U m p hμ
  obtain ⟨v, hv⟩ := modulePairingCoefficient_isUnit ν U n p hν
  let cU : Γ(X, U)ˣ := Units.map
    (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op).hom.toMonoidHom c
  refine ⟨u, cU * v, ?_⟩
  have hg := pairing_square_eq_in_generic_coefficients μ ν s a (c : Γ(X, ⊤)) h U m n p
  rw [← hu, ← hv] at hg
  change X.germToFunctionField U (u : Γ(X, U)) *
      (moduleGlobalGenericLinearMap M U m s) ^ 2 =
    X.germToFunctionField U
      (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op (c : Γ(X, ⊤)) *
        (v : Γ(X, U))) * (moduleGlobalGenericLinearMap N U n a) ^ 2
  rw [map_mul, generic_germ_restrict]
  exact hg

end ComparePairings

end EvenQuinticConic
