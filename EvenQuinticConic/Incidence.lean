import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# An explicit affine chart of an incidence correspondence

This file verifies the elementary linear algebra used in the final incidence
step of the proposed geometric argument.  Two independent homogeneous linear
equations in three variables have one projective solution; on the chart where
the minor of the first two columns is nonzero, its third coordinate is nonzero
and the solution has an explicit normalization.

The last definition gives an equivalence of **sets** between this normalized
incidence chart and the corresponding minor chart in an arbitrary parameter
set.  It is not a theorem about schemes, rational maps, or birationality.  In
particular this file does not establish the proposed conic-bundle no-go theorem.

For the proposed application, `a z` is the row of linear forms `ℓᵢ(z)` and
`b z` is the row of quadratic forms `rᵢ(z)`.  The geometric work still needed is
to show that a suitable minor defines a nonempty dense open subset, to upgrade
the formulas to regular maps on scheme charts, and to identify those charts
with the intended conic bundle.  None of those claims is assumed or asserted
by the results below.
-/

namespace EvenQuinticConic.Incidence

@[ext]
structure Vec3 (K : Type*) where
  x : K
  y : K
  z : K

section Ring

variable {K : Type*} [CommRing K]

def dot (a t : Vec3 K) : K := a.x * t.x + a.y * t.y + a.z * t.z

def cross (a b : Vec3 K) : Vec3 K :=
  ⟨a.y * b.z - a.z * b.y,
   a.z * b.x - a.x * b.z,
   a.x * b.y - a.y * b.x⟩

def IsIncident (a b t : Vec3 K) : Prop := dot a t = 0 ∧ dot b t = 0

theorem dot_cross_left (a b : Vec3 K) : dot a (cross a b) = 0 := by
  dsimp [dot, cross]
  ring

theorem dot_cross_right (a b : Vec3 K) : dot b (cross a b) = 0 := by
  dsimp [dot, cross]
  ring

theorem cross_isIncident (a b : Vec3 K) : IsIncident a b (cross a b) :=
  ⟨dot_cross_left a b, dot_cross_right a b⟩

/-- Elimination without division; valid over every commutative ring. -/
theorem incident_minor_identities (a b t : Vec3 K) (h : IsIncident a b t) :
    (cross a b).z * t.x = (cross a b).x * t.z ∧
    (cross a b).z * t.y = (cross a b).y * t.z := by
  obtain ⟨ha, hb⟩ := h
  dsimp [dot] at ha hb
  dsimp [cross]
  constructor
  · linear_combination b.y * ha - a.y * hb
  · linear_combination a.x * hb - b.x * ha

end Ring

section Field

variable {K : Type*} [Field K]

def normalizedPoint (a b : Vec3 K) : Vec3 K :=
  ⟨(cross a b).x / (cross a b).z,
   (cross a b).y / (cross a b).z,
   1⟩

@[simp]
theorem normalizedPoint_z (a b : Vec3 K) : (normalizedPoint a b).z = 1 := rfl

theorem normalizedPoint_isIncident (a b : Vec3 K) (hd : (cross a b).z ≠ 0) :
    IsIncident a b (normalizedPoint a b) := by
  have divide_dot (r c : Vec3 K) (hc : c.z ≠ 0) :
      dot r ⟨c.x / c.z, c.y / c.z, 1⟩ = dot r c / c.z := by
    change r.x * (c.x / c.z) + r.y * (c.y / c.z) + r.z * 1 =
      (r.x * c.x + r.y * c.y + r.z * c.z) / c.z
    simp only [add_div, mul_div_assoc, div_self hc, mul_one]
  constructor
  · rw [show normalizedPoint a b =
        ⟨(cross a b).x / (cross a b).z, (cross a b).y / (cross a b).z, 1⟩ from rfl,
      divide_dot a (cross a b) hd, dot_cross_left, zero_div]
  · rw [show normalizedPoint a b =
        ⟨(cross a b).x / (cross a b).z, (cross a b).y / (cross a b).z, 1⟩ from rfl,
      divide_dot b (cross a b) hd, dot_cross_right, zero_div]

theorem incident_coordinates (a b t : Vec3 K) (hd : (cross a b).z ≠ 0)
    (h : IsIncident a b t) :
    t.x = (cross a b).x / (cross a b).z * t.z ∧
    t.y = (cross a b).y / (cross a b).z * t.z := by
  obtain ⟨hx, hy⟩ := incident_minor_identities a b t h
  constructor
  · apply (mul_left_cancel₀ hd)
    calc
      (cross a b).z * t.x = (cross a b).x * t.z := hx
      _ = (cross a b).z * ((cross a b).x / (cross a b).z * t.z) := by
        field_simp [hd]
  · apply (mul_left_cancel₀ hd)
    calc
      (cross a b).z * t.y = (cross a b).y * t.z := hy
      _ = (cross a b).z * ((cross a b).y / (cross a b).z * t.z) := by
        field_simp [hd]

/-- A nonzero projective representative must belong to the third affine chart. -/
theorem incident_third_coordinate_ne_zero (a b t : Vec3 K)
    (hd : (cross a b).z ≠ 0) (h : IsIncident a b t)
    (ht : t.x ≠ 0 ∨ t.y ≠ 0 ∨ t.z ≠ 0) : t.z ≠ 0 := by
  intro hz
  obtain ⟨hx, hy⟩ := incident_coordinates a b t hd h
  simp only [hz, mul_zero] at hx hy
  rcases ht with ht | ht | ht
  · exact ht hx
  · exact ht hy
  · exact ht hz

theorem normalizedPoint_unique (a b t : Vec3 K) (hd : (cross a b).z ≠ 0)
    (h : IsIncident a b t) (hz : t.z = 1) : t = normalizedPoint a b := by
  obtain ⟨hx, hy⟩ := incident_coordinates a b t hd h
  apply Vec3.ext
  · simpa only [hz, mul_one] using hx
  · simpa only [hz, mul_one] using hy
  · exact hz

theorem existsUnique_normalizedPoint (a b : Vec3 K) (hd : (cross a b).z ≠ 0) :
    ∃! t : Vec3 K, IsIncident a b t ∧ t.z = 1 := by
  refine ⟨normalizedPoint a b, ⟨normalizedPoint_isIncident a b hd, rfl⟩, ?_⟩
  intro t ht
  exact normalizedPoint_unique a b t hd ht.1 ht.2

variable {Z : Type*}

/-- The open-minor condition, here represented only as a subset of parameters. -/
def MinorChart (a b : Z → Vec3 K) := {z : Z // (cross (a z) (b z)).z ≠ 0}

/-- Normalized solutions over the open-minor condition, as a set. -/
def IncidenceChart (a b : Z → Vec3 K) :=
  {p : Z × Vec3 K // (cross (a p.1) (b p.1)).z ≠ 0 ∧
    IsIncident (a p.1) (b p.1) p.2 ∧ p.2.z = 1}

/-- Explicit inverse of projection, on a normalized incidence chart.

No regularity or scheme-theoretic assertion is encoded by this equivalence.
-/
def incidenceChartEquiv (a b : Z → Vec3 K) : IncidenceChart a b ≃ MinorChart a b where
  toFun p := ⟨p.val.1, p.property.1⟩
  invFun z := ⟨(z.val, normalizedPoint (a z.val) (b z.val)),
    z.property, normalizedPoint_isIncident _ _ z.property, rfl⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact (normalizedPoint_unique _ _ _ p.property.1 p.property.2.1
        p.property.2.2).symm
  right_inv z := by
    apply Subtype.ext
    rfl

end Field

end EvenQuinticConic.Incidence
