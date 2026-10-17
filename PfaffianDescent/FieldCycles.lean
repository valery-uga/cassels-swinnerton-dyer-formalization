import PfaffianDescent.QuarticCycle
import PfaffianDescent.EffectiveCycle

namespace PfaffianDescent
open Module
open scoped BigOperators
universe u

section
variable {K : Type u} [Field K]

/-- A nonzero homogeneous point on a cubic over a finite field extension.
Its extension degree counts the degree of the pushed-forward point cycle. -/
structure CubicFieldPoint (c : Cubic K 4) where
  Extension : Type u
  [field : Field Extension]
  [algebra : Algebra K Extension]
  [finite : FiniteDimensional K Extension]
  coordinates : Vec Extension 4
  nonzero : coordinates ≠ 0
  vanishes : (c.map (algebraMap K Extension)).eval coordinates = 0

attribute [instance] CubicFieldPoint.field CubicFieldPoint.algebra CubicFieldPoint.finite

/-- Existence of a finite effective cycle of field-valued points of a prescribed degree. -/
def HasEffectiveFieldCycle (c : Cubic K 4) (d : ℕ) : Prop :=
  ∃ (m : ℕ) (p : Fin m → CubicFieldPoint c) (w : Fin m → ℕ),
    ∑ i, w i * finrank K (p i).Extension = d

/-- Existence of an arbitrary integer cycle; coefficients may be negative. -/
def HasFieldZeroCycle (c : Cubic K 4) (d : ℤ) : Prop :=
  ∃ (m : ℕ) (p : Fin m → CubicFieldPoint c) (w : Fin m → ℤ),
    ∑ i, w i * (finrank K (p i).Extension : ℤ) = d

/-- Multiples of a rational point give effective cycles of every degree. -/
theorem rational_point_effective_field_cycle (c : Cubic K 4) (x : Vec K 4)
    (hx : x ≠ 0) (hF : c.eval x = 0) (d : ℕ) : HasEffectiveFieldCycle c d := by
  let p : CubicFieldPoint c := ⟨K, x, hx, hF⟩
  refine ⟨1, fun _ => p, fun _ => d, ?_⟩
  simp only [p, Module.finrank_self, mul_one, Fin.sum_univ_one]

end

section
variable {K : Type u} [Field K] [CharZero K]

/-- Effective degree four is equivalent to existence of a rational point. -/
theorem effective_field_cycle_four_iff (c : Cubic K 4) :
    HasEffectiveFieldCycle c 4 ↔ ∃ x : Vec K 4, x ≠ 0 ∧ c.eval x = 0 := by
  constructor
  · rintro ⟨m, p, w, hd⟩
    exact effective_degree_four_to_point (fun i => (p i).Extension) c w
      (fun i => (p i).coordinates) (fun i _ => (p i).nonzero) (fun i _ => (p i).vanishes) hd
  · rintro ⟨x, hx, hF⟩
    exact rational_point_effective_field_cycle c x hx hF 4

/-- Effective degree five is equivalent to existence of a rational point. -/
theorem effective_field_cycle_five_iff (c : Cubic K 4) :
    HasEffectiveFieldCycle c 5 ↔ ∃ x : Vec K 4, x ≠ 0 ∧ c.eval x = 0 := by
  constructor
  · rintro ⟨m, p, w, hd⟩
    exact effective_degree_five_to_point (fun i => (p i).Extension) c w
      (fun i => (p i).coordinates) (fun i _ => (p i).nonzero) (fun i _ => (p i).vanishes) hd
  · rintro ⟨x, hx, hF⟩
    exact rational_point_effective_field_cycle c x hx hF 5

/-- The effective degree-four/degree-five equivalence, proved without an effectivity assumption. -/
theorem effective_four_iff_five (c : Cubic K 4) :
    HasEffectiveFieldCycle c 4 ↔ HasEffectiveFieldCycle c 5 :=
  (effective_field_cycle_four_iff c).trans (effective_field_cycle_five_iff c).symm

end
end PfaffianDescent
