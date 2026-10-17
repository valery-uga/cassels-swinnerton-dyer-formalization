import AllCharacteristics.PointDegrees
import AllCharacteristics.CycleDegrees
import Mathlib.Data.Finsupp.Order

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open scoped BigOperators
universe u

section
variable {X Y : Scheme.{u}} (f : X ⟶ Y)

lemma effectiveCycle_degree_add (a b : AllCharacteristics.EffectiveZeroCycle X) :
    AllCharacteristics.EffectiveZeroCycle.degree f (a + b) =
      AllCharacteristics.EffectiveZeroCycle.degree f a + AllCharacteristics.EffectiveZeroCycle.degree f b := by
  classical
  apply Finsupp.sum_add_index'
  · intro x
    exact zero_mul _
  · intro x n m
    exact add_mul _ _ _

lemma effectiveCycle_degree_single (x : closedPoints X) (n : ℕ) :
    AllCharacteristics.EffectiveZeroCycle.degree f (Finsupp.single x n) = n * f.residueDegree x.val := by
  simp [AllCharacteristics.EffectiveZeroCycle.degree]

end

section
variable {K : Type u} [Field K] {X : Scheme.{u}}

/-- An effective closed-point cycle of degree one is a rational point. -/
theorem section_of_effective_cycle_degree_one (f : X ⟶ Spec (.of K))
    (z : AllCharacteristics.EffectiveZeroCycle X)
    (hz : AllCharacteristics.EffectiveZeroCycle.degree f z = 1) :
    ∃ s : Spec (.of K) ⟶ X, s ≫ f = 𝟙 _ := by
  classical
  have hsum : (∑ x ∈ z.support, z x * f.residueDegree x.val) = 1 := hz
  obtain ⟨x, hx, hpos⟩ := Finset.exists_ne_zero_of_sum_ne_zero (hsum.trans_ne one_ne_zero)
  have hle : z x * f.residueDegree x.val ≤ 1 := by
    calc
      _ ≤ ∑ y ∈ z.support, z y * f.residueDegree y.val :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) hx
      _ = 1 := hsum
  have hprod : z x * f.residueDegree x.val = 1 := by omega
  have hw : 0 < z x := by
    by_contra h
    have hz0 : z x = 0 := by omega
    rw [hz0, zero_mul] at hprod
    contradiction
  have hxpos : 0 < f.residueDegree x.val := by
    by_contra h
    have hx0 : f.residueDegree x.val = 0 := by omega
    rw [hx0, mul_zero] at hprod
    contradiction
  have hdle := Nat.le_mul_of_pos_left (f.residueDegree x.val) hw
  exact AllCharacteristics.section_of_residueDegree_one f x.val (by omega)

/-- Removing a degree-five point from an effective degree-six cycle leaves an
effective degree-one cycle and hence a rational section. -/
theorem residual_cycle_six_minus_five (f : X ⟶ Spec (.of K))
    (z : AllCharacteristics.EffectiveZeroCycle X) (x : closedPoints X) (hx : x ∈ z.support)
    (hz : AllCharacteristics.EffectiveZeroCycle.degree f z = 6) (hd : f.residueDegree x.val = 5) :
    ∃ r : AllCharacteristics.EffectiveZeroCycle X,
      z = r + Finsupp.single x 1 ∧ AllCharacteristics.EffectiveZeroCycle.degree f r = 1 ∧
      ∃ s : Spec (.of K) ⟶ X, s ≫ f = 𝟙 _ := by
  classical
  have hle : Finsupp.single x 1 ≤ z := Finsupp.single_le_iff.mpr
    (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hx))
  let r := z - Finsupp.single x 1
  have heq : z = r + Finsupp.single x 1 := (tsub_add_cancel_of_le hle).symm
  have hr : AllCharacteristics.EffectiveZeroCycle.degree f r = 1 := by
    rw [heq, effectiveCycle_degree_add, effectiveCycle_degree_single, hd] at hz
    omega
  exact ⟨r, heq, hr, section_of_effective_cycle_degree_one f r hr⟩

end
end PfaffianDescent
