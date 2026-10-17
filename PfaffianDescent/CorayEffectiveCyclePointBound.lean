import AllCharacteristics.ProperCyclePushforward

/-! Actual effective-cycle degree bounds for Coray's least-degree argument.
These proofs extract an actual closed point and preserve actual residue degree
under the installed proper pushforward. No Riemann–Roch or genus hypothesis
is supplied or concluded here. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory AllCharacteristics
open scoped BigOperators
universe u

/-- Every support point of an actual effective cycle has residue degree at
most the actual total degree, because its actual multiplicity is positive. -/
theorem effectiveCycle_supportPoint_degree_le
    {X Y : Scheme.{u}} (f : X ⟶ Y) (z : EffectiveZeroCycle X)
    (x : closedPoints X) (hx : x ∈ z.support) :
    f.residueDegree x.1 ≤ EffectiveZeroCycle.degree f z := by
  have hpos : 0 < z x := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hx)
  calc
    f.residueDegree x.1 ≤ z x * f.residueDegree x.1 :=
      Nat.le_mul_of_pos_left _ hpos
    _ ≤ ∑ y ∈ z.support, z y * f.residueDegree y.1 :=
      Finset.single_le_sum (fun y _ => Nat.zero_le (z y * f.residueDegree y.1)) hx
    _ = EffectiveZeroCycle.degree f z := rfl

/-- An actual effective cycle with total degree prime to three gives an
actual support point prime to three whose degree does not exceed the total. -/
theorem effectiveCycle_coprime_degree_has_bounded_closedPoint
    {X Y : Scheme.{u}} (f : X ⟶ Y) (z : EffectiveZeroCycle X)
    (hc : Nat.Coprime (EffectiveZeroCycle.degree f z) 3) :
    ∃ x ∈ z.support, Nat.Coprime (f.residueDegree x.1) 3 ∧
      f.residueDegree x.1 ≤ EffectiveZeroCycle.degree f z := by
  obtain ⟨x, hx, hcop⟩ := EffectiveZeroCycle.exists_coprime_degree f z hc
  exact ⟨x, hx, hcop, effectiveCycle_supportPoint_degree_le f z x hx⟩

/-- An actual effective cycle on the normalization or any universally closed
source gives a closed point on its actual image of bounded degree prime to
three. The full residue-weighted pushforward and its degree are constructed;
no degree-preserving comparison is assumed. -/
theorem proper_effectiveCycle_coprime_degree_has_bounded_imagePoint
    {C X B : Scheme.{u}} (i : C ⟶ X) [UniversallyClosed i]
    (f : X ⟶ B) (z : EffectiveZeroCycle C)
    (hc : Nat.Coprime (EffectiveZeroCycle.degree (i ≫ f) z) 3) :
    ∃ x : closedPoints C,
      Nat.Coprime (f.residueDegree (i x.1)) 3 ∧
      f.residueDegree (i x.1) ≤ EffectiveZeroCycle.degree (i ≫ f) z := by
  have hp : Nat.Coprime (EffectiveZeroCycle.degree f (pushforwardCycle i z)) 3 := by
    rw [degree_pushforwardCycle]
    exact hc
  obtain ⟨y, hy, hcop, hle⟩ :=
    effectiveCycle_coprime_degree_has_bounded_closedPoint f (pushforwardCycle i z) hp
  obtain ⟨x, hx⟩ := pushforwardCycle_support_subset_range i z hy
  have hxy : i x.1 = y.1 := by
    simpa only [universallyClosedPointMap] using
      congrArg (fun t : closedPoints X => t.1) hx
  refine ⟨x, ?_, ?_⟩
  · rw [hxy]
    exact hcop
  · rw [hxy]
    rw [degree_pushforwardCycle] at hle
    exact hle

end PfaffianDescent.Coray
