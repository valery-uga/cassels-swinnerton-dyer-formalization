import AllCharacteristics.EffectiveCycleToZeroCycle

/-!
# Assembling cycles from replacements of their closed points

Replacing each point in the support by an effective cycle of the same degree
preserves the degree of an effective or signed zero-cycle. This permits
geometric point-lifting constructions to be applied to signed cycles without
assuming effectivity or discarding inseparable residue degrees.
-/

open AlgebraicGeometry CategoryTheory
open scoped BigOperators
namespace AllCharacteristics
universe u

/-- The natural-number degree is a linear map on effective cycles. -/
noncomputable def EffectiveZeroCycle.degreeLinearMap
    {X Y : Scheme.{u}} (f : X ⟶ Y) : EffectiveZeroCycle X →ₗ[ℕ] ℕ :=
  Finsupp.linearCombination ℕ (fun x : closedPoints X ↦ f.residueDegree x.1)

/-- The linear-map presentation equals the original effective degree. -/
theorem EffectiveZeroCycle.degreeLinearMap_apply
    {X Y : Scheme.{u}} (f : X ⟶ Y) (z : EffectiveZeroCycle X) :
    degreeLinearMap f z = degree f z := rfl

/-- Replacing each support point by an effective cycle of the same degree
preserves the total effective degree. -/
theorem exists_effectiveZeroCycle_of_support_replacements
    {X Y B C : Scheme.{u}} (f : X ⟶ B) (g : Y ⟶ C) (z : EffectiveZeroCycle X)
    (h : ∀ x ∈ z.support, ∃ w : EffectiveZeroCycle Y,
      EffectiveZeroCycle.degree g w = f.residueDegree x.1) :
    ∃ w : EffectiveZeroCycle Y, EffectiveZeroCycle.degree g w = EffectiveZeroCycle.degree f z := by
  classical
  choose w hw using fun x : z.support ↦ h x.1 x.2
  refine ⟨∑ x : z.support, z x.1 • w x, ?_⟩
  rw [← EffectiveZeroCycle.degreeLinearMap_apply, map_sum]
  simp only [map_smul, EffectiveZeroCycle.degreeLinearMap_apply, hw, smul_eq_mul]
  exact Finset.sum_coe_sort z.support (fun x ↦ z x * f.residueDegree x.1)

/-- Signed combinations of the replacement cycles preserve degree, even when
the source cycle has negative coefficients. -/
theorem exists_zeroCycle_of_support_replacements
    {X Y B C : Scheme.{u}} (f : X ⟶ B) (g : Y ⟶ C) (z : ZeroCycle X)
    (h : ∀ x ∈ z.support, ∃ w : EffectiveZeroCycle Y,
      EffectiveZeroCycle.degree g w = f.residueDegree x.1) :
    ∃ w : ZeroCycle Y, ZeroCycle.degree g w = ZeroCycle.degree f z := by
  classical
  choose w hw using fun x : z.support ↦ h x.1 x.2
  refine ⟨∑ x : z.support, z x.1 • (w x).toZeroCycle, ?_⟩
  rw [map_sum]
  simp only [map_smul, EffectiveZeroCycle.degree_toZeroCycle, hw, smul_eq_mul]
  exact Finset.sum_coe_sort z.support (fun x ↦ z x * (f.residueDegree x.1 : ℤ))

end AllCharacteristics
