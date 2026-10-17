import PfaffianDescent.ProjectiveLineCharts

namespace PfaffianDescent
section
variable (R : Type*) [CommRing R]

lemma lineStandardSubmodule_injective (b : Bool) : Function.Injective (lineStandardSubmodule R b) := by
  intro a d h
  cases b
  · have hx : ![1, a] ∈ lineStandardSubmodule R false a := by
      change a = a * 1
      exact (mul_one a).symm
    rw [h] at hx
    change a = d * 1 at hx
    exact hx.trans (mul_one d)
  · have hx : ![a, 1] ∈ lineStandardSubmodule R true a := by
      change a = a * 1
      exact (mul_one a).symm
    rw [h] at hx
    change a = d * 1 at hx
    exact hx.trans (mul_one d)

/-- The two line charts meet exactly where their slopes are mutual inverses. -/
lemma lineStandardSubmodule_false_true_iff (a d : R) :
    lineStandardSubmodule R false a = lineStandardSubmodule R true d ↔ a * d = 1 := by
  constructor
  · intro h
    have hx : ![1, a] ∈ lineStandardSubmodule R false a := by
      change a = a * 1
      exact (mul_one a).symm
    rw [h] at hx
    change 1 = d * a at hx
    exact (mul_comm a d).trans hx.symm
  · intro h
    ext x
    change x 1 = a * x 0 ↔ x 0 = d * x 1
    constructor
    · intro hx
      rw [hx, ← mul_assoc, mul_comm d a, h, one_mul]
    · intro hx
      rw [hx, ← mul_assoc, h, one_mul]

/-- The standard line-chart equality is a concrete ring equation, without field assumptions. -/
lemma lineStandardSubmodule_eq_iff (b c : Bool) (a d : R) :
    lineStandardSubmodule R b a = lineStandardSubmodule R c d ↔
      if b = c then a = d else a * d = 1 := by
  cases b <;> cases c
  · simp only [↓reduceIte]
    exact (lineStandardSubmodule_injective R false).eq_iff
  · simpa using lineStandardSubmodule_false_true_iff R a d
  · simpa [eq_comm, mul_comm] using
      lineStandardSubmodule_false_true_iff R d a
  · simp only [↓reduceIte]
    exact (lineStandardSubmodule_injective R true).eq_iff

lemma lineGrassmannianChartSubmodule_eq_iff (b c : Bool) (a d : R) :
    grassmannianChartSubmodule R (lineChartPermutation b) (lineChartMatrix R a) =
      grassmannianChartSubmodule R (lineChartPermutation c) (lineChartMatrix R d) ↔
        if b = c then a = d else a * d = 1 := by
  rw [← (Submodule.map_injective_of_injective (lineAmbientCoordinates R).injective).eq_iff,
    lineStandardSubmodule_eq_chart, lineStandardSubmodule_eq_chart]
  exact lineStandardSubmodule_eq_iff R b c a d

end
end PfaffianDescent
