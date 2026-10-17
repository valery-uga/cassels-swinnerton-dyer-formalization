import PfaffianDescent.CorayGradedChartSectionEvaluation

/-! Source only, unverified. Ordinary multiplication in the actual
quotient grading is compatible with normalization in the same chart. -/
noncomputable section
namespace PfaffianDescent.Coray
open HomogeneousLocalization
open scoped PfaffianDescent.Coray
universe u v
section
variable {K : Type u} {A : Type v} [CommRing K] [CommRing A] [Algebra K A]
variable (G : ℕ → Submodule K A) [GradedRing G] {z : A} (hz : z ∈ G 1)

def gradeSectionProduct {a b : ℕ} (s : G a) (t : G b) : G (a + b) :=
  ⟨s.1 * t.1, SetLike.mul_mem_graded s.2 t.2⟩

theorem gradedChartSectionEvaluation_product {a b : ℕ} (s : G a) (t : G b) :
    gradedChartSectionEvaluation G hz (a + b) (gradeSectionProduct G s t) =
      gradedChartSectionEvaluation G hz a s * gradedChartSectionEvaluation G hz b t := by
  apply val_injective (.powers z)
  rw [val_mul, gradedChartSectionEvaluation_val, gradedChartSectionEvaluation_val,
    gradedChartSectionEvaluation_val, Localization.mk_mul]
  simp only [gradeSectionProduct, pow_add]
  rfl

/-- A power of the actual chart coordinate normalizes to one in its
own degree. No denominator is changed to another degree or coordinate. -/
def gradeChartCoordinatePower (k : ℕ) : G k :=
  ⟨z ^ k, by simpa only [smul_eq_mul, mul_one] using SetLike.pow_mem_graded k hz⟩

theorem gradedChartSectionEvaluation_coordinatePower (k : ℕ) :
    gradedChartSectionEvaluation G hz k (gradeChartCoordinatePower G hz k) = 1 := by
  apply val_injective (.powers z)
  rw [gradedChartSectionEvaluation_val, val_one]
  exact Localization.mk_self ⟨z ^ k, by use k⟩

end
end PfaffianDescent.Coray
end
