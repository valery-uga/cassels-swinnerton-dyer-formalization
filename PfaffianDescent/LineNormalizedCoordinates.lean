import PfaffianDescent.LineChartSubmoduleEquality

namespace PfaffianDescent
section
variable {R : Type*} [CommRing R]

/-- A normalized pair of homogeneous coordinates for a line chart. -/
def lineNormalizedCoordinates (b : Bool) (a : R) (i : Bool) : R := if i = b then 1 else a

/-- Equal line-chart submodules give an invertible ratio relating both normalized tuples. -/
lemma lineNormalizedCoordinates_ratio (b c : Bool) (a d : R)
    (h : if b = c then a = d else a * d = 1) :
    IsUnit (lineNormalizedCoordinates b a c) ∧ ∀ i,
      lineNormalizedCoordinates b a i = lineNormalizedCoordinates b a c * lineNormalizedCoordinates c d i := by
  by_cases hbc : b = c
  · subst c
    simp only [if_pos rfl] at h
    subst d
    simp [lineNormalizedCoordinates]
  · have had : a * d = 1 := by simpa only [if_neg hbc] using h
    have hcb : c ≠ b := Ne.symm hbc
    have hu : IsUnit a := isUnit_iff_exists_inv.mpr ⟨d, had⟩
    refine ⟨by simpa only [lineNormalizedCoordinates, if_neg hcb] using hu, ?_⟩
    intro i
    cases b <;> cases c <;> cases i <;> simp_all [lineNormalizedCoordinates]

end
end PfaffianDescent
