import PfaffianDescent.TopHomogeneousProduct

namespace PfaffianDescent
open MvPolynomial
section
variable {K σ : Type*} [Field K]

/-- A nonzero nonunit polynomial over a field has positive total degree. -/
lemma totalDegree_pos_of_nonunit {p : MvPolynomial σ K} (hp : p ≠ 0) (hu : ¬ IsUnit p) :
    0 < p.totalDegree := by
  apply Nat.pos_of_ne_zero
  intro h
  have he : p = C (constantCoeff p) := totalDegree_eq_zero_iff_eq_C.mp h
  have hc : constantCoeff p ≠ 0 := by
    intro hz
    apply hp
    rw [he, hz, map_zero]
  apply hu
  rw [he]
  exact (isUnit_iff_ne_zero.mpr hc).map C

/-- If a nonzero plane cubic and conic share a nonconstant factor, the cubic
has a nonzero homogeneous linear factor over the original coefficient field.
The common factor has degree one or two; in the second case the residual
factor of the cubic supplies the line. -/
theorem conic_cubic_common_factor_linear_divisor
    {q f d : MvPolynomial σ K} (hq : q.IsHomogeneous 2) (hf : f.IsHomogeneous 3)
    (hq0 : q ≠ 0) (hf0 : f ≠ 0) (hd : ¬ IsUnit d) (hdq : d ∣ q) (hdf : d ∣ f) :
    ∃ l : MvPolynomial σ K, l ≠ 0 ∧ l.IsHomogeneous 1 ∧ l ∣ f := by
  obtain ⟨a, ha⟩ := hdq
  obtain ⟨b, hb⟩ := hdf
  have hda : d*a ≠ 0 := ha ▸ hq0
  have hdb : d*b ≠ 0 := hb ▸ hf0
  have hd0 : d ≠ 0 := left_ne_zero_of_mul hda
  have ha0 : a ≠ 0 := right_ne_zero_of_mul hda
  have hb0 : b ≠ 0 := right_ne_zero_of_mul hdb
  have hdegq : d.totalDegree + a.totalDegree = 2 := by
    rw [← totalDegree_mul_of_isDomain hd0 ha0, ← ha, hq.totalDegree hq0]
  have hdegf : d.totalDegree + b.totalDegree = 3 := by
    rw [← totalDegree_mul_of_isDomain hd0 hb0, ← hb, hf.totalDegree hf0]
  have hpos := totalDegree_pos_of_nonunit hd0 hd
  have hfac : f = homogeneousComponent d.totalDegree d * homogeneousComponent b.totalDegree b := by
    rw [hb]
    exact homogeneous_product_eq_top_components hd0 hb0 (hb ▸ hf)
  by_cases h1 : d.totalDegree = 1
  · refine ⟨homogeneousComponent d.totalDegree d, top_homogeneousComponent_ne_zero hd0, ?_, ?_⟩
    · rw [h1]
      exact homogeneousComponent_isHomogeneous 1 d
    · exact ⟨homogeneousComponent b.totalDegree b, hfac⟩
  · have hb1 : b.totalDegree = 1 := by omega
    refine ⟨homogeneousComponent b.totalDegree b, top_homogeneousComponent_ne_zero hb0, ?_, ?_⟩
    · rw [hb1]
      exact homogeneousComponent_isHomogeneous 1 b
    · exact ⟨homogeneousComponent d.totalDegree d, hfac.trans (mul_comm _ _)⟩

end
end PfaffianDescent
