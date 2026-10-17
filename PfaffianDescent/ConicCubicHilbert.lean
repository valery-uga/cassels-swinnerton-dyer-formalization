import PfaffianDescent.ConicCubicHomogeneousQuotient
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace PfaffianDescent
open MvPolynomial Module
section
variable {K : Type*} [Field K]

lemma plane_homogeneous_finrank (d : ℕ) :
    finrank K (PlaneHomogeneous K d) = (d+2).choose 2 := by
  rw [homogeneous_polynomial_finrank]
  have h : 3+d-1 = d+2 := by omega
  rw [h]
  exact Nat.choose_symm_add

lemma conic_cubic_choose_identity (d : ℕ) :
    (d+7).choose 2 + (d+2).choose 2 = (d+5).choose 2 + (d+4).choose 2 + 6 := by
  simp only [Nat.add_succ, Nat.choose_succ_succ, Nat.choose_one_right, Nat.choose_zero_right]
  omega

/-- Every sufficiently large homogeneous component of the actual coordinate
ring of a relatively prime conic/cubic intersection has dimension six. -/
theorem conic_cubic_hilbert_six (q f : MvPolynomial (Fin 3) K)
    (hq : q.IsHomogeneous 2) (hf : f.IsHomogeneous 3)
    (hq0 : q ≠ 0) (hrel : IsRelPrime q f) (d : ℕ) :
    finrank K (conicCubicComponent q f (d+5)) = 6 := by
  have hfirst := LinearMap.finrank_range_add_finrank_ker (conicCubicGradedFirst q f hq hf d)
  rw [LinearMap.ker_eq_bot.mpr (conicCubicGradedFirst_injective q f hq hf hq0 d),
    finrank_bot, add_zero] at hfirst
  have hlast := LinearMap.finrank_range_add_finrank_ker (conicCubicGradedLast q f hq hf d)
  rw [← conicCubicGraded_exact q f hq hf hq0 hrel d, hfirst, Module.finrank_prod] at hlast
  have hproj := LinearMap.finrank_range_add_finrank_ker (conicCubicProjection q f (d+5))
  rw [conicCubicProjection_range, ← conicCubicProjection_exact q f hq hf d] at hproj
  rw [plane_homogeneous_finrank, plane_homogeneous_finrank, plane_homogeneous_finrank] at hlast
  rw [plane_homogeneous_finrank] at hproj
  have hchoose := conic_cubic_choose_identity d
  simp only [plane_homogeneous_finrank, Nat.add_assoc, Nat.reduceAdd] at hfirst hlast hproj
  omega

end
end PfaffianDescent
