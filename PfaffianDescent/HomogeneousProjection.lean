import PfaffianDescent.HomogeneousDimensions
import Mathlib.RingTheory.GradedAlgebra.Basic

namespace PfaffianDescent
open MvPolynomial

section
variable {K σ : Type*} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

instance homogeneousSubmodule_finite [Finite σ] (d : ℕ) :
    Module.Finite K (homogeneousSubmodule σ K d) :=
  Module.Finite.iff_fg.mpr (homogeneousSubmodule_fg σ K d)

lemma homogeneousComponent_mul_right {p q : MvPolynomial σ K} {e : ℕ}
    (hq : q.IsHomogeneous e) (d : ℕ) :
    homogeneousComponent (d + e) (p * q) = homogeneousComponent d p * q := by
  rw [← decomposition.decompose'_apply, ← decomposition.decompose'_apply,
    DirectSum.Decomposition.decompose'_eq]
  exact DirectSum.coe_decompose_mul_add_of_right_mem (homogeneousSubmodule σ K) hq

lemma homogeneousComponent_mul_left {p q : MvPolynomial σ K} {e : ℕ}
    (hp : p.IsHomogeneous e) (d : ℕ) :
    homogeneousComponent (e + d) (p * q) = p * homogeneousComponent d q := by
  rw [← decomposition.decompose'_apply, ← decomposition.decompose'_apply,
    DirectSum.Decomposition.decompose'_eq]
  exact DirectSum.coe_decompose_mul_add_of_left_mem (homogeneousSubmodule σ K) hp

lemma homogeneousComponent_mul_right_of_lt {p q : MvPolynomial σ K} {e d : ℕ}
    (hq : q.IsHomogeneous e) (hd : d < e) :
    homogeneousComponent d (p * q) = 0 := by
  rw [← decomposition.decompose'_apply, DirectSum.Decomposition.decompose'_eq]
  exact DirectSum.coe_decompose_mul_of_right_mem_of_not_le
    (homogeneousSubmodule σ K) hq (not_le.mpr hd)

lemma homogeneous_of_mul_right {p q : MvPolynomial σ K} {d e : ℕ}
    (hq : q.IsHomogeneous e) (hne : q ≠ 0) (h : (p * q).IsHomogeneous (d + e)) :
    p.IsHomogeneous d := by
  have hp : homogeneousComponent d p = p := by
    apply mul_right_cancel₀ hne
    rw [← homogeneousComponent_mul_right hq, homogeneousComponent_eq_self h]
  rw [← hp]
  exact homogeneousComponent_isHomogeneous d p

lemma eq_zero_of_mul_homogeneous_lt {p q : MvPolynomial σ K} {d e : ℕ}
    (hq : q.IsHomogeneous e) (hne : q ≠ 0) (h : (p * q).IsHomogeneous d)
    (hd : d < e) : p = 0 := by
  have hz : p * q = 0 := by
    rw [← homogeneousComponent_eq_self h, homogeneousComponent_mul_right_of_lt hq hd]
  exact (mul_eq_zero.mp hz).resolve_right hne

end
end PfaffianDescent
