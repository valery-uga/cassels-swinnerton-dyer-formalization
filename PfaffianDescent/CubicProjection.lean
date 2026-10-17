import PfaffianDescent.CubicPointDeformation

namespace PfaffianDescent
open Module
open scoped BigOperators

section
variable {K L : Type*} [Field K] [Field L] [Algebra K L] {m n : ℕ}

/-- Project cubic coefficients onto the kernel of evaluation using a frame of
cubics whose values form a basis of the finite extension. -/
noncomputable def cubicProjection (p : Vec L n) (b : Basis (Fin m) K L)
    (d : Fin m → Cubic K n) (c : Cubic K n) : Cubic K n :=
  c - ∑ i, b.repr (cubicEvaluation p c) i • d i

theorem cubicProjection_vanishes (p : Vec L n) (b : Basis (Fin m) K L)
    (d : Fin m → Cubic K n) (hd : ∀ i, cubicEvaluation p (d i) = b i) (c : Cubic K n) :
    (cubicProjection p b d c |>.map (algebraMap K L)).eval p = 0 := by
  rw [← cubicEvaluation_eq, cubicProjection, map_sub, map_sum]
  simp only [map_smul, hd]
  rw [b.sum_repr, sub_self]

theorem cubicProjection_eq_self (p : Vec L n) (b : Basis (Fin m) K L)
    (d : Fin m → Cubic K n) (c : Cubic K n)
    (hF : (c.map (algebraMap K L)).eval p = 0) : cubicProjection p b d c = c := by
  simp only [cubicProjection, cubicEvaluation_eq, hF, map_zero, Finsupp.zero_apply,
    zero_smul, Finset.sum_const_zero, sub_zero]

end
end PfaffianDescent
