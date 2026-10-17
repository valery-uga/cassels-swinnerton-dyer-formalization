import PfaffianDescent.PfaffianCubic

namespace PfaffianDescent.Cubic
open scoped BigOperators
section
variable {R S : Type*} [CommRing R] [CommRing S] {n m : ℕ}

theorem eval_coefficient_smul (c : Cubic R n) (s : R) (x : Vec R n) :
    (s • c).eval x = s * c.eval x := by
  simp only [eval, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem eval_sum {ι : Type*} (s : Finset ι) (c : ι → Cubic R n) (x : Vec R n) :
    (∑ i ∈ s, c i).eval x = ∑ i ∈ s, (c i).eval x := by
  simp only [eval, Finset.sum_apply, Finset.sum_mul]
  exact Finset.sum_comm

/-- Pull a cubic form back by a linear map on coordinates. -/
def compLinear (c : Cubic R n) (M : Matrix (Fin n) (Fin m) R) : Cubic R m :=
  ∑ i, c i • tensor (M i.1) (M i.2.1) (M i.2.2)

theorem eval_compLinear (c : Cubic R n) (M : Matrix (Fin n) (Fin m) R) (x : Vec R m) :
    (c.compLinear M).eval x = c.eval (M.mulVec x) := by
  rw [compLinear, eval_sum]
  simp_rw [eval_coefficient_smul, eval_tensor]
  simp only [eval, Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem compLinear_map (f : R →+* S) (c : Cubic R n) (M : Matrix (Fin n) (Fin m) R) :
    (c.compLinear M).map f = (c.map f).compLinear (M.map f) := by
  funext i
  simp only [map, compLinear, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    map_sum, map_mul, tensor, Matrix.map_apply]

end
end PfaffianDescent.Cubic
