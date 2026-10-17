import PfaffianDescent.QuadraticSecant
import PfaffianDescent.Specialization

namespace PfaffianDescent
open scoped BigOperators

namespace Cubic
section
variable {R : Type*} [CommRing R] {n : ℕ}

/-- A product of three linear forms, encoded as a cubic coefficient tensor. -/
def tensor (a b c : Vec R n) : Cubic R n := fun i => a i.1 * b i.2.1 * c i.2.2

theorem eval_tensor (a b c x : Vec R n) :
    (tensor a b c).eval x = (∑ i, a i * x i) * (∑ i, b i * x i) * (∑ i, c i * x i) := by
  calc
    (tensor a b c).eval x = ∑ i, ∑ j, ∑ k, (a i*x i)*(b j*x j)*(c k*x k) := by
      simp only [eval, tensor, Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = _ := by
      simp only [← Finset.mul_sum, ← Finset.sum_mul]

theorem eval_add (c d : Cubic R n) (x : Vec R n) :
    (c+d).eval x = c.eval x + d.eval x := by
  simp only [eval, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem eval_sub (c d : Cubic R n) (x : Vec R n) :
    (c-d).eval x = c.eval x - d.eval x := by
  simp only [eval, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

end
end Cubic

section Ring
variable {R : Type*} [CommRing R]

/-- The linear form given by one entry of a matrix pencil. -/
def entryForm (A : Fin 4 → Mat R 6) (i j : Fin 6) : Vec R 4 := fun k => A k i j

/-- The homogeneous cubic coefficient tensor of a Pfaffian pencil. -/
def pfaffianCubic (A : Fin 4 → Mat R 6) : Cubic R 4 :=
    Cubic.tensor (entryForm A 0 1) (entryForm A 2 3) (entryForm A 4 5)
  - Cubic.tensor (entryForm A 0 1) (entryForm A 2 4) (entryForm A 3 5)
  + Cubic.tensor (entryForm A 0 1) (entryForm A 2 5) (entryForm A 3 4)
  - Cubic.tensor (entryForm A 0 2) (entryForm A 1 3) (entryForm A 4 5)
  + Cubic.tensor (entryForm A 0 2) (entryForm A 1 4) (entryForm A 3 5)
  - Cubic.tensor (entryForm A 0 2) (entryForm A 1 5) (entryForm A 3 4)
  + Cubic.tensor (entryForm A 0 3) (entryForm A 1 2) (entryForm A 4 5)
  - Cubic.tensor (entryForm A 0 3) (entryForm A 1 4) (entryForm A 2 5)
  + Cubic.tensor (entryForm A 0 3) (entryForm A 1 5) (entryForm A 2 4)
  - Cubic.tensor (entryForm A 0 4) (entryForm A 1 2) (entryForm A 3 5)
  + Cubic.tensor (entryForm A 0 4) (entryForm A 1 3) (entryForm A 2 5)
  - Cubic.tensor (entryForm A 0 4) (entryForm A 1 5) (entryForm A 2 3)
  + Cubic.tensor (entryForm A 0 5) (entryForm A 1 2) (entryForm A 3 4)
  - Cubic.tensor (entryForm A 0 5) (entryForm A 1 3) (entryForm A 2 4)
  + Cubic.tensor (entryForm A 0 5) (entryForm A 1 4) (entryForm A 2 3)

private theorem entryForm_eval (A : Fin 4 → Mat R 6) (x : Vec R 4) (i j : Fin 6) :
    (∑ k, entryForm A i j k * x k) = pencil A x i j := by
  simp only [entryForm, pencil, Fin.sum_univ_four,
    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-- The tensor represents the actual Pfaffian polynomial. -/
theorem eval_pfaffianCubic (A : Fin 4 → Mat R 6) (x : Vec R 4) :
    (pfaffianCubic A).eval x = pf6 (pencil A x) := by
  simp only [pfaffianCubic, Cubic.eval_add, Cubic.eval_sub, Cubic.eval_tensor, entryForm_eval]
  unfold pf6
  ring

variable {S : Type*} [CommRing S]

theorem pfaffianCubic_map (f : R →+* S) (A : Fin 4 → Mat R 6) :
    (pfaffianCubic A).map f = pfaffianCubic (fun i => (A i).map f) := by
  funext i
  simp only [Cubic.map, pfaffianCubic, Cubic.tensor, entryForm, Pi.add_apply, Pi.sub_apply,
    Matrix.map_apply, map_add, map_sub, map_mul]

end Ring

section Field
variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

/-- Quadratic secant descent for the Pfaffian polynomial, with no smoothness assumption. -/
theorem pfaffian_quadratic_secant (hdim : Module.finrank K L = 2)
    (A : Fin 4 → Mat K 6)
    (h : HasPfaffianPoint (fun i => (A i).map (algebraMap K L))) :
    HasPfaffianPoint A := by
  obtain ⟨x, hx, hFx⟩ := h
  have hc : ((pfaffianCubic A).map (algebraMap K L)).eval x = 0 := by
    rw [pfaffianCubic_map, eval_pfaffianCubic]
    exact hFx
  obtain ⟨y, hy, hFy⟩ := cubic_quadratic_secant hdim (pfaffianCubic A) x hx hc
  exact ⟨y, hy, (eval_pfaffianCubic A y).symm.trans hFy⟩

end Field
end PfaffianDescent
