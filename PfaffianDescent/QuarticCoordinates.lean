import PfaffianDescent.TwistedCubic
import PfaffianDescent.PrimitiveSpan

namespace PfaffianDescent
open Module
open scoped BigOperators

section
variable {K L : Type*} [Field K] [CharZero K] [Field L] [Algebra K L]
    [FiniteDimensional K L]

/-- Power-basis coordinates and the degree-four minimal polynomial of their generator. -/
theorem exists_power_basis_four (hdim : finrank K L = 4) :
    ∃ a : L, ∃ b : Basis (Fin 4) K L,
      (∀ i, b i = a^(i : ℕ)) ∧ (minpoly K a).natDegree = 4 := by
  let p := Field.powerBasisOfFiniteOfSeparable K L
  have he : p.dim = 4 := p.finrank.symm.trans hdim
  refine ⟨p.gen, p.basis.reindex (finCongr he), ?_, p.natDegree_minpoly.trans he⟩
  intro i
  rw [Basis.reindex_apply, p.basis_eq_pow]
  rfl

/-- Independent quartic coordinates are an invertible ground-field transform
of the four powers of a primitive element. -/
theorem independent_quartic_coordinates (hdim : finrank K L = 4)
    (p : Vec L 4) (hp : LinearIndependent K p) :
    ∃ a : L, (minpoly K a).natDegree = 4 ∧
      ∃ M : Mat K 4, Function.Injective M.mulVec ∧
        p = (M.map (algebraMap K L)).mulVec (fun i => a^(i : ℕ)) := by
  obtain ⟨a, b, hb, hmin⟩ := exists_power_basis_four hdim
  let M : Mat K 4 := fun i j => b.repr (p i) j
  let phi : Vec K 4 →ₗ[K] L := Fintype.linearCombination K b
  have hM : ∀ i, ∑ j : Fin 4, M i j • b j = p i := fun i => b.sum_repr (p i)
  have hcomp : phi ∘ M = p := by
    funext i
    exact hM i
  have hrows : LinearIndependent K M := LinearIndependent.of_comp phi (by rw [hcomp]; exact hp)
  have hinj : Function.Injective M.mulVec :=
    Matrix.mulVec_injective_iff.mpr (Matrix.Nonsingular.of_linearIndependent_row hrows).linearIndependent_col
  refine ⟨a, hmin, M, hinj, ?_⟩
  funext i
  rw [← hM i]
  simp only [hb, Algebra.smul_def, Matrix.mulVec, dotProduct, Matrix.map_apply]

/-- A cubic with four independent coordinates over a quartic extension has a rational zero. -/
theorem cubic_descent_of_independent_quartic_point (hdim : finrank K L = 4)
    (c : Cubic K 4) (p : Vec L 4) (hp : LinearIndependent K p)
    (hF : (c.map (algebraMap K L)).eval p = 0) :
    ∃ x : Vec K 4, x ≠ 0 ∧ c.eval x = 0 := by
  obtain ⟨a, hmin, M, hinj, hcoord⟩ := independent_quartic_coordinates hdim p hp
  have he : ((c.compLinear M).map (algebraMap K L)).eval (fun i => a^(i : ℕ)) = 0 := by
    rw [Cubic.compLinear_map, Cubic.eval_compLinear, ← hcoord]
    exact hF
  obtain ⟨x, hx, hcx⟩ := canonical_quartic_point_descent (c.compLinear M) a hmin he
  refine ⟨M.mulVec x, ?_, ?_⟩
  · intro hzero
    apply hx
    apply hinj
    simpa only [Matrix.mulVec_zero] using hzero
  · rw [← Cubic.eval_compLinear]
    exact hcx

end
end PfaffianDescent
