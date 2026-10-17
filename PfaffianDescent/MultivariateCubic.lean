import PfaffianDescent.EffectiveCycle
import Mathlib.RingTheory.MvPolynomial.EulerIdentity

namespace PfaffianDescent
open Module
open scoped BigOperators

namespace Cubic
section
variable {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}

/-- The usual multivariate polynomial represented by a cubic coefficient tensor. -/
noncomputable def toMvPolynomial (c : Cubic R n) : MvPolynomial (Fin n) R :=
  ∑ i, MvPolynomial.C (c i) * MvPolynomial.X i.1 * MvPolynomial.X i.2.1 * MvPolynomial.X i.2.2

theorem eval_toMvPolynomial (f : R →+* S) (c : Cubic R n) (x : Vec S n) :
    MvPolynomial.eval₂ f x c.toMvPolynomial = (c.map f).eval x := by
  simp only [toMvPolynomial, MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul,
    MvPolynomial.eval₂_C, MvPolynomial.eval₂_X, eval, map]

end
end Cubic

section
variable {K : Type*} [Field K] [CharZero K] {m n : ℕ}

/-- Euler's identity splits a positive-degree homogeneous polynomial into variables
times forms of one lower degree. -/
theorem homogeneous_split (f : MvPolynomial (Fin m) K) (hf : f.IsHomogeneous (n + 1)) :
    ∃ g : Fin m → MvPolynomial (Fin m) K,
      (∀ i, (g i).IsHomogeneous n) ∧ f = ∑ i, MvPolynomial.X i * g i := by
  let s : K := (n + 1 : K)⁻¹
  let g : Fin m → MvPolynomial (Fin m) K := fun i => s • MvPolynomial.pderiv i f
  have hn : (n + 1 : K) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  refine ⟨g, ?_, ?_⟩
  · intro i
    have hd : (MvPolynomial.pderiv i f).IsHomogeneous n := by simpa using hf.pderiv
    exact (MvPolynomial.homogeneousSubmodule (Fin m) K n).smul_mem s hd
  · symm
    change (∑ i, MvPolynomial.X i * (s • MvPolynomial.pderiv i f)) = f
    simp only [mul_smul_comm, ← Finset.smul_sum]
    rw [hf.sum_X_mul_pderiv, ← Nat.cast_smul_eq_nsmul K, smul_smul]
    have hs : s * ((n + 1 : ℕ) : K) = (1 : K) := by
      simpa only [s, Nat.cast_add, Nat.cast_one] using inv_mul_cancel₀ hn
    rw [hs, one_smul]

/-- Every ordinary homogeneous cubic has a cubic coefficient tensor. -/
theorem homogeneous_cubic_has_tensor (f : MvPolynomial (Fin m) K) (hf : f.IsHomogeneous 3) :
    ∃ c : Cubic K m, c.toMvPolynomial = f := by
  obtain ⟨g, hg, hfg⟩ := homogeneous_split (n := 2) f hf
  choose h hh hgh using fun i => homogeneous_split (n := 1) (g i) (hg i)
  choose q hq hhq using fun i j => homogeneous_split (n := 0) (h i j) (hh i j)
  let c : Cubic K m := fun i => MvPolynomial.coeff 0 (q i.1 i.2.1 i.2.2)
  have hqc : ∀ i j k, q i j k = MvPolynomial.C (c (i, j, k)) := by
    intro i j k
    apply MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp
    exact (MvPolynomial.totalDegree_zero_iff_isHomogeneous (Fin m)).mpr (hq i j k)
  refine ⟨c, ?_⟩
  rw [hfg]
  simp_rw [hgh, hhq, hqc, Finset.mul_sum]
  simp only [Cubic.toMvPolynomial, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

end

section
variable {K L : Type*} [Field K] [CharZero K] [Field L] [Algebra K L] [FiniteDimensional K L]

/-- The degree-five theorem for mathlib's actual multivariate cubic polynomials. -/
theorem homogeneous_cubic_degree_five_descent (f : MvPolynomial (Fin 4) K)
    (hf : f.IsHomogeneous 3) (hdim : finrank K L = 5)
    (p : Vec L 4) (hp : p ≠ 0) (hF : MvPolynomial.eval₂ (algebraMap K L) p f = 0) :
    ∃ x : Vec K 4, x ≠ 0 ∧ MvPolynomial.eval x f = 0 := by
  obtain ⟨c, rfl⟩ := homogeneous_cubic_has_tensor f hf
  rw [Cubic.eval_toMvPolynomial] at hF
  obtain ⟨x, hx, he⟩ := cubic_degree_five_descent hdim c p hp hF
  refine ⟨x, hx, ?_⟩
  change MvPolynomial.eval₂ (RingHom.id K) x c.toMvPolynomial = 0
  rw [Cubic.eval_toMvPolynomial]
  exact he

end

section
variable {K : Type*} [Field K] [CharZero K]

/-- The main effective-cycle theorem for ordinary homogeneous cubic equations.
In particular it applies to every smooth cubic surface over a characteristic-zero field. -/
theorem homogeneous_cubic_effective_degree_five_to_point {ι : Type*} [Fintype ι]
    (L : ι → Type*) [∀ i, Field (L i)] [∀ i, Algebra K (L i)]
    [∀ i, FiniteDimensional K (L i)]
    (f : MvPolynomial (Fin 4) K) (hf : f.IsHomogeneous 3)
    (w : ι → ℕ) (p : ∀ i, Vec (L i) 4)
    (hp : ∀ i, w i ≠ 0 → p i ≠ 0)
    (hF : ∀ i, w i ≠ 0 → MvPolynomial.eval₂ (algebraMap K (L i)) (p i) f = 0)
    (hdegree : ∑ i, w i * finrank K (L i) = 5) :
    ∃ x : Vec K 4, x ≠ 0 ∧ MvPolynomial.eval x f = 0 := by
  obtain ⟨c, rfl⟩ := homogeneous_cubic_has_tensor f hf
  have he : ∀ i, w i ≠ 0 → (c.map (algebraMap K (L i))).eval (p i) = 0 := by
    intro i hi
    simpa only [Cubic.eval_toMvPolynomial] using hF i hi
  obtain ⟨x, hx, hcx⟩ := effective_degree_five_to_point L c w p hp he hdegree
  refine ⟨x, hx, ?_⟩
  change MvPolynomial.eval₂ (RingHom.id K) x c.toMvPolynomial = 0
  rw [Cubic.eval_toMvPolynomial]
  exact hcx

end
end PfaffianDescent
