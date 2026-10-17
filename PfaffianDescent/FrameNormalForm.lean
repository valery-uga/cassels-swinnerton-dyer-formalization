import PfaffianDescent.FrameEvaluation

namespace PfaffianDescent.FrameCoordinateRing
open Polynomial
open scoped BigOperators

section
variable {K : Type*} [Field K]

/-- Unique normal-form coefficients: a constant, four pure-power tails, and a mixed tail. -/
abbrev NormalData (K : Type*) [Field K] := K × ((Fin 4 → K[X]) × K[X])

noncomputable def normalMap : NormalData K →ₗ[K] FrameCoordinateRing K where
  toFun a := a.1 • 1 + (∑ i : Fin 4, x i * aeval (x i) (a.2.1 i)) +
    q * aeval (x 0) a.2.2
  map_add' a b := by
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, map_add, mul_add,
      add_smul, Finset.sum_add_distrib]
    abel
  map_smul' c a := by
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, map_smul,
      mul_smul_comm, smul_add, Finset.smul_sum, smul_smul]
    rfl

theorem normalMap_constant (c : K) : normalMap (c,0,0) = c • (1 : FrameCoordinateRing K) := by
  simp [normalMap]

theorem normalMap_pure (i : Fin 4) (p : K[X]) :
    normalMap (0, Pi.single i p, 0) = x i * aeval (x i) p := by
  classical
  simp only [normalMap, LinearMap.coe_mk, AddHom.coe_mk, zero_smul, Pi.single_apply,
    map_zero, mul_zero, add_zero, zero_add]
  simp only [apply_ite, map_zero, mul_ite, mul_zero]
  simp

theorem normalMap_mixed (p : K[X]) :
    normalMap (0,0,p) = q * aeval (x (K := K) 0) p := by
  simp [normalMap]

/-- Every class has a normal form with polynomial coefficient tails. -/
theorem normalMap_surjective : Function.Surjective (normalMap (K := K)) := by
  apply LinearMap.range_eq_top.mp
  apply top_unique
  rw [← normalSpan_eq_top]
  apply Submodule.span_le.mpr
  rintro _ ⟨j, rfl⟩
  rcases j with u | (⟨i,n⟩ | n)
  · refine ⟨(1,0,0), ?_⟩
    rw [normalMap_constant, one_smul]
    rfl
  · refine ⟨(0, Pi.single i (X^n), 0), ?_⟩
    rw [normalMap_pure, aeval_X_pow]
    exact (pow_succ' _ _).symm
  · refine ⟨(0,0,X^n), ?_⟩
    rw [normalMap_mixed, aeval_X_pow]
    rfl

theorem atLine_normalMap (p : Option (Fin 4)) (a : NormalData K) :
    atLine p (normalMap a) = C a.1 +
      (∑ i : Fin 4, frameLineVariable p i * aeval (frameLineVariable p i) (a.2.1 i)) +
      (if p = none then X ^ 2 else 0) * aeval (frameLineVariable p 0) a.2.2 := by
  change atLine p (a.1 • (1 : FrameCoordinateRing K) + (∑ i : Fin 4, x i * aeval (x i) (a.2.1 i)) +
    q * aeval (x 0) a.2.2) = _
  simp only [map_add, map_smul, map_one, map_sum, map_mul, atLine_x, atLine_q,
    ← aeval_algHom_apply, Algebra.smul_def, mul_one]
  rfl

theorem atAxis_normalMap (j : Fin 4) (a : NormalData K) :
    atLine (some j) (normalMap a) = C a.1 + X * a.2.1 j := by
  classical
  rw [atLine_normalMap]
  simp only [frameLineVariable, reduceCtorEq, ↓reduceIte, zero_mul, add_zero]
  have he : ∀ i : Fin 4,
      (if i = j then (X : K[X]) else 0) * aeval (if i = j then X else 0) (a.2.1 i) =
      if i = j then X * a.2.1 j else 0 := by
    intro i
    split_ifs with h
    · subst i
      rw [aeval_X_left_apply]
    · rw [zero_mul]
  simp only [he, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

theorem atDiagonal_normalMap (a : NormalData K) :
    atLine none (normalMap a) = C a.1 + (∑ i : Fin 4, X * a.2.1 i) + X ^ 2 * a.2.2 := by
  rw [atLine_normalMap]
  simp only [frameLineVariable, ↓reduceIte, aeval_X_left_apply]

end
end PfaffianDescent.FrameCoordinateRing
