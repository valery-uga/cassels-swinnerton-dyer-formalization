import AllCharacteristics.TangentHyperplaneGeneric

namespace PfaffianDescent

open scoped BigOperators

universe u

/-- Solving for a nonzero coefficient recovers every vector of the hyperplane,
not merely a subset of it. -/
theorem hyperplaneInclusion_mulVec_coordinateOmission_of_dot_eq_zero
    {K : Type u} [Field K] (g : Fin 4 → K) (k : Fin 4)
    (hk : g k ≠ 0) (d : Fin 4 → K)
    (hd : ∑ i, g i * d i = 0) :
    (hyperplaneInclusion g k).mulVec (fun j => d (k.succAbove j)) = d := by
  classical
  let S : K := ∑ j : Fin 3, g (k.succAbove j) * d (k.succAbove j)
  have hsum : g k * d k + S = 0 := by
    simpa only [Fin.sum_univ_succAbove _ k, S] using hd
  have hdk : d k = -(g k)⁻¹ * S := by
    calc
      d k = (g k)⁻¹ * (g k * d k) := by
        rw [← mul_assoc, inv_mul_cancel₀ hk, one_mul]
      _ = -(g k)⁻¹ * S := by
        rw [eq_neg_of_add_eq_zero_left hsum]
        ring
  funext i
  by_cases hi : i = k
  · subst i
    change (∑ j : Fin 3, hyperplaneInclusion g k k j * d (k.succAbove j)) = d k
    calc
      _ = -(g k)⁻¹ * S := by
        simp only [hyperplaneInclusion, ↓reduceIte, S, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = d k := hdk.symm
  · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hi
    simp [Matrix.mulVec, dotProduct, hyperplaneInclusion, Fin.succAbove_ne,
      Fin.succAbove_right_inj]

end PfaffianDescent

namespace AllCharacteristics

open PfaffianDescent MvPolynomial

universe u

/-- The explicit gradient matrix parametrizes the entire tangent hyperplane,
over every field and without a smoothness assumption away from the pivot. -/
theorem tangentHyperplane_direction_eq_matrix_coordinates
    {K : Type u} [Field K] (c : Cubic K 4) (p d : Fin 4 → K)
    (k : Fin 4) (hk : (MvPolynomial.pderiv k c.toMvPolynomial).eval p ≠ 0)
    (hd : c.mixed p d = 0) :
    (hyperplaneInclusion
      (fun i => (MvPolynomial.pderiv i c.toMvPolynomial).eval p) k).mulVec
      (fun j => d (k.succAbove j)) = d := by
  apply hyperplaneInclusion_mulVec_coordinateOmission_of_dot_eq_zero _ k hk d
  rw [Cubic.mixed_eq_sum_pderiv_eval] at hd
  simpa only [mul_comm] using hd

end AllCharacteristics
