import PfaffianDescent.GroundFrameChosenQuadraticResidualIntersection
import AllCharacteristics.CubicPolynomialCoordinates

/-! SOURCE ONLY / UNVERIFIED. Normalize the SAME chosen vector inside the
SAME ground frame determined by its actual two-conjugate span. No new frame,
generator, nonzero normalization, moved element or cubic root is supplied. -/
noncomputable section
namespace PfaffianDescent
open Module MvPolynomial
open scoped BigOperators
open QuarticNet
universe u
variable {k E : Type u} [Field k] [Field E] [Algebra k E]

/-- The fixed two-conjugate space determines coordinates in the SAME C.
Independence forces its first coordinate to be nonzero and its ratio to
move under sigma; both facts are proved internally. -/
theorem chosenConjugateVector_normalizes_in_same_groundFrame
    (sigma : E ≃ₐ[k] E) (x : Fin 4 → E)
    (hLI : LinearIndependent E ![x, fun m => sigma (x m)])
    (C : Basis (Fin 4) k (Fin 4 → k))
    (hSpan : Submodule.span E (Set.range ![x, fun m => sigma (x m)]) =
      Submodule.span E (Set.range ![(fun m => algebraMap k E (C 0 m)),
        (fun m => algebraMap k E (C 1 m))])) :
    ∃ lambda alpha : E, lambda ≠ 0 ∧ alpha ≠ sigma alpha ∧
      x = lambda • ((fun m => algebraMap k E (C 0 m)) +
        alpha • (fun m => algebraMap k E (C 1 m))) := by
  classical
  let U : Fin 4 → E := fun m => algebraMap k E (C 0 m)
  let V : Fin 4 → E := fun m => algebraMap k E (C 1 m)
  let y : Fin 4 → E := fun m => sigma (x m)
  have hxne : x ≠ 0 := by simpa only [Matrix.cons_val_zero] using hLI.ne_zero 0
  have hxSpan : x ∈ Submodule.span E (Set.range ![U, V]) := by
    rw [← hSpan]
    exact Submodule.subset_span ⟨0, rfl⟩
  rw [Matrix.range_cons_cons_empty] at hxSpan
  obtain ⟨A, B, hAB⟩ := Submodule.mem_span_pair.mp hxSpan
  have hx : x = A • U + B • V := hAB.symm
  have hy : y = sigma A • U + sigma B • V := by
    funext m
    have hm := congrFun hx m
    change sigma (x m) = _
    change x m = A * algebraMap k E (C 0 m) + B * algebraMap k E (C 1 m) at hm
    rw [hm, map_add, map_mul, map_mul, sigma.commutes, sigma.commutes]
    rfl
  have hA : A ≠ 0 := by
    intro hA0
    have he : sigma B • x + (-B) • y = 0 := by
      funext m
      rw [hx, hy]
      change sigma B * (A * U m + B * V m) +
        (-B) * (sigma A * U m + sigma B * V m) = 0
      rw [hA0, map_zero]
      ring
    have hsums : ∑ i : Fin 2, ![sigma B, -B] i • ![x, y] i = 0 := by
      simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons] using he
    have hcoeff := Fintype.linearIndependent_iff.mp hLI ![sigma B, -B] hsums
    have hB0 : B = 0 := neg_eq_zero.mp (hcoeff 1)
    apply hxne
    rw [hx, hA0, hB0, zero_smul, zero_smul, add_zero]
  let alpha := B / A
  have hNorm : x = A • (U + alpha • V) := by
    funext m
    rw [hx]
    change A * U m + B * V m = A * (U m + (B / A) * V m)
    field_simp [hA] <;> ring
  have hAlpha : alpha ≠ sigma alpha := by
    intro hFixed
    have hyNorm : y = sigma A • (U + alpha • V) := by
      funext m
      have hm := congrFun hNorm m
      change sigma (x m) = _
      change x m = A * (algebraMap k E (C 0 m) +
        alpha * algebraMap k E (C 1 m)) at hm
      rw [hm, map_mul, map_add, map_mul, sigma.commutes, sigma.commutes, ← hFixed]
      rfl
    have he : sigma A • x + (-A) • y = 0 := by
      rw [hNorm, hyNorm, smul_smul, smul_smul, ← add_smul]
      have hz : sigma A * A + (-A) * sigma A = 0 := by ring
      rw [hz, zero_smul]
    have hsums : ∑ i : Fin 2, ![sigma A, -A] i • ![x, y] i = 0 := by
      simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons] using he
    have hcoeff := Fintype.linearIndependent_iff.mp hLI ![sigma A, -A] hsums
    exact hA (neg_eq_zero.mp (hcoeff 1))
  exact ⟨A, alpha, hA, hAlpha, hNorm⟩

/-- Homogeneity cancels only the internally derived nonzero scalar.
This concerns the original polynomial and fixed C, in every characteristic. -/
theorem chosenConjugatePoint_sameFrame_cubicRoot
    (C : Basis (Fin 4) k (Fin 4 → k))
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (x : Fin 4 → E) (lambda alpha : E) (hlambda : lambda ≠ 0)
    (hNorm : x = lambda • ((fun m => algebraMap k E (C 0 m)) +
      alpha • (fun m => algebraMap k E (C 1 m))))
    (hFx : aeval x F = 0) :
    aeval ![1, alpha] (groundFrameLineRestriction C F) = (0 : E) := by
  let z : Fin 4 → E := (fun m => algebraMap k E (C 0 m)) +
    alpha • (fun m => algebraMap k E (C 1 m))
  have hScale : aeval x F = lambda ^ 3 * aeval z F := by
    obtain ⟨t, ht⟩ := AllCharacteristics.homogeneous_cubic_has_tensor_any_characteristic F hF
    rw [← ht, aeval_def, aeval_def, Cubic.eval_toMvPolynomial,
      Cubic.eval_toMvPolynomial, hNorm]
    exact Cubic.eval_smul (t.map (algebraMap k E)) z lambda
  have hz : aeval z F = 0 :=
    (mul_eq_zero.mp (hScale.symm.trans hFx)).resolve_left (pow_ne_zero 3 hlambda)
  have hEval := groundFrameLineRestriction_aeval C (![1, alpha] : Fin 2 → E) F
  have hCoordinates :
      (fun m => algebraMap k E (C 0 m) * (![1, alpha] : Fin 2 → E) 0 +
        algebraMap k E (C 1 m) * (![1, alpha] : Fin 2 → E) 1) = z := by
    funext m
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      mul_one, z, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_comm]
  rw [hCoordinates] at hEval
  exact hEval.trans hz

end PfaffianDescent
