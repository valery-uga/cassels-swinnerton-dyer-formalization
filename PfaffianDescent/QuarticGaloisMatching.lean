import PfaffianDescent.QuarticGaloisPairDescent
import PfaffianDescent.QuarticMatchingLines
import PfaffianDescent.QuarticTangentRescaling

/-!
# Galois descent in the matching branch

The matching tangent graph yields a Galois-stable pair of cubic points.  The
pair-descent theorem then gives a ground-field cubic point.
-/

namespace PfaffianDescent
namespace QuarticNet

open MvPolynomial Module

universe u

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

theorem matching_edge_cases (a f : K) (i j : Fin 4)
    (h : skewTangentDirections a 0 0 0 0 f i j ≠ 0) :
    (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨ (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) := by
  fin_cases i <;> fin_cases j <;> simp_all [skewTangentDirections]

theorem matching_cubic_vanishes_at_sum
    (B : Basis (Fin 4) K (Fin 4 → K))
    (a f : K) (ha : a ≠ 0) (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (hvan : ∀ r, aeval (tangentDualPoint (skewTangentDirections a 0 0 0 0 f) r)
      (linearSubstitution (basisCoordinateMatrix B) (map (algebraMap k K) F)) = 0) :
    aeval (fun m => B 0 m + B 1 m) F = 0 := by
  let G := linearSubstitution (basisCoordinateMatrix B) (map (algebraMap k K) F)
  let l : Fin 4 → K := ![a⁻¹, (-a)⁻¹, 1, 1]
  have hv := rescaleTangentDirections_vanishing
    (skewTangentDirections a 0 0 0 0 f) l G hvan
  have hx0 : tangentDualPoint (rescaleTangentDirections l
      (skewTangentDirections a 0 0 0 0 f)) 0 =
      ![(1 : DualNumber K), DualNumber.eps, 0, 0] := by
    funext j
    fin_cases j <;>
      simp [tangentDualPoint, rescaleTangentDirections, skewTangentDirections,
        DualNumber.inr_eq_smul_eps, l, ha]
  have hx1 : tangentDualPoint (rescaleTangentDirections l
      (skewTangentDirections a 0 0 0 0 f)) 1 =
      ![DualNumber.eps, (1 : DualNumber K), 0, 0] := by
    funext j
    fin_cases j <;>
      simp [tangentDualPoint, rescaleTangentDirections, skewTangentDirections,
        DualNumber.inr_eq_smul_eps, l, ha]
  have hline : coordinateLineRestriction G = 0 :=
    cubic_contains_coordinate_line_of_double_points G
      (linearSubstitution_homogeneous _ (hF.map (algebraMap k K)))
      (hx0 ▸ hv 0) (hx1 ▸ hv 1)
  have he : (aeval (R := K) (![1, 1] : Fin 2 → K)).comp
      (coordinateLineRestriction (K := K)) =
      aeval (R := K) (![1, 1, 0, 0] : Fin 4 → K) := by
    ext i : 1
    fin_cases i <;> simp [coordinateLineRestriction]
  have hG : aeval (R := K) (![1, 1, 0, 0] : Fin 4 → K) G = 0 := by
    rw [← AlgHom.congr_fun he G, AlgHom.comp_apply, hline, map_zero]
  rw [aeval_linearSubstitution, aeval_def, eval₂_map] at hG
  simpa [aeval_def, basisCoordinateMatrix, Fin.sum_univ_four] using hG

theorem cubic_point_from_galois_matching [IsGalois k K]
    (B : Basis (Fin 4) K (Fin 4 → K)) (a f : K) (ha : a ≠ 0)
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (hvan : ∀ r, aeval (tangentDualPoint (skewTangentDirections a 0 0 0 0 f) r)
      (linearSubstitution (basisCoordinateMatrix B) (map (algebraMap k K) F)) = 0)
    (hact : ∀ g : K ≃ₐ[k] K, ∃ π : Equiv.Perm (Fin 4),
      (∀ i m, g (B i m) = B (π i) m) ∧
      (∀ i j, skewTangentDirections a 0 0 0 0 f i j ≠ 0 ↔
        skewTangentDirections a 0 0 0 0 f (π i) (π j) ≠ 0)) :
    ∃ p : Fin 4 → k, p ≠ 0 ∧ aeval p F = 0 := by
  let x : Fin 4 → K := B 0 + B 1
  let y : Fin 4 → K := B 2 + B 3
  have hx : x ≠ 0 := by
    intro hz
    have h := congrArg (fun v : Fin 4 → K => B.repr v 0) hz
    simp [x] at h
  apply cubic_point_of_galois_pair F hF x y hx
    (matching_cubic_vanishes_at_sum B a f ha F hF hvan)
  intro g
  obtain ⟨π, hB, hπ⟩ := hact g
  have hs (m : Fin 4) : g (x m + y m) = x m + y m := by
    have hsum : ∑ i : Fin 4, g (B i m) = ∑ i : Fin 4, B i m := by
      simp only [hB]
      exact Equiv.sum_comp π (fun i => B i m)
    simpa [x, y, Fin.sum_univ_four, map_add, add_assoc] using hsum
  have hxy : (∀ m, g (x m) = x m) ∨ (∀ m, g (x m) = y m) := by
    have h01 : skewTangentDirections a 0 0 0 0 f 0 1 ≠ 0 := ha
    rcases matching_edge_cases a f (π 0) (π 1) ((hπ 0 1).mp h01) with h | h | h | h
    · exact Or.inl (fun m => by simp [x, map_add, hB, h.1, h.2])
    · exact Or.inl (fun m => by simp [x, map_add, hB, h.1, h.2, add_comm])
    · exact Or.inr (fun m => by simp [x, y, map_add, hB, h.1, h.2])
    · exact Or.inr (fun m => by simp [x, y, map_add, hB, h.1, h.2, add_comm])
  rcases hxy with h | h
  · refine Or.inl ⟨h, ?_⟩
    intro m
    have he := hs m
    rw [map_add, h] at he
    exact add_left_cancel he
  · refine Or.inr ⟨h, ?_⟩
    intro m
    have he := hs m
    rw [map_add, h] at he
    linear_combination he

end QuarticNet
end PfaffianDescent
