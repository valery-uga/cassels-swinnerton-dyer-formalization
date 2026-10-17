import PfaffianDescent.QuarticBinaryForms
import PfaffianDescent.QuarticTangentInterpolation
import Mathlib.Algebra.DualNumber

/-!
# Coordinate matching lines in the valence-one branch of Section 4
-/

namespace PfaffianDescent
namespace QuarticNet

open MvPolynomial TrivSqZeroExt

section
variable {K : Type*} [Field K]

/-- A homogeneous binary cubic that vanishes to order two at both coordinate
points is identically zero. -/
theorem binary_cubic_eq_zero_of_two_double_points
    (F : MvPolynomial (Fin 2) K) (hF : F.IsHomogeneous 3)
    (h0 : aeval ![1, DualNumber.eps] F = (0 : DualNumber K))
    (h1 : aeval ![DualNumber.eps, 1] F = (0 : DualNumber K)) : F = 0 := by
  obtain ⟨a, b, c, d, heq⟩ := binary_cubic_expansion F hF
  rw [heq] at h0 h1 ⊢
  have ha := congrArg TrivSqZeroExt.fst h0
  have hb := congrArg TrivSqZeroExt.snd h0
  have hc := congrArg TrivSqZeroExt.snd h1
  have hd := congrArg TrivSqZeroExt.fst h1
  simp [pow_succ, TrivSqZeroExt.algebraMap_eq_inl] at ha hb hc hd
  simp [ha, hb, hc, hd]

/-- The same binary calculation with arbitrary nonzero tangent speeds. -/
theorem binary_cubic_eq_zero_of_two_scaled_double_points
    (F : MvPolynomial (Fin 2) K) (hF : F.IsHomogeneous 3)
    (r s : K) (hr : r ≠ 0) (hs : s ≠ 0)
    (h0 : aeval ![1, TrivSqZeroExt.inr r] F = (0 : DualNumber K))
    (h1 : aeval ![TrivSqZeroExt.inr s, 1] F = (0 : DualNumber K)) : F = 0 := by
  obtain ⟨a, b, c, d, heq⟩ := binary_cubic_expansion F hF
  rw [heq] at h0 h1 ⊢
  have ha := congrArg TrivSqZeroExt.fst h0
  have hb := congrArg TrivSqZeroExt.snd h0
  have hc := congrArg TrivSqZeroExt.snd h1
  have hd := congrArg TrivSqZeroExt.fst h1
  simp [pow_succ, TrivSqZeroExt.algebraMap_eq_inl] at ha hb hc hd
  have hb0 : b = 0 := by
    exact hb.resolve_left hr
  have hc0 : c = 0 := by
    exact hc.resolve_left hs
  simp [ha, hb0, hc0, hd]

/-- Restriction to the line through the first two coordinate vertices. -/
noncomputable def coordinateLineRestriction :
    MvPolynomial (Fin 4) K →ₐ[K] MvPolynomial (Fin 2) K :=
  aeval ![X 0, X 1, 0, 0]

theorem coordinateLineRestriction_homogeneous
    {F : MvPolynomial (Fin 4) K} {n : ℕ} (hF : F.IsHomogeneous n) :
    (coordinateLineRestriction F).IsHomogeneous n := by
  apply (one_mul n) ▸ hF.aeval (![X 0, X 1, 0, 0] : Fin 4 → MvPolynomial (Fin 2) K)
  intro i
  fin_cases i <;> simp [isHomogeneous_X, isHomogeneous_zero]

theorem coordinateLineRestriction_evaluate (s t : DualNumber K)
    (F : MvPolynomial (Fin 4) K) :
    aeval ![s, t] (coordinateLineRestriction F) = aeval ![s, t, 0, 0] F := by
  have h : (aeval ![s, t]).comp (coordinateLineRestriction (K := K)) =
      aeval ![s, t, 0, 0] := by
    ext i : 1
    fin_cases i <;> simp [coordinateLineRestriction]
  exact AlgHom.congr_fun h F

/-- A homogeneous cubic containing the two tangent double points of the first
coordinate line contains that entire line. -/
theorem cubic_contains_coordinate_line_of_double_points
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3)
    (h0 : aeval ![1, DualNumber.eps, 0, 0] F = (0 : DualNumber K))
    (h1 : aeval ![DualNumber.eps, 1, 0, 0] F = (0 : DualNumber K)) :
    coordinateLineRestriction F = 0 := by
  apply binary_cubic_eq_zero_of_two_double_points _ (coordinateLineRestriction_homogeneous hF)
  · rwa [coordinateLineRestriction_evaluate]
  · rwa [coordinateLineRestriction_evaluate]


/-- A homogeneous cubic containing two nontrivial tangent double points on
the first coordinate line contains the whole line. -/
theorem cubic_contains_coordinate_line_of_scaled_double_points
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3)
    (r s : K) (hr : r ≠ 0) (hs : s ≠ 0)
    (h0 : aeval ![1, TrivSqZeroExt.inr r, 0, 0] F = (0 : DualNumber K))
    (h1 : aeval ![TrivSqZeroExt.inr s, 1, 0, 0] F = (0 : DualNumber K)) :
    coordinateLineRestriction F = 0 := by
  apply binary_cubic_eq_zero_of_two_scaled_double_points _
    (coordinateLineRestriction_homogeneous hF) r s hr hs
  · rwa [coordinateLineRestriction_evaluate]
  · rwa [coordinateLineRestriction_evaluate]

/-- Restriction to the line through the last two coordinate vertices. -/
noncomputable def coordinateLineRestriction23 :
    MvPolynomial (Fin 4) K →ₐ[K] MvPolynomial (Fin 2) K :=
  aeval ![0, 0, X 0, X 1]

theorem coordinateLineRestriction23_homogeneous
    {F : MvPolynomial (Fin 4) K} {n : ℕ} (hF : F.IsHomogeneous n) :
    (coordinateLineRestriction23 F).IsHomogeneous n := by
  apply (one_mul n) ▸ hF.aeval (![0, 0, X 0, X 1] : Fin 4 → MvPolynomial (Fin 2) K)
  intro i
  fin_cases i <;> simp [isHomogeneous_X, isHomogeneous_zero]

theorem coordinateLineRestriction23_evaluate (s t : DualNumber K)
    (F : MvPolynomial (Fin 4) K) :
    aeval ![s, t] (coordinateLineRestriction23 F) = aeval ![0, 0, s, t] F := by
  have h : (aeval ![s, t]).comp (coordinateLineRestriction23 (K := K)) =
      aeval ![0, 0, s, t] := by
    ext i : 1
    fin_cases i <;> simp [coordinateLineRestriction23]
  exact AlgHom.congr_fun h F

/-- A homogeneous cubic containing the two tangent double points of the last
coordinate line contains that entire line. -/
theorem cubic_contains_coordinate_line23_of_double_points
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3)
    (h0 : aeval ![0, 0, 1, DualNumber.eps] F = (0 : DualNumber K))
    (h1 : aeval ![0, 0, DualNumber.eps, 1] F = (0 : DualNumber K)) :
    coordinateLineRestriction23 F = 0 := by
  apply binary_cubic_eq_zero_of_two_double_points _ (coordinateLineRestriction23_homogeneous hF)
  · rwa [coordinateLineRestriction23_evaluate]
  · rwa [coordinateLineRestriction23_evaluate]

/-- The corresponding statement for the last coordinate line. -/
theorem cubic_contains_coordinate_line23_of_scaled_double_points
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3)
    (r s : K) (hr : r ≠ 0) (hs : s ≠ 0)
    (h0 : aeval ![0, 0, 1, TrivSqZeroExt.inr r] F = (0 : DualNumber K))
    (h1 : aeval ![0, 0, TrivSqZeroExt.inr s, 1] F = (0 : DualNumber K)) :
    coordinateLineRestriction23 F = 0 := by
  apply binary_cubic_eq_zero_of_two_scaled_double_points _
    (coordinateLineRestriction23_homogeneous hF) r s hr hs
  · rwa [coordinateLineRestriction23_evaluate]
  · rwa [coordinateLineRestriction23_evaluate]

/-- The matching graph with edges `{0,1}` and `{2,3}` gives two coordinate
lines contained in every cubic through the four displayed double points. -/
theorem cubic_contains_matching_coordinate_lines_of_double_points
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3)
    (h0 : aeval ![1, DualNumber.eps, 0, 0] F = (0 : DualNumber K))
    (h1 : aeval ![DualNumber.eps, 1, 0, 0] F = (0 : DualNumber K))
    (h2 : aeval ![0, 0, 1, DualNumber.eps] F = (0 : DualNumber K))
    (h3 : aeval ![0, 0, DualNumber.eps, 1] F = (0 : DualNumber K)) :
    coordinateLineRestriction F = 0 ∧ coordinateLineRestriction23 F = 0 :=
  ⟨cubic_contains_coordinate_line_of_double_points F hF h0 h1,
    cubic_contains_coordinate_line23_of_double_points F hF h2 h3⟩

/-- The valence-one normal form of the matching branch contains both
matching coordinate lines. -/
theorem cubic_contains_matching_lines_of_skew_matrix
    (a f : K) (ha : a ≠ 0) (hf : f ≠ 0)
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3)
    (hvan : ∀ i : Fin 4,
      aeval (tangentDualPoint (skewTangentDirections a 0 0 0 0 f) i) F = 0) :
    coordinateLineRestriction F = 0 ∧ coordinateLineRestriction23 F = 0 := by
  have hp0 : tangentDualPoint (skewTangentDirections a 0 0 0 0 f) 0 =
      ![1, TrivSqZeroExt.inr a, 0, 0] := by
    funext j
    fin_cases j <;> simp [tangentDualPoint, skewTangentDirections,
      DualNumber.inr_eq_smul_eps]
  have hp1 : tangentDualPoint (skewTangentDirections a 0 0 0 0 f) 1 =
      ![TrivSqZeroExt.inr (-a), 1, 0, 0] := by
    funext j
    fin_cases j <;> simp [tangentDualPoint, skewTangentDirections,
      DualNumber.inr_eq_smul_eps]
  have hp2 : tangentDualPoint (skewTangentDirections a 0 0 0 0 f) 2 =
      ![0, 0, 1, TrivSqZeroExt.inr f] := by
    funext j
    fin_cases j <;> simp [tangentDualPoint, skewTangentDirections,
      DualNumber.inr_eq_smul_eps]
  have hp3 : tangentDualPoint (skewTangentDirections a 0 0 0 0 f) 3 =
      ![0, 0, TrivSqZeroExt.inr (-f), 1] := by
    funext j
    fin_cases j <;> simp [tangentDualPoint, skewTangentDirections,
      DualNumber.inr_eq_smul_eps]
  have h0 : aeval ![1, TrivSqZeroExt.inr a, 0, 0] F = (0 : DualNumber K) := by
    rw [← hp0]
    exact hvan 0
  have h1 : aeval ![TrivSqZeroExt.inr (-a), 1, 0, 0] F = (0 : DualNumber K) := by
    rw [← hp1]
    exact hvan 1
  have h2 : aeval ![0, 0, 1, TrivSqZeroExt.inr f] F = (0 : DualNumber K) := by
    rw [← hp2]
    exact hvan 2
  have h3 : aeval ![0, 0, TrivSqZeroExt.inr (-f), 1] F = (0 : DualNumber K) := by
    rw [← hp3]
    exact hvan 3
  refine ⟨cubic_contains_coordinate_line_of_scaled_double_points F hF a (-a) ha
    (neg_ne_zero.mpr ha) h0 h1, ?_⟩
  exact cubic_contains_coordinate_line23_of_scaled_double_points F hF f (-f) hf
    (neg_ne_zero.mpr hf) h2 h3

end
end QuarticNet
end PfaffianDescent
