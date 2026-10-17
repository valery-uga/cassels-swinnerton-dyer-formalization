import PfaffianDescent.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Linear algebra of quadrics through four tangent double points

This is the coordinate calculation in Lemma 5.3 of `2-proofs.tex`.
The six coordinates of `q` are the coefficients of
`x₀x₁, x₀x₂, x₀x₃, x₁x₂, x₁x₃, x₂x₃`; the four coordinates of the
output are the directional derivatives at the four coordinate vertices.
-/

namespace PfaffianDescent
namespace QuarticNet

section
variable {K : Type*} [Field K]

/-- Directional evaluations of the six off-diagonal quadrics at four coordinate
vertices with tangent-direction coefficients `u`. -/
def tangentQuadricEvaluation (u : Fin 4 → Fin 4 → K) (q : Fin 6 → K) : Fin 4 → K :=
  ![q 0 * u 0 1 + q 1 * u 0 2 + q 2 * u 0 3,
    q 0 * u 1 0 + q 3 * u 1 2 + q 4 * u 1 3,
    q 1 * u 2 0 + q 3 * u 2 1 + q 5 * u 2 3,
    q 2 * u 3 0 + q 4 * u 3 1 + q 5 * u 3 2]

/-- The weighted linear dependence of the four directional-evaluation
functionals. -/
def weightedTangentQuadricEvaluation (u : Fin 4 → Fin 4 → K)
    (w : Fin 4 → K) (q : Fin 6 → K) : K :=
  ∑ i, w i * tangentQuadricEvaluation u q i

/-- The directional-evaluation map from the six-dimensional space of
off-diagonal quadrics to the four tangent conditions. -/
def tangentQuadricEvaluationLinearMap (u : Fin 4 → Fin 4 → K) :
    (Fin 6 → K) →ₗ[K] (Fin 4 → K) where
  toFun := tangentQuadricEvaluation u
  map_add' q r := by
    funext i
    fin_cases i <;> simp [tangentQuadricEvaluation] <;> ring
  map_smul' t q := by
    funext i
    fin_cases i <;> simp [tangentQuadricEvaluation] <;> ring

/-- The linear functional with coefficients `w` on the four tangent
conditions. -/
def weightedTangentFunctional (w : Fin 4 → K) : (Fin 4 → K) →ₗ[K] K where
  toFun v := ∑ i, w i * v i
  map_add' v z := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' t v := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

theorem weightedTangentFunctional_apply (w v : Fin 4 → K) :
    weightedTangentFunctional w v = ∑ i, w i * v i := rfl

/-- The six weighted skew relations, viewed as a linear map in the weights. -/
def weightedRelationLinearMap (u : Fin 4 → Fin 4 → K) :
    (Fin 4 → K) →ₗ[K] (Fin 6 → K) where
  toFun w := ![w 0 * u 0 1 + w 1 * u 1 0,
    w 0 * u 0 2 + w 2 * u 2 0,
    w 0 * u 0 3 + w 3 * u 3 0,
    w 1 * u 1 2 + w 2 * u 2 1,
    w 1 * u 1 3 + w 3 * u 3 1,
    w 2 * u 2 3 + w 3 * u 3 2]
  map_add' w z := by
    funext i
    fin_cases i <;> simp <;> ring
  map_smul' a w := by
    funext i
    fin_cases i <;> simp [smul_eq_mul] <;> ring

/-- Membership in the kernel of `weightedRelationLinearMap` is the six
relations displayed in Lemma 5.3. -/
theorem mem_ker_weightedRelationLinearMap_iff
    (u : Fin 4 → Fin 4 → K) (w : Fin 4 → K) :
    w ∈ LinearMap.ker (weightedRelationLinearMap u) ↔
      (w 0 * u 0 1 + w 1 * u 1 0 = 0) ∧
      (w 0 * u 0 2 + w 2 * u 2 0 = 0) ∧
      (w 0 * u 0 3 + w 3 * u 3 0 = 0) ∧
      (w 1 * u 1 2 + w 2 * u 2 1 = 0) ∧
      (w 1 * u 1 3 + w 3 * u 3 1 = 0) ∧
      (w 2 * u 2 3 + w 3 * u 3 2 = 0) := by
  constructor
  · intro h
    change weightedRelationLinearMap u w = 0 at h
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      first | exact congrFun h 0 | exact congrFun h 1 | exact congrFun h 2 |
        exact congrFun h 3 | exact congrFun h 4 | exact congrFun h 5
  · rintro ⟨h01, h02, h03, h12, h13, h23⟩
    change weightedRelationLinearMap u w = 0
    funext i
    fin_cases i <;> assumption

/-- A finite-dimensional coordinate-space version of the fact that a finite
union of proper subspaces cannot cover a vector space over an infinite field. -/
theorem Submodule.exists_mem_all_coordinate_ne_zero
    [Infinite K] (R : Submodule K (Fin 4 → K))
    (hcoordinate : ∀ i : Fin 4, ∃ w ∈ R, w i ≠ 0) :
    ∃ w ∈ R, ∀ i : Fin 4, w i ≠ 0 := by
  apply Module.Dual.exists_forall_mem_ne_zero_of_forall_exists R
    (fun i => LinearMap.proj i)
  intro i
  obtain ⟨w, hwR, hwi⟩ := hcoordinate i
  exact ⟨w, hwR, hwi⟩

theorem weightedTangentFunctional_ne_zero {w : Fin 4 → K} (hw : w ≠ 0) :
    weightedTangentFunctional w ≠ 0 := by
  intro hz
  apply hw
  funext i
  have hi := congrArg (fun F : (Fin 4 → K) →ₗ[K] K => F (Pi.single i 1)) hz
  fin_cases i <;> simpa [weightedTangentFunctional, Fin.sum_univ_four] using hi

/-- The six coefficient relations imply a linear dependence of the four
directional-evaluation functionals. -/
theorem weightedTangentQuadricEvaluation_eq_zero_of_relations
    (u : Fin 4 → Fin 4 → K) (w : Fin 4 → K)
    (h01 : w 0 * u 0 1 + w 1 * u 1 0 = 0)
    (h02 : w 0 * u 0 2 + w 2 * u 2 0 = 0)
    (h03 : w 0 * u 0 3 + w 3 * u 3 0 = 0)
    (h12 : w 1 * u 1 2 + w 2 * u 2 1 = 0)
    (h13 : w 1 * u 1 3 + w 3 * u 3 1 = 0)
    (h23 : w 2 * u 2 3 + w 3 * u 3 2 = 0)
    (q : Fin 6 → K) : weightedTangentQuadricEvaluation u w q = 0 := by
  rw [weightedTangentQuadricEvaluation, Fin.sum_univ_four]
  change w 0 * (q 0 * u 0 1 + q 1 * u 0 2 + q 2 * u 0 3) +
      w 1 * (q 0 * u 1 0 + q 3 * u 1 2 + q 4 * u 1 3) +
      w 2 * (q 1 * u 2 0 + q 3 * u 2 1 + q 5 * u 2 3) +
      w 3 * (q 2 * u 3 0 + q 4 * u 3 1 + q 5 * u 3 2) = 0
  linear_combination q 0 * h01 + q 1 * h02 + q 2 * h03 +
    q 3 * h12 + q 4 * h13 + q 5 * h23

/-- Conversely, a weighted linear dependence of the four directional
evaluations gives precisely the six skew relations from the paper. -/
theorem tangentQuadric_relations_of_weighted_eq_zero
    (u : Fin 4 → Fin 4 → K) (w : Fin 4 → K)
    (h : ∀ q : Fin 6 → K, weightedTangentQuadricEvaluation u w q = 0) :
    (w 0 * u 0 1 + w 1 * u 1 0 = 0) ∧
      (w 0 * u 0 2 + w 2 * u 2 0 = 0) ∧
      (w 0 * u 0 3 + w 3 * u 3 0 = 0) ∧
      (w 1 * u 1 2 + w 2 * u 2 1 = 0) ∧
      (w 1 * u 1 3 + w 3 * u 3 1 = 0) ∧
      (w 2 * u 2 3 + w 3 * u 3 2 = 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · specialize h (Pi.single 0 1)
    rw [weightedTangentQuadricEvaluation, Fin.sum_univ_four] at h
    simpa [tangentQuadricEvaluation] using h
  · specialize h (Pi.single 1 1)
    rw [weightedTangentQuadricEvaluation, Fin.sum_univ_four] at h
    simpa [tangentQuadricEvaluation] using h
  · specialize h (Pi.single 2 1)
    rw [weightedTangentQuadricEvaluation, Fin.sum_univ_four] at h
    simpa [tangentQuadricEvaluation] using h
  · specialize h (Pi.single 3 1)
    rw [weightedTangentQuadricEvaluation, Fin.sum_univ_four] at h
    simpa [tangentQuadricEvaluation] using h
  · specialize h (Pi.single 4 1)
    rw [weightedTangentQuadricEvaluation, Fin.sum_univ_four] at h
    simpa [tangentQuadricEvaluation] using h
  · specialize h (Pi.single 5 1)
    rw [weightedTangentQuadricEvaluation, Fin.sum_univ_four] at h
    simpa [tangentQuadricEvaluation] using h

/-- A nontrivial weighted relation leaves at least three independent quadrics
through the four tangent double points.  This is the dimension conclusion in
the forward direction of Lemma 5.3 of `2-proofs.tex`. -/
theorem three_le_finrank_ker_tangentQuadricEvaluation_of_weighted_relation
    (u : Fin 4 → Fin 4 → K) (w : Fin 4 → K) (hw : w ≠ 0)
    (h : ∀ q : Fin 6 → K, weightedTangentQuadricEvaluation u w q = 0) :
    3 ≤ Module.finrank K (LinearMap.ker (tangentQuadricEvaluationLinearMap u)) := by
  let T := tangentQuadricEvaluationLinearMap u
  let W := weightedTangentFunctional w
  change 3 ≤ Module.finrank K (LinearMap.ker T)
  have hrange : LinearMap.range T ≤ LinearMap.ker W := by
    intro y hy
    obtain ⟨q, rfl⟩ := hy
    change weightedTangentQuadricEvaluation u w q = 0
    exact h q
  have hkerW : Module.finrank K (LinearMap.ker W) = 3 := by
    have hsum := Module.Dual.finrank_ker_add_one_of_ne_zero
      (f := W) (weightedTangentFunctional_ne_zero hw)
    rw [show Module.finrank K (Fin 4 → K) = 4 by simp] at hsum
    omega
  have hrank : Module.finrank K (LinearMap.range T) ≤ 3 :=
    (Submodule.finrank_mono hrange).trans_eq hkerW
  have hsum := T.finrank_range_add_finrank_ker
  rw [show Module.finrank K (Fin 6 → K) = 6 by simp] at hsum
  omega

/-- A linear functional on a finite coordinate space is recovered from its
values on the coordinate vectors. -/
theorem dual_apply_eq_sum_coordinate
    (φ : Module.Dual K (Fin 4 → K)) (v : Fin 4 → K) :
    φ v = ∑ i, φ (Pi.single i 1) * v i := by
  have hv : v = ∑ i, v i • Pi.single i 1 := by
    ext j
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply]
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      rw [if_neg hij.symm, smul_zero]
    · simp
  calc
    φ v = φ (∑ i, v i • Pi.single i 1) := congrArg φ hv
    _ = ∑ i, φ (Pi.single i 1) * v i := by
      rw [map_sum]
      simp only [map_smul, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- The dimension hypothesis in Lemma 5.3 of `2-proofs.tex` supplies a
nonzero weighted relation among the four tangent conditions. -/
theorem exists_nonzero_weighted_relation_of_three_le_finrank_ker
    (u : Fin 4 → Fin 4 → K)
    (hker : 3 ≤ Module.finrank K (LinearMap.ker (tangentQuadricEvaluationLinearMap u))) :
    ∃ w : Fin 4 → K, w ≠ 0 ∧
      ∀ q : Fin 6 → K, weightedTangentQuadricEvaluation u w q = 0 := by
  let T := tangentQuadricEvaluationLinearMap u
  change 3 ≤ Module.finrank K (LinearMap.ker T) at hker
  have hrange : Module.finrank K (LinearMap.range T) ≤ 3 := by
    have hsum := T.finrank_range_add_finrank_ker
    rw [show Module.finrank K (Fin 6 → K) = 6 by simp] at hsum
    omega
  have hannpos : 0 < Module.finrank K (LinearMap.range T).dualAnnihilator := by
    have hsum := Subspace.finrank_add_finrank_dualAnnihilator_eq (LinearMap.range T)
    rw [show Module.finrank K (Fin 4 → K) = 4 by simp] at hsum
    omega
  have hann : (LinearMap.range T).dualAnnihilator ≠ ⊥ := by
    intro he
    have hz : Module.finrank K (LinearMap.range T).dualAnnihilator = 0 := by
      rw [he]
      simp
    omega
  obtain ⟨φ, hφ, hφ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hann
  let w : Fin 4 → K := fun i => φ (Pi.single i 1)
  have hw : w ≠ 0 := by
    intro hw
    apply hφ0
    apply LinearMap.ext
    intro v
    rw [dual_apply_eq_sum_coordinate]
    have hwi : ∀ i, φ (Pi.single i 1) = 0 := by
      intro i
      have h := congrFun hw i
      simpa [w] using h
    simp [hwi]
  refine ⟨w, hw, ?_⟩
  intro q
  have hφT : φ (T q) = 0 :=
    (Submodule.mem_dualAnnihilator φ).mp hφ (T q) ⟨q, rfl⟩
  change ∑ i, w i * T q i = 0
  rw [← dual_apply_eq_sum_coordinate]
  exact hφT

/-- The complete coordinate form of Lemma 5.3: the space of quadrics through
the four tangent double points has dimension at least three exactly when the
six displayed weighted skew relations have a nonzero solution. -/
theorem three_le_finrank_ker_tangentQuadricEvaluation_iff
    (u : Fin 4 → Fin 4 → K) :
    3 ≤ Module.finrank K (LinearMap.ker (tangentQuadricEvaluationLinearMap u)) ↔
      ∃ w : Fin 4 → K, w ≠ 0 ∧
        (w 0 * u 0 1 + w 1 * u 1 0 = 0) ∧
        (w 0 * u 0 2 + w 2 * u 2 0 = 0) ∧
        (w 0 * u 0 3 + w 3 * u 3 0 = 0) ∧
        (w 1 * u 1 2 + w 2 * u 2 1 = 0) ∧
        (w 1 * u 1 3 + w 3 * u 3 1 = 0) ∧
        (w 2 * u 2 3 + w 3 * u 3 2 = 0) := by
  constructor
  · intro hker
    obtain ⟨w, hw, hweighted⟩ :=
      exists_nonzero_weighted_relation_of_three_le_finrank_ker u hker
    exact ⟨w, hw, tangentQuadric_relations_of_weighted_eq_zero u w hweighted⟩
  · rintro ⟨w, hw, h01, h02, h03, h12, h13, h23⟩
    apply three_le_finrank_ker_tangentQuadricEvaluation_of_weighted_relation u w hw
    exact weightedTangentQuadricEvaluation_eq_zero_of_relations u w h01 h02 h03 h12 h13 h23

/-- Rescaling the four tangent-direction representatives by a weighted
relation with no zero coordinate makes their coefficient matrix
skew-symmetric. This is the final coordinate step of `lem:uij=-uji`. -/
def rescaleTangentDirections (w : Fin 4 → K) (u : Fin 4 → Fin 4 → K) :
    Fin 4 → Fin 4 → K :=
  fun i j => w i * u i j

theorem rescaleTangentDirections_skew_of_relations
    (u : Fin 4 → Fin 4 → K) (w : Fin 4 → K)
    (hdiag : ∀ i, u i i = 0)
    (h01 : w 0 * u 0 1 + w 1 * u 1 0 = 0)
    (h02 : w 0 * u 0 2 + w 2 * u 2 0 = 0)
    (h03 : w 0 * u 0 3 + w 3 * u 3 0 = 0)
    (h12 : w 1 * u 1 2 + w 2 * u 2 1 = 0)
    (h13 : w 1 * u 1 3 + w 3 * u 3 1 = 0)
    (h23 : w 2 * u 2 3 + w 3 * u 3 2 = 0) :
    ∀ i j, rescaleTangentDirections w u i j = -rescaleTangentDirections w u j i := by
  intro i j
  fin_cases i <;> fin_cases j
  · change w 0 * u 0 0 = -(w 0 * u 0 0)
    rw [hdiag 0]
    ring
  · change w 0 * u 0 1 = -(w 1 * u 1 0)
    linear_combination h01
  · change w 0 * u 0 2 = -(w 2 * u 2 0)
    linear_combination h02
  · change w 0 * u 0 3 = -(w 3 * u 3 0)
    linear_combination h03
  · change w 1 * u 1 0 = -(w 0 * u 0 1)
    linear_combination h01
  · change w 1 * u 1 1 = -(w 1 * u 1 1)
    rw [hdiag 1]
    ring
  · change w 1 * u 1 2 = -(w 2 * u 2 1)
    linear_combination h12
  · change w 1 * u 1 3 = -(w 3 * u 3 1)
    linear_combination h13
  · change w 2 * u 2 0 = -(w 0 * u 0 2)
    linear_combination h02
  · change w 2 * u 2 1 = -(w 1 * u 1 2)
    linear_combination h12
  · change w 2 * u 2 2 = -(w 2 * u 2 2)
    rw [hdiag 2]
    ring
  · change w 2 * u 2 3 = -(w 3 * u 3 2)
    linear_combination h23
  · change w 3 * u 3 0 = -(w 0 * u 0 3)
    linear_combination h03
  · change w 3 * u 3 1 = -(w 1 * u 1 3)
    linear_combination h13
  · change w 3 * u 3 2 = -(w 2 * u 2 3)
    linear_combination h23
  · change w 3 * u 3 3 = -(w 3 * u 3 3)
    rw [hdiag 3]
    ring

/-- If every coordinate can be nonzero on some weighted relation, then over
an infinite field one relation has all four coordinates nonzero. -/
theorem exists_weighted_relation_all_coordinates_ne_zero
    [Infinite K] (u : Fin 4 → Fin 4 → K)
    (hcoordinate : ∀ i : Fin 4,
      ∃ w ∈ LinearMap.ker (weightedRelationLinearMap u), w i ≠ 0) :
    ∃ w ∈ LinearMap.ker (weightedRelationLinearMap u),
      ∀ i : Fin 4, w i ≠ 0 :=
  Submodule.exists_mem_all_coordinate_ne_zero
    (LinearMap.ker (weightedRelationLinearMap u)) hcoordinate

/-- The Galois-theoretic nonvanishing input in `lem:uij=-uji` has a purely
linear conclusion: one can rescale the tangent directions so that their
matrix is skew-symmetric. -/
theorem exists_rescaling_skew_of_weighted_relation_coordinates
    [Infinite K] (u : Fin 4 → Fin 4 → K)
    (hdiag : ∀ i, u i i = 0)
    (hcoordinate : ∀ i : Fin 4,
      ∃ w ∈ LinearMap.ker (weightedRelationLinearMap u), w i ≠ 0) :
    ∃ w : Fin 4 → K, (∀ i : Fin 4, w i ≠ 0) ∧
      ∀ i j, rescaleTangentDirections w u i j = -rescaleTangentDirections w u j i := by
  obtain ⟨w, hw, hwne⟩ := exists_weighted_relation_all_coordinates_ne_zero u hcoordinate
  obtain ⟨h01, h02, h03, h12, h13, h23⟩ :=
    (mem_ker_weightedRelationLinearMap_iff u w).mp hw
  refine ⟨w, hwne, ?_⟩
  exact rescaleTangentDirections_skew_of_relations u w hdiag h01 h02 h03 h12 h13 h23

/-- Evaluation of a linear form on four homogeneous coordinates. -/
def linearFormEval (h x : Fin 4 → K) : K := ∑ i, h i * x i

/-- The map defined by a triple of linear forms. -/
def threeLinearFormsMap (h : Fin 3 → Fin 4 → K) :
    (Fin 4 → K) →ₗ[K] (Fin 3 → K) where
  toFun x i := linearFormEval (h i) x
  map_add' x y := by
    funext i
    simp only [linearFormEval, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' t x := by
    funext i
    simp only [linearFormEval, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring

/-- Three linear forms in four variables have a nonzero common zero. -/
theorem exists_nonzero_common_zero_of_three_linear_forms (h : Fin 3 → Fin 4 → K) :
    ∃ x : Fin 4 → K, x ≠ 0 ∧ ∀ i, linearFormEval (h i) x = 0 := by
  let H := threeLinearFormsMap h
  have hker : LinearMap.ker H ≠ ⊥ := H.ker_ne_bot_of_finrank_lt (by simp)
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  refine ⟨x, hx0, ?_⟩
  intro i
  have hHx : H x = 0 := hx
  exact congrFun hHx i

/-- The elementary rational-point criterion used before the net-of-quadrics
lemma: a cubic expressed as three linear multiples has a nonzero rational
zero.  The functions `Q i` stand for the three quadratic evaluations. -/
theorem cubic_zero_of_three_linear_quadric_decomposition
    (F : (Fin 4 → K) → K) (H : Fin 3 → Fin 4 → K)
    (Q : Fin 3 → (Fin 4 → K) → K)
    (hdecomp : ∀ x, F x = ∑ i, linearFormEval (H i) x * Q i x) :
    ∃ x : Fin 4 → K, x ≠ 0 ∧ F x = 0 := by
  obtain ⟨x, hx, hHx⟩ := exists_nonzero_common_zero_of_three_linear_forms H
  refine ⟨x, hx, ?_⟩
  rw [hdecomp]
  apply Finset.sum_eq_zero
  intro i _
  rw [hHx i, zero_mul]

end

section
variable {K : Type*} [Field K]

/-- The skew matrix of tangent-direction coefficients used in the nondegenerate
case of the base-locus calculation. -/
def skewTangentDirections (a b c d e f : K) : Fin 4 → Fin 4 → K :=
  ![![0, a, b, c], ![-a, 0, d, e], ![-b, -d, 0, f], ![-c, -e, -f, 0]]

/-- The first quadric in the base-locus computation, represented by its six
off-diagonal coefficients. -/
def baseLocusQuadric1 (a b _c d _e _f : K) : Fin 6 → K :=
  ![d / a, -d / b, 0, 1, 0, 0]

/-- The second quadric in the base-locus computation. -/
def baseLocusQuadric2 (a _b c _d e _f : K) : Fin 6 → K :=
  ![e / a, 0, -e / c, 0, 1, 0]

/-- The third quadric in the base-locus computation. -/
def baseLocusQuadric3 (_a b c _d _e f : K) : Fin 6 → K :=
  ![0, f / b, -f / c, 0, 0, 1]

/-- Evaluation of a quadric with no square terms. -/
def offDiagonalQuadricEval (q : Fin 6 → K) (x : Fin 4 → K) : K :=
  q 0 * x 0 * x 1 + q 1 * x 0 * x 2 + q 2 * x 0 * x 3 +
    q 3 * x 1 * x 2 + q 4 * x 1 * x 3 + q 5 * x 2 * x 3

/-- The cubic parameterization obtained in the `Δ = 0` case of the
base-locus computation. -/
def baseLocusCubicParam (a b c d e : K) (s t : K) : Fin 4 → K :=
  ![a * s * (d * s - b * t) * (e * s - c * t),
    a * t * (d * s - b * t) * (e * s - c * t),
    b * d * s * t * (e * s - c * t),
    c * e * s * t * (d * s - b * t)]

/-- The coefficient matrix of the four cubic forms in the exceptional
parametrization, in the basis `s³, s²t, st², t³`. -/
def baseLocusCubicCoefficientMatrix (a b c d e : K) : Matrix (Fin 4) (Fin 4) K :=
  !![a * d * e, -a * (d * c + b * e), a * b * c, 0;
    0, a * d * e, -a * (d * c + b * e), a * b * c;
    0, b * d * e, -b * c * d, 0;
    0, c * d * e, -b * c * e, 0]

/-- The displayed parameterization is the coefficient matrix applied to the
standard cubic monomial vector. -/
theorem baseLocusCubicParam_eq_coefficient_matrix
    (a b c d e s t : K) :
    baseLocusCubicParam a b c d e s t = fun i =>
      ∑ j, baseLocusCubicCoefficientMatrix a b c d e i j *
        ![s ^ 3, s ^ 2 * t, s * t ^ 2, t ^ 3] j := by
  funext i
  fin_cases i <;>
    simp [baseLocusCubicParam, baseLocusCubicCoefficientMatrix,
      Fin.sum_univ_four] <;> ring

/-- The determinant calculation which makes the exceptional parameterization
into a projectively normal twisted cubic. -/
theorem baseLocusCubicCoefficientMatrix_det (a b c d e : K) :
    Matrix.det (baseLocusCubicCoefficientMatrix a b c d e) =
      -a ^ 2 * b ^ 2 * c ^ 2 * d ^ 2 * e ^ 2 * (b * e - c * d) := by
  rw [Matrix.det_succ_row_zero]
  simp [baseLocusCubicCoefficientMatrix, Matrix.det_fin_three, Fin.sum_univ_four]
  ring

/-- Under the six-entry nondegeneracy assumptions, the exceptional cubic
parameterization has invertible coefficient matrix. -/
theorem baseLocusCubicCoefficientMatrix_det_ne_zero
    (a b c d e : K) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hd : d ≠ 0) (he : e ≠ 0) (hbe : b * e - c * d ≠ 0) :
    Matrix.det (baseLocusCubicCoefficientMatrix a b c d e) ≠ 0 := by
  rw [baseLocusCubicCoefficientMatrix_det]
  exact mul_ne_zero
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr (pow_ne_zero 2 ha))
      (pow_ne_zero 2 hb)) (pow_ne_zero 2 hc)) (pow_ne_zero 2 hd))
      (pow_ne_zero 2 he)) hbe

/-- The four parameterizing cubics are linearly independent in the standard
basis of binary cubics under the exceptional-branch nondegeneracy condition. -/
theorem baseLocusCubicCoefficientRows_linearIndependent
    (a b c d e : K) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hd : d ≠ 0) (he : e ≠ 0) (hbe : b * e - c * d ≠ 0) :
    LinearIndependent K (fun i => baseLocusCubicCoefficientMatrix a b c d e i) :=
  Matrix.linearIndependent_rows_of_det_ne_zero
    (baseLocusCubicCoefficientMatrix_det_ne_zero a b c d e ha hb hc hd he hbe)

/-- The scalar whose vanishing is the exceptional twisted-cubic case. -/
def baseLocusDelta (a b c d e f : K) : K :=
  a * b * e * f - a * c * d * f + b * c * d * e

/-- In the exceptional `Δ = 0` case, the denominator condition used in the
twisted-cubic parametrization follows from nonvanishing of the six matrix
entries. -/
theorem baseLocus_be_sub_cd_ne_zero_of_delta_zero
    (a b c d e f : K) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0)
    (hdelta : baseLocusDelta a b c d e f = 0) : b * e - c * d ≠ 0 := by
  intro hbe
  have hrewrite : baseLocusDelta a b c d e f = b * c * d * e := by
    dsimp [baseLocusDelta]
    linear_combination a * f * hbe
  have hzero : b * c * d * e = 0 := hrewrite.symm.trans hdelta
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero hb hc) hd) he) hzero

/-- Under the nondegeneracy condition `be - cd ≠ 0`, the four cubic forms in
the exceptional base-locus parametrization never vanish simultaneously on a
nonzero parameter pair. -/
theorem baseLocusCubicParam_ne_zero
    (a b c d e : K) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hd : d ≠ 0) (he : e ≠ 0) (hbe : b * e - c * d ≠ 0)
    (s t : K) (hst : (s, t) ≠ 0) : baseLocusCubicParam a b c d e s t ≠ 0 := by
  intro hzero
  by_cases hs0 : s = 0
  · have ht : t ≠ 0 := by
      intro ht
      apply hst
      simp [hs0, ht]
    have h1 := congrFun hzero 1
    change a * t * (d * s - b * t) * (e * s - c * t) = 0 at h1
    have h1' : a * t * (-(b * t)) * (-(c * t)) = 0 := by
      simpa only [hs0, mul_zero, zero_mul, zero_sub] using h1
    exact (mul_ne_zero
      (mul_ne_zero (mul_ne_zero ha ht) (neg_ne_zero.mpr (mul_ne_zero hb ht)))
      (neg_ne_zero.mpr (mul_ne_zero hc ht))) h1'
  · have hs : s ≠ 0 := hs0
    by_cases ht0 : t = 0
    · have h0 := congrFun hzero 0
      change a * s * (d * s - b * t) * (e * s - c * t) = 0 at h0
      have h0' : a * s * (d * s) * (e * s) = 0 := by
        simpa only [ht0, mul_zero, sub_zero] using h0
      exact (mul_ne_zero
        (mul_ne_zero (mul_ne_zero ha hs) (mul_ne_zero hd hs))
        (mul_ne_zero he hs)) h0'
    · have ht : t ≠ 0 := ht0
      by_cases hD : d * s - b * t = 0
      · by_cases hE : e * s - c * t = 0
        · apply hbe
          have hprod : (b * e - c * d) * s = 0 := by
            linear_combination b * hE - c * hD
          exact (mul_eq_zero.mp hprod).resolve_right hs
        · have h2 := congrFun hzero 2
          change b * d * s * t * (e * s - c * t) = 0 at h2
          exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hb hd) hs) ht) hE) h2
      · by_cases hE : e * s - c * t = 0
        · have h3 := congrFun hzero 3
          change c * e * s * t * (d * s - b * t) = 0 at h3
          exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hc he) hs) ht) hD) h3
        · have h0 := congrFun hzero 0
          change a * s * (d * s - b * t) * (e * s - c * t) = 0 at h0
          exact (mul_ne_zero (mul_ne_zero (mul_ne_zero ha hs) hD) hE) h0

theorem baseLocusQuadric1_param_eval
    (a b c d e f s t : K) (hb : b ≠ 0) :
    offDiagonalQuadricEval (baseLocusQuadric1 a b c d e f)
      (baseLocusCubicParam a b c d e s t) = 0 := by
  dsimp [offDiagonalQuadricEval, baseLocusQuadric1, baseLocusCubicParam]
  field_simp [hb]
  ring

theorem baseLocusQuadric2_param_eval
    (a b c d e f s t : K) (hc : c ≠ 0) :
    offDiagonalQuadricEval (baseLocusQuadric2 a b c d e f)
      (baseLocusCubicParam a b c d e s t) = 0 := by
  dsimp [offDiagonalQuadricEval, baseLocusQuadric2, baseLocusCubicParam]
  field_simp [hc]
  ring

/-- The third quadric evaluates to the displayed residual factor. -/
theorem baseLocusQuadric3_param_eval
    (a b c d e f s t : K) (hb : b ≠ 0) (hc : c ≠ 0) :
    offDiagonalQuadricEval (baseLocusQuadric3 a b c d e f)
      (baseLocusCubicParam a b c d e s t) =
      s^2 * t^2 * (d * s - b * t) * (e * s - c * t) * baseLocusDelta a b c d e f := by
  dsimp [offDiagonalQuadricEval, baseLocusQuadric3, baseLocusCubicParam,
    baseLocusDelta]
  field_simp [hb, hc]
  ring

/-- When `Δ = 0`, the displayed cubic parametrization lies in the common
zero locus of all three base-locus quadrics. -/
theorem baseLocusQuadrics_param_eval_of_delta_zero
    (a b c d e f s t : K) (hb : b ≠ 0) (hc : c ≠ 0)
    (hdelta : baseLocusDelta a b c d e f = 0) :
    offDiagonalQuadricEval (baseLocusQuadric1 a b c d e f)
        (baseLocusCubicParam a b c d e s t) = 0 ∧
      offDiagonalQuadricEval (baseLocusQuadric2 a b c d e f)
        (baseLocusCubicParam a b c d e s t) = 0 ∧
      offDiagonalQuadricEval (baseLocusQuadric3 a b c d e f)
        (baseLocusCubicParam a b c d e s t) = 0 := by
  refine ⟨baseLocusQuadric1_param_eval a b c d e f s t hb,
    baseLocusQuadric2_param_eval a b c d e f s t hc, ?_⟩
  rw [baseLocusQuadric3_param_eval a b c d e f s t hb hc, hdelta, mul_zero]

/-- The explicit exceptional-branch parameterization gives nonzero common
zeros of all three quadrics for every nonzero binary parameter pair. -/
theorem baseLocusExceptionalParametrization
    (a b c d e f : K) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hd : d ≠ 0) (he : e ≠ 0)
    (hdelta : baseLocusDelta a b c d e f = 0)
    (s t : K) (hst : (s, t) ≠ 0) :
    baseLocusCubicParam a b c d e s t ≠ 0 ∧
      offDiagonalQuadricEval (baseLocusQuadric1 a b c d e f)
        (baseLocusCubicParam a b c d e s t) = 0 ∧
      offDiagonalQuadricEval (baseLocusQuadric2 a b c d e f)
        (baseLocusCubicParam a b c d e s t) = 0 ∧
      offDiagonalQuadricEval (baseLocusQuadric3 a b c d e f)
        (baseLocusCubicParam a b c d e s t) = 0 := by
  have hbe : b * e - c * d ≠ 0 :=
    baseLocus_be_sub_cd_ne_zero_of_delta_zero a b c d e f hb hc hd he hdelta
  refine ⟨baseLocusCubicParam_ne_zero a b c d e ha hb hc hd he hbe s t hst, ?_⟩
  exact baseLocusQuadrics_param_eval_of_delta_zero a b c d e f s t hb hc hdelta

/-- Outside the exceptional `Δ = 0` case, the three displayed quadrics have
no projective common zero away from the four coordinate vertices.  This is
the finite-base-locus branch of Lemma 5.4. -/
theorem baseLocus_common_zero_is_coordinate_axis_of_delta_ne_zero
    (a b c d e f : K) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hd : d ≠ 0) (he : e ≠ 0)
    (hdelta : baseLocusDelta a b c d e f ≠ 0)
    (x : Fin 4 → K)
    (h1 : offDiagonalQuadricEval (baseLocusQuadric1 a b c d e f) x = 0)
    (h2 : offDiagonalQuadricEval (baseLocusQuadric2 a b c d e f) x = 0)
    (h3 : offDiagonalQuadricEval (baseLocusQuadric3 a b c d e f) x = 0) :
    ∃ i : Fin 4, ∀ j, j ≠ i → x j = 0 := by
  by_cases hx0 : x 0 = 0
  · have h12 : x 1 * x 2 = 0 := by
      simpa [offDiagonalQuadricEval, baseLocusQuadric1, hx0] using h1
    have h13 : x 1 * x 3 = 0 := by
      simpa [offDiagonalQuadricEval, baseLocusQuadric2, hx0] using h2
    have h23 : x 2 * x 3 = 0 := by
      simpa [offDiagonalQuadricEval, baseLocusQuadric3, hx0] using h3
    rcases mul_eq_zero.mp h12 with hx1 | hx2
    · rcases mul_eq_zero.mp h23 with hx2 | hx3
      · refine ⟨3, ?_⟩
        intro j hj
        fin_cases j <;> simp_all
      · refine ⟨2, ?_⟩
        intro j hj
        fin_cases j <;> simp_all
    · rcases mul_eq_zero.mp h13 with hx1 | hx3
      · refine ⟨3, ?_⟩
        intro j hj
        fin_cases j <;> simp_all
      · refine ⟨1, ?_⟩
        intro j hj
        fin_cases j <;> simp_all
  · have hD : d * x 0 - b * x 1 ≠ 0 := by
      intro hD
      have hbd : b * d * x 0 * x 1 = 0 := by
        calc
          b * d * x 0 * x 1 =
              (a * b) * offDiagonalQuadricEval
                (baseLocusQuadric1 a b c d e f) x +
                (a * x 2) * (d * x 0 - b * x 1) := by
            dsimp [offDiagonalQuadricEval, baseLocusQuadric1]
            field_simp [ha, hb]
            ring
          _ = 0 := by rw [h1, hD]; ring
      have hdd : d * d * x 0 * x 0 = 0 := by
        calc
          d * d * x 0 * x 0 =
              d * x 0 * (d * x 0 - b * x 1) + b * d * x 0 * x 1 := by ring
          _ = 0 := by rw [hD, hbd]; ring
      exact (mul_ne_zero (mul_ne_zero (mul_ne_zero hd hd) hx0) hx0) hdd
    have hE : e * x 0 - c * x 1 ≠ 0 := by
      intro hE
      have hce : c * e * x 0 * x 1 = 0 := by
        calc
          c * e * x 0 * x 1 =
              (a * c) * offDiagonalQuadricEval
                (baseLocusQuadric2 a b c d e f) x +
                (a * x 3) * (e * x 0 - c * x 1) := by
            dsimp [offDiagonalQuadricEval, baseLocusQuadric2]
            field_simp [ha, hc]
            ring
          _ = 0 := by rw [h2, hE]; ring
      have hee : e * e * x 0 * x 0 = 0 := by
        calc
          e * e * x 0 * x 0 =
              e * x 0 * (e * x 0 - c * x 1) + c * e * x 0 * x 1 := by ring
          _ = 0 := by rw [hE, hce]; ring
      exact (mul_ne_zero (mul_ne_zero (mul_ne_zero he he) hx0) hx0) hee
    have hx2 : x 2 = b * d * x 0 * x 1 / (a * (d * x 0 - b * x 1)) := by
      apply (eq_div_iff (mul_ne_zero ha hD)).mpr
      calc
        x 2 * (a * (d * x 0 - b * x 1)) =
            -(a * b) * offDiagonalQuadricEval
              (baseLocusQuadric1 a b c d e f) x + b * d * x 0 * x 1 := by
          dsimp [offDiagonalQuadricEval, baseLocusQuadric1]
          field_simp [ha, hb]
          ring
        _ = b * d * x 0 * x 1 := by rw [h1]; ring
    have hx3 : x 3 = c * e * x 0 * x 1 / (a * (e * x 0 - c * x 1)) := by
      apply (eq_div_iff (mul_ne_zero ha hE)).mpr
      calc
        x 3 * (a * (e * x 0 - c * x 1)) =
            -(a * c) * offDiagonalQuadricEval
              (baseLocusQuadric2 a b c d e f) x + c * e * x 0 * x 1 := by
          dsimp [offDiagonalQuadricEval, baseLocusQuadric2]
          field_simp [ha, hc]
          ring
        _ = c * e * x 0 * x 1 := by rw [h2]; ring
    have hD' : x 0 * d - x 1 * b ≠ 0 := by
      simpa [mul_comm] using hD
    have hE' : x 0 * e - x 1 * c ≠ 0 := by
      simpa [mul_comm] using hE
    have hdelta' : baseLocusDelta a b c d e f * x 0 ^ 2 * x 1 ^ 2 = 0 := by
      dsimp [offDiagonalQuadricEval, baseLocusQuadric3] at h3
      rw [hx2, hx3] at h3
      field_simp [ha, hD', hE'] at h3
      dsimp [baseLocusDelta]
      linear_combination h3
    have hx1 : x 1 = 0 := by
      by_contra hx1
      have hprod : baseLocusDelta a b c d e f * x 0 ^ 2 * x 1 ^ 2 ≠ 0 :=
        mul_ne_zero (mul_ne_zero hdelta (pow_ne_zero 2 hx0)) (pow_ne_zero 2 hx1)
      exact hprod hdelta'
    have hx2zero : x 2 = 0 := by
      have h := h1
      simp [offDiagonalQuadricEval, baseLocusQuadric1, hx1] at h
      rcases h with ((hd0 | hb0) | hx0') | hx2zero
      · exact (hd hd0).elim
      · exact (hb hb0).elim
      · exact (hx0 hx0').elim
      · exact hx2zero
    have hx3zero : x 3 = 0 := by
      have h := h2
      simp [offDiagonalQuadricEval, baseLocusQuadric2, hx1] at h
      rcases h with ((he0 | hc0) | hx0') | hx3zero
      · exact (he he0).elim
      · exact (hc hc0).elim
      · exact (hx0 hx0').elim
      · exact hx3zero
    refine ⟨0, ?_⟩
    intro j hj
    fin_cases j <;> simp_all

/-- The first explicit quadric vanishes along all four tangent double points. -/
theorem tangentQuadricEvaluation_baseLocusQuadric1
    (a b c d e f : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    tangentQuadricEvaluation (skewTangentDirections a b c d e f)
      (baseLocusQuadric1 a b c d e f) = 0 := by
  funext i
  fin_cases i
  · change (d / a) * a + (-d / b) * b + 0 * c = 0
    field_simp [ha, hb]; ring
  · change (d / a) * (-a) + 1 * d + 0 * e = 0
    field_simp [ha]; ring
  · change (-d / b) * (-b) + 1 * (-d) + 0 * f = 0
    field_simp [hb]; ring
  · change 0 * (-c) + 0 * (-e) + 0 * (-f) = 0
    ring

/-- The second explicit quadric vanishes along all four tangent double points. -/
theorem tangentQuadricEvaluation_baseLocusQuadric2
    (a b c d e f : K) (ha : a ≠ 0) (hc : c ≠ 0) :
    tangentQuadricEvaluation (skewTangentDirections a b c d e f)
      (baseLocusQuadric2 a b c d e f) = 0 := by
  funext i
  fin_cases i
  · change (e / a) * a + 0 * b + (-e / c) * c = 0
    field_simp [ha, hc]; ring
  · change (e / a) * (-a) + 0 * d + 1 * e = 0
    field_simp [ha]; ring
  · change 0 * (-b) + 0 * (-d) + 0 * f = 0
    ring
  · change (-e / c) * (-c) + 1 * (-e) + 0 * (-f) = 0
    field_simp [hc]; ring

/-- The third explicit quadric vanishes along all four tangent double points. -/
theorem tangentQuadricEvaluation_baseLocusQuadric3
    (a b c d e f : K) (hb : b ≠ 0) (hc : c ≠ 0) :
    tangentQuadricEvaluation (skewTangentDirections a b c d e f)
      (baseLocusQuadric3 a b c d e f) = 0 := by
  funext i
  fin_cases i
  · change 0 * a + (f / b) * b + (-f / c) * c = 0
    field_simp [hb, hc]; ring
  · change 0 * (-a) + 0 * d + 0 * e = 0
    ring
  · change (f / b) * (-b) + 0 * (-d) + 1 * f = 0
    field_simp [hb]; ring
  · change (-f / c) * (-c) + 0 * (-e) + 1 * (-f) = 0
    field_simp [hc]; ring

/-- The three explicit quadrics are linearly independent; their coefficients of
`x₁x₂`, `x₁x₃`, and `x₂x₃` recover the three scalars. -/
theorem baseLocusQuadrics_linearIndependent
    (a b c d e f : K) (r : Fin 3 → K)
    (h : (fun j => r 0 * baseLocusQuadric1 a b c d e f j +
        r 1 * baseLocusQuadric2 a b c d e f j +
        r 2 * baseLocusQuadric3 a b c d e f j) = 0) : r = 0 := by
  funext i
  fin_cases i
  · have h3 := congrFun h 3
    simpa [baseLocusQuadric1, baseLocusQuadric2, baseLocusQuadric3] using h3
  · have h4 := congrFun h 4
    simpa [baseLocusQuadric1, baseLocusQuadric2, baseLocusQuadric3] using h4
  · have h5 := congrFun h 5
    simpa [baseLocusQuadric1, baseLocusQuadric2, baseLocusQuadric3] using h5

/-- The first quadric used in the valence-two branch of
`prop:zero-off-diagonal`. -/
def zeroOffDiagonalQuadric1 : Fin 6 → K := ![1, 0, 0, 0, 0, 0]

/-- The second quadric used in the valence-two branch of
`prop:zero-off-diagonal`. -/
def zeroOffDiagonalQuadric2 : Fin 6 → K := ![0, 0, 0, 0, 0, 1]

/-- The third quadric used in the valence-two branch of
`prop:zero-off-diagonal`. -/
def zeroOffDiagonalQuadric3 (b c d e : K) : Fin 6 → K :=
  ![0, 1 / b, -1 / c, -1 / d, 1 / e, 0]

/-- In the four-cycle case, the first two quadrics cut out the four coordinate
lines and the third has nonzero restriction to each of them. Algebraically,
their common affine-cone zeros are supported on coordinate axes. -/
theorem zeroOffDiagonal_common_zero_is_coordinate_axis
    (b c d e : K) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0)
    (x : Fin 4 → K)
    (h1 : offDiagonalQuadricEval (zeroOffDiagonalQuadric1 : Fin 6 → K) x = 0)
    (h2 : offDiagonalQuadricEval (zeroOffDiagonalQuadric2 : Fin 6 → K) x = 0)
    (h3 : offDiagonalQuadricEval (zeroOffDiagonalQuadric3 b c d e) x = 0) :
    ∃ i : Fin 4, ∀ j, j ≠ i → x j = 0 := by
  have h01 : x 0 * x 1 = 0 := by
    simpa [offDiagonalQuadricEval, zeroOffDiagonalQuadric1] using h1
  have h23 : x 2 * x 3 = 0 := by
    simpa [offDiagonalQuadricEval, zeroOffDiagonalQuadric2] using h2
  rcases mul_eq_zero.mp h01 with hx0 | hx1 <;>
    rcases mul_eq_zero.mp h23 with hx2 | hx3
  · have h13 : x 1 * x 3 = 0 := by
      have h13' : (1 / e) * (x 1 * x 3) = 0 := by
        simpa [offDiagonalQuadricEval, zeroOffDiagonalQuadric3, hx0, hx2,
          mul_assoc] using h3
      exact (mul_eq_zero.mp h13').resolve_left (one_div_ne_zero he)
    rcases mul_eq_zero.mp h13 with hx1 | hx3
    · refine ⟨3, ?_⟩
      intro j hj
      fin_cases j <;> simp_all
    · refine ⟨1, ?_⟩
      intro j hj
      fin_cases j <;> simp_all
  · have h12 : x 1 * x 2 = 0 := by
      have h12' : (-1 / d) * (x 1 * x 2) = 0 := by
        simpa [offDiagonalQuadricEval, zeroOffDiagonalQuadric3, hx0, hx3,
          mul_assoc] using h3
      exact (mul_eq_zero.mp h12').resolve_left (div_ne_zero (neg_ne_zero.mpr one_ne_zero) hd)
    rcases mul_eq_zero.mp h12 with hx1 | hx2
    · refine ⟨2, ?_⟩
      intro j hj
      fin_cases j <;> simp_all
    · refine ⟨1, ?_⟩
      intro j hj
      fin_cases j <;> simp_all
  · have h03 : x 0 * x 3 = 0 := by
      have h03' : (-1 / c) * (x 0 * x 3) = 0 := by
        simpa [offDiagonalQuadricEval, zeroOffDiagonalQuadric3, hx1, hx2,
          mul_assoc] using h3
      exact (mul_eq_zero.mp h03').resolve_left (div_ne_zero (neg_ne_zero.mpr one_ne_zero) hc)
    rcases mul_eq_zero.mp h03 with hx0 | hx3
    · refine ⟨3, ?_⟩
      intro j hj
      fin_cases j <;> simp_all
    · refine ⟨0, ?_⟩
      intro j hj
      fin_cases j <;> simp_all
  · have h02 : x 0 * x 2 = 0 := by
      have h02' : (1 / b) * (x 0 * x 2) = 0 := by
        simpa [offDiagonalQuadricEval, zeroOffDiagonalQuadric3, hx1, hx3,
          mul_assoc] using h3
      exact (mul_eq_zero.mp h02').resolve_left (one_div_ne_zero hb)
    rcases mul_eq_zero.mp h02 with hx0 | hx2
    · refine ⟨2, ?_⟩
      intro j hj
      fin_cases j <;> simp_all
    · refine ⟨0, ?_⟩
      intro j hj
      fin_cases j <;> simp_all

/-- The three quadrics in the valence-two branch vanish along the four
specified tangent double-point conditions. -/
theorem tangentQuadricEvaluation_zeroOffDiagonalQuadrics
    (b c d e : K) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0) :
    tangentQuadricEvaluation (skewTangentDirections 0 b c d e 0)
        (zeroOffDiagonalQuadric1 : Fin 6 → K) = 0 ∧
      tangentQuadricEvaluation (skewTangentDirections 0 b c d e 0)
        (zeroOffDiagonalQuadric2 : Fin 6 → K) = 0 ∧
      tangentQuadricEvaluation (skewTangentDirections 0 b c d e 0)
        (zeroOffDiagonalQuadric3 b c d e) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · funext i
    fin_cases i <;> simp [tangentQuadricEvaluation, skewTangentDirections,
      zeroOffDiagonalQuadric1]
  · funext i
    fin_cases i <;> simp [tangentQuadricEvaluation, skewTangentDirections,
      zeroOffDiagonalQuadric2]
  · funext i
    fin_cases i
    · simp [tangentQuadricEvaluation, skewTangentDirections, zeroOffDiagonalQuadric3]
      field_simp [hb, hc]
      ring
    · simp [tangentQuadricEvaluation, skewTangentDirections, zeroOffDiagonalQuadric3]
      field_simp [hd, he]
      ring
    · simp [tangentQuadricEvaluation, skewTangentDirections, zeroOffDiagonalQuadric3]
      field_simp [hb, hd]
      ring
    · simp [tangentQuadricEvaluation, skewTangentDirections, zeroOffDiagonalQuadric3]
      field_simp [hc, he]
      ring

end
end QuarticNet
end PfaffianDescent
