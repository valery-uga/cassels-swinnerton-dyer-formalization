import AllCharacteristics.TangentPlaneLineFactor
import AllCharacteristics.CommonTangentLineNoncubicPoint
import AllCharacteristics.TangentHyperplaneCoordinateSurjectivity
import AllCharacteristics.TangentHyperplaneDirection
import Mathlib.Tactic.FieldSimp

/-! Noncontainment of the common line of two tangent
planes. A tangent-plane cubic is singular at its center. A line of that
plane avoiding the center would force a contained line through the center
if the whole line lay on the cubic. -/

noncomputable section
namespace AllCharacteristics

open PfaffianDescent MvPolynomial Polynomial AlgebraicGeometry HomogeneousProjective
open scoped BigOperators
universe u

/-- Equality of actual cubic evaluations along a linear embedding transports
the mixed coefficient. The proof compares binary cubic coefficients and
uses no differentiation or characteristic restriction. -/
theorem cubic_mixed_of_matrix_evaluation_eq
    {K : Type u} [Field K] [Infinite K] {m n : ℕ}
    (c : Cubic K m) (d : Cubic K n) (M : Matrix (Fin m) (Fin n) K)
    (heval : ∀ x, d.eval x = c.eval (M.mulVec x))
    (p q : Fin n → K) : d.mixed p q = c.mixed (M.mulVec p) (M.mulVec q) := by
  have hpoly : cubicLinePolynomial d p q = cubicLinePolynomial c (M.mulVec p) (M.mulVec q) := by
    apply Polynomial.funext
    intro t
    have hd := cubicLinePolynomial_eval₂ (RingHom.id K) d p q t
    have hc := cubicLinePolynomial_eval₂ (RingHom.id K) c (M.mulVec p) (M.mulVec q) t
    have hdm : d.map (RingHom.id K) = d := by funext i; rfl
    have hcm : c.map (RingHom.id K) = c := by funext i; rfl
    have hd' : (cubicLinePolynomial d p q).eval t = d.eval (t • p + q) := by
      simpa only [Polynomial.eval₂_id, hdm, RingHom.id_apply] using hd
    have hc' : (cubicLinePolynomial c (M.mulVec p) (M.mulVec q)).eval t =
        c.eval (t • M.mulVec p + M.mulVec q) := by
      simpa only [Polynomial.eval₂_id, hcm, RingHom.id_apply] using hc
    have hlin : M.mulVec (t • p + q) = t • M.mulVec p + M.mulVec q := by
      change M.mulVecLin (t • p + q) = _
      rw [map_add, map_smul]
      rfl
    rw [hd', hc', heval, hlin]
  simpa [cubicLinePolynomial, Polynomial.coeff_C_mul] using
    congrArg (fun f : K[X] => f.coeff 2) hpoly

/-- A split embedding of a tangent plane carries the original no-line
condition to its actual ternary cubic restriction. -/
theorem tangentPlaneRestriction_no_contained_line_through
    {K : Type u} [Field K]
    (c : Cubic K 4) (M : Matrix (Fin 4) (Fin 3) K)
    (N : Matrix (Fin 3) (Fin 4) K) (hNM : N * M = 1)
    (z : Fin 3 → K) (p : Fin 4 → K) (hMz : M.mulVec z = p)
    (hno : ∀ d : Fin 4 → K, LinearIndependent K ![p, d] →
      ∃ s t : K, c.eval (s • p + t • d) ≠ 0) :
    ∀ d : Fin 3 → K, LinearIndependent K ![z, d] →
      ∃ s t : K, MvPolynomial.eval (s • z + t • d) (rectangularSubstitution M c.toMvPolynomial) ≠ 0 := by
  have hinj : Function.Injective M.mulVec := by
    intro x y hxy
    have h := congrArg N.mulVec hxy
    simpa only [Matrix.mulVec_mulVec, hNM, Matrix.one_mulVec] using h
  intro d hind
  have hind' : LinearIndependent K ![p, M.mulVec d] := by
    convert hind.map' M.mulVecLin (LinearMap.ker_eq_bot.mpr hinj) using 1
    funext i
    fin_cases i <;> simp [hMz]
    all_goals rfl
  obtain ⟨s, t, hst⟩ := hno (M.mulVec d) hind'
  refine ⟨s, t, ?_⟩
  rw [← cubic_eval_matrix_mulVec]
  have hlin : M.mulVec (s • z + t • d) = s • p + t • M.mulVec d := by
    change M.mulVecLin (s • z + t • d) = _
    rw [map_add, map_smul, map_smul]
    change s • M.mulVec z + t • M.mulVec d = _
    rw [hMz]
  rw [hlin]
  exact hst

/-- The actual restricted cubic is singular at the tangent center, proved
from its original mixed tangent equation and the linear evaluation diagram. -/
theorem tangentPlaneRestriction_singular_at_center
    {K : Type u} [Field K] [Infinite K]
    (c : Cubic K 4) (hF : c.toMvPolynomial.IsHomogeneous 3)
    (M : Matrix (Fin 4) (Fin 3) K)
    (z : Fin 3 → K) (p : Fin 4 → K) (hMz : M.mulVec z = p)
    (hp : c.eval p = 0) (htan : ∀ u : Fin 3 → K, c.mixed p (M.mulVec u) = 0) :
    MvPolynomial.eval z (rectangularSubstitution M c.toMvPolynomial) = 0 ∧
      ∀ i : Fin 3, MvPolynomial.eval z
        (MvPolynomial.pderiv i (rectangularSubstitution M c.toMvPolynomial)) = 0 := by
  let G := rectangularSubstitution M c.toMvPolynomial
  have hG : G.IsHomogeneous 3 := rectangularSubstitution_homogeneous M hF
  obtain ⟨d, hd⟩ := homogeneous_cubic_has_tensor_any_characteristic G hG
  have heval : ∀ x : Fin 3 → K, d.eval x = c.eval (M.mulVec x) := by
    intro x
    have hdm : d.map (RingHom.id K) = d := by funext i; rfl
    have hdeval := Cubic.eval_toMvPolynomial (RingHom.id K) d x
    rw [MvPolynomial.eval₂_id, hdm, hd] at hdeval
    exact hdeval.symm.trans (cubic_eval_matrix_mulVec c M x).symm
  constructor
  · rw [← cubic_eval_matrix_mulVec, hMz, hp]
  intro i
  have hm : d.mixed z (Pi.single i 1) = 0 := by
    rw [cubic_mixed_of_matrix_evaluation_eq c d M heval, hMz]
    exact htan _
  rw [AllCharacteristics.Cubic.mixed_eq_sum_pderiv_eval, hd] at hm
  simpa [Pi.single_apply] using hm

/-- Every line of the actual tangent plane that avoids the center has
nonzero cubic restriction. This is the geometric input to the common-line
secant avoidance construction. -/
theorem tangentPlane_line_restriction_ne_zero_of_no_contained_line
    {K : Type u} [Field K] [IsAlgClosed K]
    (c : Cubic K 4) (hF : c.toMvPolynomial.IsHomogeneous 3)
    (M : Matrix (Fin 4) (Fin 3) K) (N : Matrix (Fin 3) (Fin 4) K)
    (hNM : N * M = 1)
    (z : Fin 3 → K) (p : Fin 4 → K) (hMz : M.mulVec z = p)
    (hp : c.eval p = 0) (htan : ∀ u : Fin 3 → K, c.mixed p (M.mulVec u) = 0)
    (hG0 : rectangularSubstitution M c.toMvPolynomial ≠ 0)
    (hno : ∀ d : Fin 4 → K, LinearIndependent K ![p, d] →
      ∃ s t : K, c.eval (s • p + t • d) ≠ 0)
    (a : Fin 3 → K) (k : Fin 3) (hk : a k ≠ 0)
    (hap : MvPolynomial.eval z (homogeneousLinearForm a) ≠ 0) :
    rectangularSubstitution (M * hyperplaneInclusion a k) c.toMvPolynomial ≠ 0 := by
  have hsing := tangentPlaneRestriction_singular_at_center c hF M z p hMz hp htan
  have hnoG := tangentPlaneRestriction_no_contained_line_through c M N hNM z p hMz hno
  have hrest := plane_cubic_line_restriction_ne_zero_of_no_contained_line_through
    (rectangularSubstitution M c.toMvPolynomial)
    (rectangularSubstitution_homogeneous M hF) hG0 z hsing.1 hsing.2 hnoG a k hk hap
  intro hzero
  apply hrest
  change ((rectangularSubstitution (hyperplaneInclusion a k)).comp
    (rectangularSubstitution M)) c.toMvPolynomial = 0
  rw [rectangularSubstitution_comp, hzero]

theorem eval_homogeneousLinearForm_vecMul
    {K : Type u} [Field K]
    (g : Fin 4 → K) (M : Matrix (Fin 4) (Fin 3) K) (z : Fin 3 → K) :
    MvPolynomial.eval z (homogeneousLinearForm (Matrix.vecMul g M)) = ∑ i, g i * M.mulVec z i := by
  simp only [homogeneousLinearForm, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
  exact (Matrix.dotProduct_mulVec g M z).symm

theorem hyperplaneInclusion_dot_mulVec_zero_any_dimension
    {K : Type u} [Field K] {n : ℕ}
    (g : Fin (n + 1) → K) (k : Fin (n + 1)) (hk : g k ≠ 0) (x : Fin n → K) :
    ∑ i, g i * (hyperplaneInclusion g k).mulVec x i = 0 := by
  classical
  have hpivot : (hyperplaneInclusion g k).mulVec x k =
      -(g k)⁻¹ * ∑ j, g (k.succAbove j) * x j := by
    simp only [Matrix.mulVec, dotProduct, hyperplaneInclusion, ↓reduceIte]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hother (j : Fin n) : (hyperplaneInclusion g k).mulVec x (k.succAbove j) = x j := by
    simp [Matrix.mulVec, dotProduct, hyperplaneInclusion, Fin.succAbove_ne]
  rw [Fin.sum_univ_succAbove _ k, hpivot]
  simp_rw [hother]
  field_simp [hk]
  ring

theorem coordinatePairMatrix_common_hyperplane_kernel
    {K : Type u} [Field K]
    (g h : Fin 4 → K) (k : Fin 4) (hk : g k ≠ 0)
    (a : Fin 3 → K) (ha : a = Matrix.vecMul h (hyperplaneInclusion g k))
    (l : Fin 3) (hl : a l ≠ 0) :
    coordinatePairMatrix g h * (hyperplaneInclusion g k * hyperplaneInclusion a l) = 0 := by
  let C := hyperplaneInclusion g k * hyperplaneInclusion a l
  have hz (v : Fin 2 → K) : (coordinatePairMatrix g h).mulVec (C.mulVec v) = 0 := by
    rw [coordinatePairMatrix_mulVec]
    funext i
    fin_cases i
    · change (∑ i, g i * C.mulVec v i) = 0
      change (∑ i, g i * (hyperplaneInclusion g k * hyperplaneInclusion a l).mulVec v i) = 0
      rw [← Matrix.mulVec_mulVec]
      exact hyperplaneInclusion_dot_mulVec_zero_any_dimension g k hk _
    · change dotProduct h ((hyperplaneInclusion g k * hyperplaneInclusion a l).mulVec v) = 0
      rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← ha]
      exact hyperplaneInclusion_dot_mulVec_zero_any_dimension a l hl v
  ext i j
  have hprod := hz (Pi.single j (1 : K))
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_single_one] at hprod
  have hij := congrFun hprod i
  change (coordinatePairMatrix g h * C) i j = 0 at hij
  exact hij

/-- If one common-kernel parametrization has nonzero restriction, then so
does every actual split basis of that kernel. This avoids choosing the
special line parametrization in the final secant argument. -/
theorem split_kernel_frame_restriction_ne_zero_of_kernel_parametrization
    {K : Type u} [Field K] [Infinite K]
    (R : Matrix (Fin 2) (Fin 4) K)
    (A : Matrix (Fin 4) (Fin 2) K) (B : Matrix (Fin 2) (Fin 4) K)
    (S C : Matrix (Fin 4) (Fin 2) K)
    (hBA : B * A = 1) (hRA : R * A = 0) (hRS : R * S = 1)
    (hRC : R * C = 0) (F : MvPolynomial (Fin 4) K)
    (hCF : rectangularSubstitution C F ≠ 0) : rectangularSubstitution A F ≠ 0 := by
  intro hzero
  apply hCF
  apply MvPolynomial.funext
  intro v
  rw [map_zero, rectangularSubstitution_eval_any_dimensions]
  have hRv : R.mulVec (C.mulVec v) = 0 := by
    rw [Matrix.mulVec_mulVec, hRC, Matrix.zero_mulVec]
  obtain ⟨s, t, hst⟩ := mapped_kernel_frame_spans (RingHom.id K) R A B S hBA hRA hRS
    (C.mulVec v) (by simpa using hRv)
  have hvec : C.mulVec v = A.mulVec (![s, t] : Fin 2 → K) := by
    calc
      C.mulVec v = s • (fun i => A i 0) + t • (fun i => A i 1) := by
        simpa only [RingHom.id_apply] using hst
      _ = A.mulVec (![s, t] : Fin 2 → K) := by
        funext i
        simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.add_apply,
          Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one]
        ring
  rw [hvec]
  have heval : MvPolynomial.eval (![s, t] : Fin 2 → K) (rectangularSubstitution A F) = 0 := by
    rw [hzero, map_zero]
  rwa [rectangularSubstitution_eval_any_dimensions] at heval

/-- For the actual gradient tangent plane at `p`, mutual tangent separation
constructs a noncontained line cut by the tangent equation at `q`. The
tangent-plane frame, its center, its nonzero equation and the second linear
equation are all derived internally from the original smooth cubic. -/
theorem exists_common_tangent_line_restriction_ne_zero
    {K : Type u} [Field K] [IsAlgClosed K]
    (c : Cubic K 4) (hF : c.toMvPolynomial.IsHomogeneous 3)
    [Smooth (hypersurfaceToBase c.toMvPolynomial hF)]
    (p q : Fin 4 → K) (hp : c.eval p = 0)
    (k : Fin 4) (hk : (MvPolynomial.pderiv k c.toMvPolynomial).eval p ≠ 0)
    (hqp : c.mixed q p ≠ 0)
    (hno : ∀ d : Fin 4 → K, LinearIndependent K ![p, d] →
      ∃ s t : K, c.eval (s • p + t • d) ≠ 0) :
    let g := fun i => (MvPolynomial.pderiv i c.toMvPolynomial).eval p
    let M := hyperplaneInclusion g k
    let z : Fin 3 → K := fun j => p (k.succAbove j)
    ∃ (a : Fin 3 → K) (l : Fin 3), a l ≠ 0 ∧
      MvPolynomial.eval z (homogeneousLinearForm a) ≠ 0 ∧
      a = Matrix.vecMul (fun i => (MvPolynomial.pderiv i c.toMvPolynomial).eval q) M ∧
      rectangularSubstitution (M * hyperplaneInclusion a l) c.toMvPolynomial ≠ 0 := by
  let g := fun i => (MvPolynomial.pderiv i c.toMvPolynomial).eval p
  let M := hyperplaneInclusion g k
  let N := coordinateOmission (K := K) k
  let z : Fin 3 → K := fun j => p (k.succAbove j)
  have hNM : N * M = 1 := hyperplaneInclusion_leftInverse g k
  have hself : c.mixed p p = 0 := by rw [Cubic.mixed_self_eq_three_eval, hp, mul_zero]
  have hMz : M.mulVec z = p := tangentHyperplane_direction_eq_matrix_coordinates c p p k hk hself
  have htan : ∀ u : Fin 3 → K, c.mixed p (M.mulVec u) = 0 := by
    intro u
    have h := mixed_hyperplaneInclusion_zero (RingHom.id K) c p g (fun _ => rfl) k hk u
    have hc : c.map (RingHom.id K) = c := by funext i; rfl
    have hM : M.map (RingHom.id K) = M := by ext i j; rfl
    change (c.map (RingHom.id K)).mixed (fun i => RingHom.id K (p i)) ((M.map (RingHom.id K)).mulVec u) = 0 at h
    rw [hc, hM] at h
    exact h
  have hF0 : c.toMvPolynomial ≠ 0 := by
    intro hzero
    apply hk
    rw [hzero]
    simp
  have hprime := principalIdeal_prime_of_smooth_homogeneous_cubic c.toMvPolynomial hF hF0
  have hG0 : rectangularSubstitution M c.toMvPolynomial ≠ 0 :=
    hyperplane_restriction_ne_zero_of_prime c.toMvPolynomial hF hF0 hprime g k hk
  let a : Fin 3 → K := Matrix.vecMul (fun i => (MvPolynomial.pderiv i c.toMvPolynomial).eval q) M
  have hap : MvPolynomial.eval z (homogeneousLinearForm a) ≠ 0 := by
    have heq : MvPolynomial.eval z (homogeneousLinearForm a) = c.mixed q p := by
      rw [eval_homogeneousLinearForm_vecMul, hMz, Cubic.mixed_eq_sum_pderiv_eval]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [heq]
    exact hqp
  obtain ⟨l, hl⟩ : ∃ l : Fin 3, a l ≠ 0 := by
    by_contra h
    push Not at h
    apply hap
    simp only [homogeneousLinearForm, h, MvPolynomial.C_0, zero_mul,
      Finset.sum_const_zero, map_zero]
  refine ⟨a, l, hl, hap, rfl, ?_⟩
  exact tangentPlane_line_restriction_ne_zero_of_no_contained_line
    c hF M N hNM z p hMz hp htan hG0 hno a l hl hap

/-- The original common-kernel frame used by the secant construction has a
nonzero actual cubic restriction. Every geometry condition is derived from
smoothness, mutual tangent separation, and no contained line through `p`. -/
theorem common_tangent_split_frame_cubic_restriction_ne_zero
    {K : Type u} [Field K] [IsAlgClosed K]
    (c : Cubic K 4) (hF : c.toMvPolynomial.IsHomogeneous 3)
    [Smooth (hypersurfaceToBase c.toMvPolynomial hF)]
    (p q : Fin 4 → K) (hp : c.eval p = 0)
    (k : Fin 4) (hk : (MvPolynomial.pderiv k c.toMvPolynomial).eval p ≠ 0)
    (hqp : c.mixed q p ≠ 0)
    (hno : ∀ d : Fin 4 → K, LinearIndependent K ![p, d] →
      ∃ s t : K, c.eval (s • p + t • d) ≠ 0)
    (A : Matrix (Fin 4) (Fin 2) K) (B : Matrix (Fin 2) (Fin 4) K)
    (S : Matrix (Fin 4) (Fin 2) K)
    (hBA : B * A = 1)
    (hRA : coordinatePairMatrix
      (fun i => (MvPolynomial.pderiv i c.toMvPolynomial).eval p)
      (fun i => (MvPolynomial.pderiv i c.toMvPolynomial).eval q) * A = 0)
    (hRS : coordinatePairMatrix
      (fun i => (MvPolynomial.pderiv i c.toMvPolynomial).eval p)
      (fun i => (MvPolynomial.pderiv i c.toMvPolynomial).eval q) * S = 1) :
    rectangularSubstitution A c.toMvPolynomial ≠ 0 := by
  let g := fun i => (MvPolynomial.pderiv i c.toMvPolynomial).eval p
  let h := fun i => (MvPolynomial.pderiv i c.toMvPolynomial).eval q
  let M := hyperplaneInclusion g k
  obtain ⟨a, l, hl, _, ha, hrest⟩ :=
    exists_common_tangent_line_restriction_ne_zero c hF p q hp k hk hqp hno
  have hRC := coordinatePairMatrix_common_hyperplane_kernel g h k hk a ha l hl
  exact split_kernel_frame_restriction_ne_zero_of_kernel_parametrization
    (coordinatePairMatrix g h) A B S (M * hyperplaneInclusion a l)
    hBA hRA hRS hRC c.toMvPolynomial hrest

end AllCharacteristics
