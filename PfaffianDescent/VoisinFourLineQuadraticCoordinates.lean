import PfaffianDescent.VoisinFourLineAffineChart
import PfaffianDescent.QuarticAffineQuadrics

/-!
# Coordinates of affine quadrics on the four split lines

The ten standard monomials make the remaining four-line kernel computation
an explicit linear calculation.
-/

namespace PfaffianDescent

open MvPolynomial

universe u

theorem affineQuadrics_eval_coordinates
    {L : Type u} [Field L] (c : Fin 10 → L) (v : Fin 3 → L) :
    (QuarticNet.affineQuadrics c).eval v =
      c 0 + c 1 * v 0 + c 2 * v 1 + c 3 * v 2 +
        c 4 * v 0 ^ 2 + c 5 * v 0 * v 1 + c 6 * v 0 * v 2 +
          c 7 * v 1 ^ 2 + c 8 * v 1 * v 2 + c 9 * v 2 ^ 2 := by
  simp [QuarticNet.affineQuadrics, QuarticNet.affineQuadricExponent,
    Fintype.linearCombination_apply, Fin.sum_univ_succ,
    MvPolynomial.eval_monomial, Finsupp.prod_single_index,
    Fin.prod_univ_succ, Finsupp.single_apply]
  ring

theorem affineQuadrics_fourLine_vanishing_coordinates
    {L : Type u} [Field L] [CharZero L] (c : Fin 10 → L)
    (hline : ∀ i j : Fin 2, ∀ s : L,
      (QuarticNet.affineQuadrics c).eval
        (s • affineLineDirection i j) = 0) :
    c 0 = 0 ∧ c 1 = 0 ∧ c 2 = 0 ∧ c 3 = 0 ∧
      c 4 = 0 ∧ c 7 = 0 ∧ c 6 = c 9 ∧ c 8 = c 9 := by
  have h00 := hline 0 0 0
  have h01 := hline 0 0 1
  have h0m := hline 0 0 (-1)
  have h10 := hline 1 0 1
  have h1m := hline 1 0 (-1)
  have h11 := hline 0 1 1
  have h1n := hline 0 1 (-1)
  have h21 := hline 1 1 1
  rw [affineQuadrics_eval_coordinates] at h00
  simp [affineQuadrics_eval_coordinates, affineLineDirection,
    lineDirection] at h00 h01 h0m h10 h1m h11 h1n h21
  have hc0 : c 0 = 0 := h00
  have hc1 : c 1 = 0 := by linear_combination (h10 - h1m) / 2
  have hc2 : c 2 = 0 := by linear_combination (h01 - h0m) / 2
  have hc3 : c 3 = 0 := by
    linear_combination -(h11 - h1n - h01 + h0m) / 2
  have hc4 : c 4 = 0 := by
    linear_combination (h10 + h1m - 2 * hc0) / 2
  have hc7 : c 7 = 0 := by
    linear_combination (h01 + h0m - 2 * hc0) / 2
  have hc6 : c 6 = c 9 := by
    linear_combination -h21 + h10 - hc3
  have hc8 : c 8 = c 9 := by
    linear_combination -h11 + hc0 + hc2 - hc3 + hc7
  exact ⟨hc0, hc1, hc2, hc3, hc4, hc7, hc6, hc8⟩

theorem affineQuadrics_eq_split_pencil_of_fourLine_vanishing
    {L : Type u} [Field L] [CharZero L] (c : Fin 10 → L)
    (hline : ∀ i j : Fin 2, ∀ s : L,
      (QuarticNet.affineQuadrics c).eval
        (s • affineLineDirection i j) = 0) :
    QuarticNet.affineQuadrics c =
      C (c 5) * X 0 * X 1 +
        C (c 9) * X 2 * (X 0 + X 1 + X 2) := by
  obtain ⟨hc0, hc1, hc2, hc3, hc4, hc7, hc6, hc8⟩ :=
    affineQuadrics_fourLine_vanishing_coordinates c hline
  apply MvPolynomial.funext
  intro v
  simp [affineQuadrics_eval_coordinates, hc0, hc1, hc2, hc3,
    hc4, hc7, hc6, hc8]
  ring

theorem affineQuadricExponent_surjective_on_degree_two
    (d : Fin 3 →₀ ℕ) (hd : d.sum (fun _ n => n) ≤ 2) :
    ∃ i : Fin 10, QuarticNet.affineQuadricExponent i = d := by
  have hsum : d 0 + d 1 + d 2 ≤ 2 := by
    simpa [Finsupp.sum_fintype, Fin.sum_univ_succ, add_assoc] using hd
  have h0 : d 0 ≤ 2 := by omega
  have h1 : d 1 ≤ 2 := by omega
  have h2 : d 2 ≤ 2 := by omega
  interval_cases hval0 : d 0 <;>
    interval_cases hval1 : d 1 <;>
    interval_cases hval2 : d 2
  all_goals solve
    | omega
    | (refine ⟨0, ?_⟩; ext k; fin_cases k <;>
        simp [QuarticNet.affineQuadricExponent, *])
    | (refine ⟨1, ?_⟩; ext k; fin_cases k <;>
        simp [QuarticNet.affineQuadricExponent, *])
    | (refine ⟨2, ?_⟩; ext k; fin_cases k <;>
        simp [QuarticNet.affineQuadricExponent, *])
    | (refine ⟨3, ?_⟩; ext k; fin_cases k <;>
        simp [QuarticNet.affineQuadricExponent, *])
    | (refine ⟨4, ?_⟩; ext k; fin_cases k <;>
        simp [QuarticNet.affineQuadricExponent, *])
    | (refine ⟨5, ?_⟩; ext k; fin_cases k <;>
        simp [QuarticNet.affineQuadricExponent, *])
    | (refine ⟨6, ?_⟩; ext k; fin_cases k <;>
        simp [QuarticNet.affineQuadricExponent, *])
    | (refine ⟨7, ?_⟩; ext k; fin_cases k <;>
        simp [QuarticNet.affineQuadricExponent, *])
    | (refine ⟨8, ?_⟩; ext k; fin_cases k <;>
        simp [QuarticNet.affineQuadricExponent, *])
    | (refine ⟨9, ?_⟩; ext k; fin_cases k <;>
        simp [QuarticNet.affineQuadricExponent, *])

theorem exists_affineQuadrics_of_totalDegree_le_two
    {L : Type u} [Field L]
    (Q : MvPolynomial (Fin 3) L) (hQ : Q.totalDegree ≤ 2) :
    ∃ c : Fin 10 → L, QuarticNet.affineQuadrics c = Q := by
  classical
  have hmon : ∀ d ∈ Q.support,
      monomial d (coeff d Q) ∈
        LinearMap.range (QuarticNet.affineQuadrics (k := L)) := by
    intro d hd
    obtain ⟨i, hi⟩ := affineQuadricExponent_surjective_on_degree_two d
      ((le_totalDegree hd).trans hQ)
    refine ⟨Pi.single i (coeff d Q), ?_⟩
    rw [← hi]
    simp [QuarticNet.affineQuadrics, Fintype.linearCombination_apply,
      Pi.single_apply, MvPolynomial.smul_monomial]
  have hsum : Q ∈ LinearMap.range (QuarticNet.affineQuadrics (k := L)) := by
    rw [← support_sum_monomial_coeff Q]
    exact Submodule.sum_mem _ (fun d hd => hmon d hd)
  exact hsum

/-- The full quadratic kernel of the four affine line restrictions is
the pencil generated by their two split equations. -/
theorem affine_quadric_eq_split_pencil_of_fourLine_vanishing
    {L : Type u} [Field L] [CharZero L]
    (Q : MvPolynomial (Fin 3) L) (hQ : Q.totalDegree ≤ 2)
    (hline : ∀ i j : Fin 2, ∀ s : L,
      Q.eval (s • affineLineDirection i j) = 0) :
    ∃ a b : L, Q =
      C a * X 0 * X 1 + C b * X 2 * (X 0 + X 1 + X 2) := by
  obtain ⟨c, hc⟩ := exists_affineQuadrics_of_totalDegree_le_two Q hQ
  refine ⟨c 5, c 9, ?_⟩
  rw [← hc]
  exact affineQuadrics_eq_split_pencil_of_fourLine_vanishing c
    (by simpa only [hc] using hline)

/-- A homogeneous quadric whose affine dehomogenization vanishes on the
four split lines belongs to the homogeneous split pencil. -/
theorem homogeneous_quadric_eq_split_pencil_of_fourLine_vanishing
    {L : Type u} [Field L] [CharZero L]
    (Q : MvPolynomial (Fin 4) L) (hQ : Q.IsHomogeneous 2)
    (hline : ∀ i j : Fin 2, ∀ s : L,
      (QuarticNet.dehomogenizeAtZero Q).eval
        (s • affineLineDirection i j) = 0) :
    ∃ a b : L, Q =
      C a * X 1 * X 2 + C b * X 3 * (X 1 + X 2 + X 3) := by
  obtain ⟨a, b, hab⟩ := affine_quadric_eq_split_pencil_of_fourLine_vanishing
    (QuarticNet.dehomogenizeAtZero Q)
    (dehomogenized_quadric_totalDegree_le_two Q hQ.totalDegree_le)
    hline
  refine ⟨a, b, ?_⟩
  apply QuarticNet.dehomogenizeAtZero_injective_on_homogeneous hQ
  · have hqa : (C a * X 1 * X 2 : MvPolynomial (Fin 4) L).IsHomogeneous 2 := by
      simpa only [mul_assoc] using
        ((isHomogeneous_X L (1 : Fin 4)).mul
          (isHomogeneous_X L (2 : Fin 4))).C_mul a
    have hqb :
        (C b * X 3 * (X 1 + X 2 + X 3) : MvPolynomial (Fin 4) L).IsHomogeneous 2 := by
      have hl : (X 1 + X 2 + X 3 : MvPolynomial (Fin 4) L).IsHomogeneous 1 :=
        ((isHomogeneous_X L (1 : Fin 4)).add
          (isHomogeneous_X L (2 : Fin 4))).add
          (isHomogeneous_X L (3 : Fin 4))
      simpa only [mul_assoc] using
        ((isHomogeneous_X L (3 : Fin 4)).mul hl).C_mul b
    exact hqa.add hqb
  · simpa [QuarticNet.dehomogenizeAtZero] using hab

/-- The twelve generic four-line roots detect precisely the defining
two-dimensional pencil of homogeneous quadrics. -/
theorem generic_fourLine_roots_quadratic_kernel_eq_split_pencil
    (K : Type u) [Field K] [CharZero K]
    {L : Type u} [Field L] [CharZero L]
    (φ : FractionRing (CubicTensorCoefficients K) →+* L)
    (x : Fin 2 → Fin 2 → Fin 3 → Fin 4 → L)
    (hinj : ∀ i j, Function.Injective (x i j))
    (hcubic : ∀ i j k,
      ((genericCubicTensor K).map φ).eval (x i j k) = 0)
    (hform : ∀ i j k, ∃ t : L,
      x i j k = t • (Pi.single 0 1 : Fin 4 → L) + lineDirection i j)
    (Q : MvPolynomial (Fin 4) L) (hQ : Q.IsHomogeneous 2)
    (hQzero : ∀ i j k, Q.eval (x i j k) = 0) :
    ∃ a b : L, Q =
      C a * X 1 * X 2 + C b * X 3 * (X 1 + X 2 + X 3) := by
  classical
  choose t ht using hform
  apply homogeneous_quadric_eq_split_pencil_of_fourLine_vanishing Q hQ
  intro i j
  have htinj : Function.Injective (t i j) :=
    fourLine_root_parameters_injective i j (x i j) (t i j)
      (hinj i j) (ht i j)
  have htnz : ∀ k, t i j k ≠ 0 := by
    intro k
    apply genericCubicTensor_fourLine_root_parameter_ne_zero K φ i j
    rw [← ht i j k]
    exact hcubic i j k
  apply dehomogenized_quadric_zero_on_fourLine_of_three_roots
    Q hQ i j (t i j) htinj htnz
  intro k
  rw [← ht i j k]
  exact hQzero i j k

end PfaffianDescent
