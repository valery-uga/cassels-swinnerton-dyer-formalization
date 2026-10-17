import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceGridSeparable
import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceGridIntersection

/-! # Twenty-seven distinct normalized geometric points in the native grid -/

noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective

namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

theorem voisinDegreeTenSelectedAvoidance_gridSlope_injective
    (L : Type u) [Field L] [CharZero L] :
    Function.Injective (voisinDegreeTenSelectedAvoidance_gridSlope L) := by
  intro a b h
  apply Fin.ext
  apply Nat.cast_injective (R := L)
  simpa only [voisinDegreeTenSelectedAvoidance_gridSlope, sub_add_cancel] using
    congrArg (fun x : L => x + 1) h

set_option backward.isDefEq.respectTransparency false in
/-- The explicit native grid admits twenty-seven distinct geometric vector
representatives in the chart `X₀ = 1`, and those representatives cover its
entire affine cone up to scalar multiplication. Separability is proved from
the absence of a ground-field rational point. -/
theorem voisinDegreeTenSelectedAvoidance_exists_twenty_seven_grid_points
    {K L : Type u} [Field K] [CharZero K] [Field L] [Algebra K L] [IsAlgClosed L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hno : ¬ ∃ s : Spec (.of K) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _) :
    ∃ x : Fin 27 → Fin 4 → L,
      Function.Injective x ∧
      (∀ i, x i 0 = 1) ∧
      (∀ i, x i ∈ MvPolynomial.zeroLocus L
        (voisinDegreeTenSelectedAvoidance_gridIdeal (p.map (algebraMap K L))
          (hp.map (algebraMap K L))).toIdeal) ∧
      ∀ y ∈ MvPolynomial.zeroLocus L
        (voisinDegreeTenSelectedAvoidance_gridIdeal (p.map (algebraMap K L))
          (hp.map (algebraMap K L))).toIdeal,
        y = 0 ∨ ∃ (i : Fin 27) (t : L), y = t • x i := by
  classical
  let φ := algebraMap K L
  letI : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  obtain ⟨c, hc⟩ := homogeneous_cubic_has_tensor_any_characteristic p hp
  let d := c.map φ
  have hd : d.toMvPolynomial = p.map φ := by
    rw [Cubic.toMvPolynomial_map, hc]
  have hu : d.eval (voisinDegreeTenSelectedAvoidance_gridInfinity L) ≠ 0 := by
    have huc := voisinDegreeTenSelectedAvoidance_grid_tensor_infinity_ne_zero p hp hno c hc
    have hcoord : (fun i => φ (voisinDegreeTenSelectedAvoidance_gridInfinity K i)) =
        voisinDegreeTenSelectedAvoidance_gridInfinity L := by
      ext i
      fin_cases i <;> simp [voisinDegreeTenSelectedAvoidance_gridInfinity]
    rw [← hcoord, Cubic.eval_map]
    exact (map_ne_zero φ).mpr huc
  have hline : ∀ a b : Fin 3, ∃ x : Fin 3 → Fin 4 → L,
      (∀ k, d.eval (x k) = 0) ∧ Function.Injective x ∧
      (∀ k, ∃ t : L, x k = t • voisinDegreeTenSelectedAvoidance_gridInfinity L +
        voisinDegreeTenSelectedAvoidance_gridBase L a b) ∧
      ∀ s t : L, d.eval (s • voisinDegreeTenSelectedAvoidance_gridInfinity L +
          t • voisinDegreeTenSelectedAvoidance_gridBase L a b) = 0 →
        s • voisinDegreeTenSelectedAvoidance_gridInfinity L +
          t • voisinDegreeTenSelectedAvoidance_gridBase L a b = 0 ∨
        ∃ (k : Fin 3) (w : L),
          s • voisinDegreeTenSelectedAvoidance_gridInfinity L +
            t • voisinDegreeTenSelectedAvoidance_gridBase L a b = w • x k := by
    intro a b
    apply exists_three_cubic_line_points_cover_of_separable d _ _ hu
    rw [← voisinDegreeTenSelectedAvoidance_grid_linePolynomial_map φ c a b]
    exact (voisinDegreeTenSelectedAvoidance_grid_linePolynomial_separable p hp hno c hc a b).map
  choose z hz hzinj hzform hzcover using hline
  have hz0 : ∀ a b k, z a b k 0 = 1 := by
    intro a b k
    obtain ⟨t, ht⟩ := hzform a b k
    simp [ht, voisinDegreeTenSelectedAvoidance_gridInfinity,
      voisinDegreeTenSelectedAvoidance_gridBase]
  have hz1 : ∀ a b k, z a b k 1 = voisinDegreeTenSelectedAvoidance_gridSlope L a := by
    intro a b k
    obtain ⟨t, ht⟩ := hzform a b k
    simp [ht, voisinDegreeTenSelectedAvoidance_gridInfinity,
      voisinDegreeTenSelectedAvoidance_gridBase]
  have hz2 : ∀ a b k, z a b k 2 = voisinDegreeTenSelectedAvoidance_gridSlope L b := by
    intro a b k
    obtain ⟨t, ht⟩ := hzform a b k
    simp [ht, voisinDegreeTenSelectedAvoidance_gridInfinity,
      voisinDegreeTenSelectedAvoidance_gridBase]
  let e : Fin 27 ≃ Fin 3 × Fin 3 × Fin 3 :=
    (Fintype.equivFinOfCardEq (by decide : Fintype.card (Fin 3 × Fin 3 × Fin 3) = 27)).symm
  let x : Fin 27 → Fin 4 → L := fun i => z (e i).1 (e i).2.1 (e i).2.2
  let J := voisinDegreeTenSelectedAvoidance_gridIdeal (p.map φ) (hp.map φ)
  have hzinJ : ∀ a b k, z a b k ∈ MvPolynomial.zeroLocus L J.toIdeal := by
    intro a b k s hs
    have hpzero : (p.map φ).eval (z a b k) = 0 := by
      rw [← hd]
      change MvPolynomial.eval₂ (RingHom.id L) (z a b k) d.toMvPolynomial = 0
      rw [Cubic.eval_toMvPolynomial]
      exact hz a b k
    have hqzero : (voisinDegreeTenSelectedAvoidance_gridCubic L 1).eval (z a b k) = 0 := by
      rw [voisinDegreeTenSelectedAvoidance_gridCubic, map_prod]
      apply Finset.prod_eq_zero_iff.mpr
      refine ⟨a, Finset.mem_univ _, ?_⟩
      simp [voisinDegreeTenSelectedAvoidance_gridPlane, hz0, hz1]
    have hrzero : (voisinDegreeTenSelectedAvoidance_gridCubic L 2).eval (z a b k) = 0 := by
      rw [voisinDegreeTenSelectedAvoidance_gridCubic, map_prod]
      apply Finset.prod_eq_zero_iff.mpr
      refine ⟨b, Finset.mem_univ _, ?_⟩
      simp [voisinDegreeTenSelectedAvoidance_gridPlane, hz0, hz2]
    have hker : J.toIdeal ≤ RingHom.ker (MvPolynomial.eval (z a b k)) := by
      apply Ideal.span_le.mpr
      intro f hf
      rcases hf with rfl | rfl | rfl
      · exact hpzero
      · exact hqzero
      · exact hrzero
    exact hker hs
  refine ⟨x, ?_, (fun i => hz0 _ _ _), (fun i => hzinJ _ _ _), ?_⟩
  · intro i j hij
    have ha : (e i).1 = (e j).1 :=
      voisinDegreeTenSelectedAvoidance_gridSlope_injective L (by
        have h := congrFun hij 1
        simpa only [x, hz1] using h)
    have hb : (e i).2.1 = (e j).2.1 :=
      voisinDegreeTenSelectedAvoidance_gridSlope_injective L (by
        have h := congrFun hij 2
        simpa only [x, hz2] using h)
    have hk : (e i).2.2 = (e j).2.2 := hzinj (e i).1 (e i).2.1 (by
      simpa only [x, ← ha, ← hb] using hij)
    apply e.injective
    exact Prod.ext ha (Prod.ext hb hk)
  · intro y hy
    have hpzero : (p.map φ).eval y = 0 := hy _ (Ideal.subset_span (by simp [φ, J,
      voisinDegreeTenSelectedAvoidance_gridIdeal, tripleCompleteIntersectionHomogeneousIdeal_toIdeal,
      tripleCompleteIntersectionIdeal]))
    have hqzero : ∏ a : Fin 3, (voisinDegreeTenSelectedAvoidance_gridPlane L 1 a).eval y = 0 := by
      have h := hy (voisinDegreeTenSelectedAvoidance_gridCubic L 1)
        (Ideal.subset_span (by simp [J, voisinDegreeTenSelectedAvoidance_gridIdeal,
          tripleCompleteIntersectionHomogeneousIdeal_toIdeal, tripleCompleteIntersectionIdeal]))
      simpa [voisinDegreeTenSelectedAvoidance_gridCubic, map_prod] using h
    have hrzero : ∏ b : Fin 3, (voisinDegreeTenSelectedAvoidance_gridPlane L 2 b).eval y = 0 := by
      have h := hy (voisinDegreeTenSelectedAvoidance_gridCubic L 2)
        (Ideal.subset_span (by simp [J, voisinDegreeTenSelectedAvoidance_gridIdeal,
          tripleCompleteIntersectionHomogeneousIdeal_toIdeal, tripleCompleteIntersectionIdeal]))
      simpa [voisinDegreeTenSelectedAvoidance_gridCubic, map_prod] using h
    obtain ⟨a, -, ha⟩ := Finset.prod_eq_zero_iff.mp hqzero
    obtain ⟨b, -, hb⟩ := Finset.prod_eq_zero_iff.mp hrzero
    obtain ⟨s, t, hyform⟩ := voisinDegreeTenSelectedAvoidance_grid_line_parameters a b y ha hb
    have hdzero : d.eval (s • voisinDegreeTenSelectedAvoidance_gridInfinity L +
        t • voisinDegreeTenSelectedAvoidance_gridBase L a b) = 0 := by
      rw [hyform, ← hd] at hpzero
      change MvPolynomial.eval₂ (RingHom.id L) _ d.toMvPolynomial = 0 at hpzero
      rw [Cubic.eval_toMvPolynomial] at hpzero
      exact hpzero
    rcases hzcover a b s t hdzero with hzero | ⟨k, w, hw⟩
    · exact Or.inl (hyform.trans hzero)
    · refine Or.inr ⟨e.symm (a, b, k), w, ?_⟩
      simpa only [x, Equiv.apply_symm_apply] using hyform.trans hw

end PfaffianDescent
