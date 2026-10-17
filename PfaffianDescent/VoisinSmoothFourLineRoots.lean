import PfaffianDescent.VoisinGenericLineDescent
import PfaffianDescent.VoisinFourLineCoverage
import PfaffianDescent.VoisinSplitTwelvePointNumerics
import PfaffianDescent.VoisinFiniteTripleBezout
import PfaffianDescent.VoisinFourLineQuadraticCoordinates
import PfaffianDescent.VoisinLinearChangeEvaluation

/-!
# Twelve geometric roots from the smooth four-line witness

The four standard line restrictions produced after the universal invertible
coordinate change remain separable over an algebraic closure.  Choosing their
three roots gives twelve pairwise distinct projective points on the standard
split cubic--quadric--quadric intersection.
-/

namespace PfaffianDescent

open MvPolynomial Polynomial AlgebraicGeometry
open AllCharacteristics
open AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

private abbrev standardBase (K : Type u) [Field K] : Fin 4 → K :=
  Pi.single 0 1

theorem standardBase_map
    {K L : Type u} [Field K] [Field L] (f : K →+* L) :
    (fun i => f (standardBase K i)) = standardBase L := by
  funext i
  fin_cases i <;> simp [standardBase]

theorem lineDirection_map
    {K L : Type u} [Field K] [Field L] (f : K →+* L) (i j : Fin 2) :
    (fun k => f (lineDirection (L := K) i j k)) =
      lineDirection (L := L) i j := by
  funext k
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp [lineDirection]

/-- Four separable standard line sections over a field yield twelve distinct
geometric roots over any algebraically closed extension. -/
theorem exists_standard_twelve_split_projectivelyDistinct_roots
    {K L : Type u} [Field K] [Field L] [IsAlgClosed L]
    (f : K →+* L) (c : Cubic K 4)
    (hbase : c.eval (standardBase K) ≠ 0)
    (hdirection : ∀ q : Fin 2 × Fin 2,
      c.eval (lineDirection q.1 q.2) ≠ 0)
    (hsep : ∀ q : Fin 2 × Fin 2,
      (cubicLinePolynomial c (standardBase K)
        (lineDirection q.1 q.2)).Separable) :
    ∃ x : Fin 2 → Fin 2 → Fin 3 → Fin 4 → L,
      (∀ i j k,
        (c.map f).eval (x i j k) = 0 ∧
        (X 1 * X 2 : MvPolynomial (Fin 4) L).eval (x i j k) = 0 ∧
        (X 3 * (X 1 + X 2 + X 3) : MvPolynomial (Fin 4) L).eval
          (x i j k) = 0) ∧
      (∀ i j, Function.Injective (x i j)) ∧
      (∀ i j k, ∃ t : L, t ≠ 0 ∧
        x i j k = t • standardBase L + lineDirection i j) ∧
      (∀ {i j i' j' : Fin 2} {k k' : Fin 3},
        (i, j, k) ≠ (i', j', k') → ∀ a : L,
          a • x i j k ≠ x i' j' k') := by
  classical
  have hbaseL : (c.map f).eval (standardBase L) ≠ 0 := by
    have hev := Cubic.eval_map f c (standardBase K)
    rw [standardBase_map f] at hev
    intro hzero
    apply hbase
    apply f.injective
    simpa using hev.symm.trans hzero
  have hsepL : ∀ i j : Fin 2,
      (cubicLinePolynomial (c.map f) (standardBase L)
        (lineDirection i j)).Separable := by
    intro i j
    have h : ((cubicLinePolynomial c (standardBase K)
        (lineDirection i j)).map f).Separable := (hsep (i, j)).map
    rw [cubicLinePolynomial_map] at h
    simpa [standardBase_map f, lineDirection_map f i j] using h
  have hlocal : ∀ i j : Fin 2,
      ∃ x : Fin 3 → Fin 4 → L,
        (∀ k, (c.map f).eval (x k) = 0) ∧
        Function.Injective x ∧
        (∀ k, ∃ t : L, t ≠ 0 ∧
          x k = t • standardBase L + lineDirection i j) := by
    intro i j
    obtain ⟨x, hxzero, hxinj, hxform, -⟩ :=
      exists_three_cubic_line_points_cover_of_separable
        (c.map f) (standardBase L) (lineDirection i j) hbaseL (hsepL i j)
    have hxform' : ∀ k, ∃ t : L, t ≠ 0 ∧
        x k = t • standardBase L + lineDirection i j := by
      intro k
      obtain ⟨t, ht⟩ := hxform k
      refine ⟨t, ?_, ht⟩
      intro ht0
      subst t
      have hdirL : (c.map f).eval (lineDirection i j) ≠ 0 := by
        have hev := Cubic.eval_map f c (lineDirection (L := K) i j)
        rw [lineDirection_map f i j] at hev
        intro hzero
        apply hdirection (i, j)
        apply f.injective
        simpa using hev.symm.trans hzero
      apply hdirL
      simpa [ht] using hxzero k
    exact ⟨x, hxzero, hxinj, hxform'⟩
  choose x hxzero hxinj hxformnz using hlocal
  have hxform : ∀ i j k, ∃ t : L,
      x i j k = t • standardBase L + lineDirection i j := by
    intro i j k
    obtain ⟨t, -, ht⟩ := hxformnz i j k
    exact ⟨t, ht⟩
  refine ⟨x, ?_, hxinj, hxformnz, ?_⟩
  · intro i j k
    obtain ⟨t, -, ht⟩ := hxformnz i j k
    rw [ht]
    have hsplit := standard_split_quadrics_zero_on_line (L := L) i j t
    exact ⟨by simpa [ht] using hxzero i j k, hsplit.1, hsplit.2⟩
  · intro i j i' j' k k' hindex a
    exact shearedFourLines_twelve_roots_projectively_distinct
      (standardBase L) (by simp [standardBase]) x hxinj hxform hindex a

/-- Three affine-chart roots on each standard line determine the complete
two-dimensional pencil of quadrics through the twelve points. -/
theorem standard_fourLine_roots_quadratic_kernel_eq_split_pencil
    {L : Type u} [Field L] [CharZero L]
    (x : Fin 2 → Fin 2 → Fin 3 → Fin 4 → L)
    (hinj : ∀ i j, Function.Injective (x i j))
    (hform : ∀ i j k, ∃ t : L, t ≠ 0 ∧
      x i j k = t • standardBase L + lineDirection i j)
    (Q : MvPolynomial (Fin 4) L) (hQ : Q.IsHomogeneous 2)
    (hQzero : ∀ i j k, Q.eval (x i j k) = 0) :
    ∃ a b : L, Q =
      MvPolynomial.C a * X 1 * X 2 +
        MvPolynomial.C b * X 3 * (X 1 + X 2 + X 3) := by
  classical
  choose t ht using hform
  have htnz : ∀ i j k, t i j k ≠ 0 := fun i j k => (ht i j k).1
  have htform : ∀ i j k,
      x i j k = t i j k • standardBase L + lineDirection i j :=
    fun i j k => (ht i j k).2
  apply homogeneous_quadric_eq_split_pencil_of_fourLine_vanishing Q hQ
  intro i j
  have htinj : Function.Injective (t i j) :=
    fourLine_root_parameters_injective i j (x i j) (t i j)
      (hinj i j) (htform i j)
  apply dehomogenized_quadric_zero_on_fourLine_of_three_roots
    Q hQ i j (t i j) htinj (htnz i j)
  intro k
  rw [← htform i j k]
  exact hQzero i j k

/-- Eight of the twelve standard four-line roots impose all eight independent
quadratic conditions, while retaining distinct projective directions. -/
theorem standard_fourLine_roots_exists_finEight_quadratic_witness
    {L : Type u} [Field L] [CharZero L]
    (x₀ : Fin 2 → Fin 2 → Fin 3 → Fin 4 → L)
    (hinj : ∀ i j, Function.Injective (x₀ i j))
    (hform : ∀ i j k, ∃ t : L, t ≠ 0 ∧
      x₀ i j k = t • standardBase L + lineDirection i j) :
    ∃ y : Fin 8 → Fin 4 → L,
      Function.Surjective
        (homogeneousSectionRestriction (K := L)
          (fun (j : Fin 4) (i : Fin 8) => y i j) 2) ∧
      (∀ i, (X 1 * X 2 : MvPolynomial (Fin 4) L).eval (y i) = 0 ∧
        (X 3 * (X 1 + X 2 + X 3) : MvPolynomial (Fin 4) L).eval
          (y i) = 0) ∧
      (∀ i, y i ≠ 0) ∧
      (∀ i j, i ≠ j → ∀ a : L, a • y i ≠ y j) ∧
      ∀ i, ∃ a b : Fin 2, ∃ k : Fin 3, y i = x₀ a b k := by
  classical
  let e : Fin 12 ≃ Fin 2 × Fin 2 × Fin 3 :=
    (Fintype.equivFinOfCardEq (by decide :
      Fintype.card (Fin 2 × Fin 2 × Fin 3) = 12)).symm
  let x : Fin 12 → Fin 4 → L :=
    fun n => x₀ (e n).1 (e n).2.1 (e n).2.2
  let q : MvPolynomial (Fin 4) L := X 1 * X 2
  let r : MvPolynomial (Fin 4) L := X 3 * (X 1 + X 2 + X 3)
  let hq : q.IsHomogeneous 2 :=
    (isHomogeneous_X L 1).mul (isHomogeneous_X L 2)
  let hr : r.IsHomogeneous 2 := (isHomogeneous_X L 3).mul
    (((isHomogeneous_X L 1).add (isHomogeneous_X L 2)).add
      (isHomogeneous_X L 3))
  have hqr : LinearIndependent L
      ![(⟨q, hq⟩ : homogeneousSubmodule (Fin 4) L 2), ⟨r, hr⟩] :=
    homogeneous_quadric_pair_linearIndependent_of_polynomials
      q r hq hr standard_split_quadric_pair_linearIndependent
  let E := homogeneousSectionRestriction (K := L)
    (fun j n => x n j : Fin 4 → Fin 12 → L) 2
  have hkeriff : ∀ s : homogeneousSubmodule (Fin 4) L 2,
      s ∈ LinearMap.ker E ↔
        ∃ a b : L, s.1 = MvPolynomial.C a * q + MvPolynomial.C b * r := by
    intro s
    constructor
    · intro hs
      have hzero : ∀ i j k, s.1.eval (x₀ i j k) = 0 := by
        intro i j k
        have hv := congrArg (fun z : Fin 12 → L => z (e.symm (i, j, k)))
          (LinearMap.mem_ker.mp hs)
        simpa [E, x, homogeneousSectionRestriction_apply,
          twelve_point_product_evaluation_apply] using hv
      obtain ⟨a, b, hab⟩ :=
        standard_fourLine_roots_quadratic_kernel_eq_split_pencil
          x₀ hinj hform s.1 s.2 hzero
      exact ⟨a, b, by simpa [q, r, mul_assoc] using hab⟩
    · rintro ⟨a, b, hab⟩
      apply LinearMap.mem_ker.mpr
      funext n
      obtain ⟨t, -, ht⟩ := hform (e n).1 (e n).2.1 (e n).2.2
      have hsplit := standard_split_quadrics_zero_on_line
        (L := L) (e n).1 (e n).2.1 t
      simp [E, x, homogeneousSectionRestriction_apply,
        twelve_point_product_evaluation_apply, hab, q, r, ht,
        hsplit.1, hsplit.2]
  have hker : Module.finrank L (LinearMap.ker E) = 2 :=
    twelve_point_homogeneousSectionRestriction_ker_finrank_eq_two_of_kernel_iff
      q r hq hr hqr x hkeriff
  obtain ⟨κ, a, inst, ha, hcard, hsurj, -⟩ :=
    twelve_point_exists_eight_split_restriction_surjective_of_kernel_finrank
      x hker
  letI : Fintype κ := inst
  let d : Fin 8 ≃ κ := (Fintype.equivFinOfCardEq hcard).symm
  let y : Fin 8 → Fin 4 → L := fun i => x (a (d i))
  refine ⟨y, ?_, ?_, ?_, ?_, ?_⟩
  · intro z
    obtain ⟨s, hs⟩ := hsurj (fun t : κ => z (d.symm t))
    refine ⟨s, ?_⟩
    funext i
    have hi := congrFun hs (d i)
    simpa [y, homogeneousSectionRestriction_apply,
      finite_product_evaluation_apply] using hi
  · intro i
    obtain ⟨t, -, ht⟩ :=
      hform (e (a (d i))).1 (e (a (d i))).2.1 (e (a (d i))).2.2
    have hsplit := standard_split_quadrics_zero_on_line
      (L := L) (e (a (d i))).1 (e (a (d i))).2.1 t
    simpa [y, x, ht] using hsplit
  · intro i
    let ii := (e (a (d i))).1
    let jj := (e (a (d i))).2.1
    let kk := (e (a (d i))).2.2
    obtain ⟨t, -, ht⟩ :=
      hform ii jj kk
    change x₀ ii jj kk ≠ 0
    rw [ht]
    intro hzero
    have hk := congrFun hzero (if ii = 0 then (2 : Fin 4) else 1)
    by_cases hii : ii = 0
    · by_cases hjj : jj = 0 <;>
        simp [hii, hjj, standardBase, lineDirection] at hk
    · by_cases hjj : jj = 0 <;>
        simp [hii, hjj, standardBase, lineDirection] at hk
  · intro i j hij b
    have hindex : e (a (d i)) ≠ e (a (d j)) := by
      intro heq
      apply hij
      exact d.injective (ha (e.injective heq))
    exact shearedFourLines_twelve_roots_projectively_distinct
      (standardBase L) (by simp [standardBase]) x₀ hinj
      (fun i j k => by
        obtain ⟨t, -, ht⟩ := hform i j k
        exact ⟨t, ht⟩) hindex b
  · intro i
    exact ⟨(e (a (d i))).1, (e (a (d i))).2.1,
      (e (a (d i))).2.2, rfl⟩

/-- A smooth cubic admits an invertible coordinate change whose standard
split-quadric intersection has twelve pairwise distinct geometric points. -/
theorem exists_linear_change_and_standard_twelve_split_roots_of_smooth
    {K : Type u} [Field K] [CharZero K]
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) (hF0 : F ≠ 0)
    (c : Cubic K 4) (hc : c.toMvPolynomial = F)
    [Smooth (AllCharacteristics.HomogeneousProjective.hypersurfaceToBase F hF)] :
    ∃ (M : Matrix (Fin 4) (Fin 4) K)
      (x : Fin 2 → Fin 2 → Fin 3 → Fin 4 → AlgebraicClosure K),
      IsUnit M.det ∧
      (∀ i j k,
        ((c.compLinear M).map (algebraMap K (AlgebraicClosure K))).eval
            (x i j k) = 0 ∧
        (X 1 * X 2 : MvPolynomial (Fin 4) (AlgebraicClosure K)).eval
            (x i j k) = 0 ∧
        (X 3 * (X 1 + X 2 + X 3) :
          MvPolynomial (Fin 4) (AlgebraicClosure K)).eval (x i j k) = 0) ∧
      (∀ i j, Function.Injective (x i j)) ∧
      (∀ i j k, ∃ t : AlgebraicClosure K, t ≠ 0 ∧
        x i j k = t • standardBase (AlgebraicClosure K) +
          lineDirection i j) ∧
      (∀ {i j i' j' : Fin 2} {k k' : Fin 3},
        (i, j, k) ≠ (i', j', k') → ∀ a : AlgebraicClosure K,
          a • x i j k ≠ x i' j' k') := by
  obtain ⟨M, hM, hbase, hdirection, hsep⟩ :=
    exists_linear_change_with_standard_four_separable_nonzero_lines_of_smooth
      F hF hF0 c hc
  obtain ⟨x, hx, hxinj, hxform, hdistinct⟩ :=
    exists_standard_twelve_split_projectivelyDistinct_roots
      (algebraMap K (AlgebraicClosure K)) (c.compLinear M)
        hbase hdirection hsep
  exact ⟨M, x, hM, hx, hxinj, hxform, hdistinct⟩

/-- Eight selected roots of the transverse split intersection impose all
eight independent quadratic conditions. -/
theorem exists_linear_change_and_geometricEight_quadratic_witness_of_smooth
    {K : Type u} [Field K] [CharZero K]
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) (hF0 : F ≠ 0)
    (c : Cubic K 4) (hc : c.toMvPolynomial = F)
    [Smooth (hypersurfaceToBase F hF)] :
    ∃ (M : Matrix (Fin 4) (Fin 4) K)
      (y : Fin 8 → Fin 4 → AlgebraicClosure K),
      IsUnit M.det ∧
      Function.Surjective
        (homogeneousSectionRestriction (K := AlgebraicClosure K)
          (fun (j : Fin 4) (i : Fin 8) => y i j) 2) ∧
      (∀ i, ((c.compLinear M).map
        (algebraMap K (AlgebraicClosure K))).toMvPolynomial.eval (y i) = 0) ∧
      (∀ i, (X 1 * X 2 :
          MvPolynomial (Fin 4) (AlgebraicClosure K)).eval (y i) = 0 ∧
        (X 3 * (X 1 + X 2 + X 3) :
          MvPolynomial (Fin 4) (AlgebraicClosure K)).eval (y i) = 0) ∧
      (∀ i, y i ≠ 0) ∧
      ∀ i j, i ≠ j → ∀ a : AlgebraicClosure K, a • y i ≠ y j := by
  obtain ⟨M, x, hM, hroots, hxinj, hxform, -⟩ :=
    exists_linear_change_and_standard_twelve_split_roots_of_smooth
      F hF hF0 c hc
  obtain ⟨y, hsurj, hquadrics, hy0, hdistinct, hselected⟩ :=
    standard_fourLine_roots_exists_finEight_quadratic_witness x hxinj hxform
  refine ⟨M, y, hM, hsurj, ?_, hquadrics, hy0, hdistinct⟩
  intro i
  obtain ⟨a, b, k, hy⟩ := hselected i
  rw [hy]
  let cL := (c.compLinear M).map (algebraMap K (AlgebraicClosure K))
  have hev := Cubic.eval_toMvPolynomial
    (RingHom.id (AlgebraicClosure K)) cL (x a b k)
  have hmap : cL.map (RingHom.id (AlgebraicClosure K)) = cL := by
    funext n
    rfl
  rw [hmap] at hev
  have hzero : cL.eval (x a b k) = 0 := (hroots a b k).1
  change cL.toMvPolynomial.eval (x a b k) = 0
  exact hev.trans hzero

/-- Returning an eight-point witness through an invertible coordinate
change preserves cubic incidence, quadratic interpolation, nonzeroness, and
pairwise projective distinctness. -/
theorem transport_geometricEight_quadratic_witness
    {K L : Type u} [Field K] [Field L] (f : K →+* L)
    (c : Cubic K 4) (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnit M.det)
    (y : Fin 8 → Fin 4 → L)
    (hsurj : Function.Surjective
      (homogeneousSectionRestriction (K := L)
        (fun (j : Fin 4) (i : Fin 8) => y i j) 2))
    (hzero : ∀ i, ((c.compLinear M).map f).toMvPolynomial.eval (y i) = 0)
    (hy0 : ∀ i, y i ≠ 0)
    (hdistinct : ∀ i j, i ≠ j → ∀ a : L, a • y i ≠ y j) :
    ∃ z : Fin 8 → Fin 4 → L,
      Function.Surjective
        (homogeneousSectionRestriction (K := L)
          (fun (j : Fin 4) (i : Fin 8) => z i j) 2) ∧
      (∀ i, (c.map f).toMvPolynomial.eval (z i) = 0) ∧
      (∀ i, z i ≠ 0) ∧
      ∀ i j, i ≠ j → ∀ a : L, a • z i ≠ z j := by
  have hunit : IsUnit (M.map f) := Matrix.map_isUnit_of_isUnit_det f M hM
  have heq : (M.map f).det = f M.det := by
    simpa only [RingHom.mapMatrix_apply] using (RingHom.map_det f M).symm
  have hdet : IsUnit (M.map f).det := by
    rw [heq]
    exact hM.map f
  exact ⟨fun i => (M.map f).mulVec (y i),
    homogeneousSectionRestriction_surjective_linearChange
      (M.map f) hdet y hsurj,
    fun i => (Cubic.compLinear_map_toMvPolynomial_eval f c M (y i)).symm.trans
      (hzero i),
    linearChange_points_nonzero (M.map f) hunit (y := y) hy0,
    linearChange_points_projectivelyDistinct
      (M.map f) hunit (y := y) hdistinct⟩

/-- Every smooth cubic has eight geometric points in its original
coordinates which impose independent quadratic conditions and are pairwise
projectively distinct. -/
theorem exists_geometricEight_quadratic_witness_of_smooth
    {K : Type u} [Field K] [CharZero K]
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) (hF0 : F ≠ 0)
    (c : Cubic K 4) (hc : c.toMvPolynomial = F)
    [Smooth (hypersurfaceToBase F hF)] :
    ∃ z : Fin 8 → Fin 4 → AlgebraicClosure K,
      Function.Surjective
        (homogeneousSectionRestriction (K := AlgebraicClosure K)
          (fun (j : Fin 4) (i : Fin 8) => z i j) 2) ∧
      (∀ i, (c.map (algebraMap K (AlgebraicClosure K))).toMvPolynomial.eval
        (z i) = 0) ∧
      (∀ i, z i ≠ 0) ∧
      ∀ i j, i ≠ j → ∀ a : AlgebraicClosure K, a • z i ≠ z j := by
  obtain ⟨M, y, hM, hsurj, hzero, -, hy0, hdistinct⟩ :=
    exists_linear_change_and_geometricEight_quadratic_witness_of_smooth
      F hF hF0 c hc
  exact transport_geometricEight_quadratic_witness
    (algebraMap K (AlgebraicClosure K)) c M hM y
      hsurj hzero hy0 hdistinct

/-- A specified transverse four-line witness gives a finite étale
length-twelve standard split complete intersection after passage to an
algebraically closed field. -/
theorem standard_split_finiteEtale_of_four_line_witness
    {K L : Type u} [Field K] [Field L] [CharZero L] [IsAlgClosed L]
    (f : K →+* L) (cK : Cubic K 4)
    (hbase : cK.eval (standardBase K) ≠ 0)
    (hdirection : ∀ q : Fin 2 × Fin 2,
      cK.eval (lineDirection q.1 q.2) ≠ 0)
    (hsep : ∀ q : Fin 2 × Fin 2,
      (cubicLinePolynomial cK (standardBase K)
        (lineDirection q.1 q.2)).Separable) :
    let cL := cK.map f
    let p := cL.toMvPolynomial
    let hp := cubic_toMvPolynomial_isHomogeneous_three cL
    let q : MvPolynomial (Fin 4) L := X 1 * X 2
    let r : MvPolynomial (Fin 4) L := X 3 * (X 1 + X 2 + X 3)
    let hq : q.IsHomogeneous 2 :=
      (isHomogeneous_X L 1).mul (isHomogeneous_X L 2)
    let hr : r.IsHomogeneous 2 :=
      (isHomogeneous_X L 3).mul
        (((isHomogeneous_X L 1).add (isHomogeneous_X L 2)).add
          (isHomogeneous_X L 3))
    let I := tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr
    ∃ hfinite : IsFinite (toBase I),
      letI : IsFinite (toBase I) := hfinite
      finiteSchemeRank (toBase I) = 12 ∧ Etale (toBase I) := by
  dsimp only
  let cL := cK.map f
  let p := cL.toMvPolynomial
  let hp := cubic_toMvPolynomial_isHomogeneous_three cL
  let q : MvPolynomial (Fin 4) L := X 1 * X 2
  let r : MvPolynomial (Fin 4) L := X 3 * (X 1 + X 2 + X 3)
  let hq : q.IsHomogeneous 2 :=
    (isHomogeneous_X L 1).mul (isHomogeneous_X L 2)
  let hr : r.IsHomogeneous 2 :=
    (isHomogeneous_X L 3).mul
      (((isHomogeneous_X L 1).add (isHomogeneous_X L 2)).add
        (isHomogeneous_X L 3))
  let I := tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr
  have hbaseL : cL.eval (standardBase L) ≠ 0 := by
    have hev := Cubic.eval_map f cK (standardBase K)
    rw [standardBase_map f] at hev
    intro hzero
    apply hbase
    apply f.injective
    simpa [cL] using hev.symm.trans hzero
  have hpbase : p.eval (standardBase L) ≠ 0 := by
    have hev := Cubic.eval_toMvPolynomial (RingHom.id L) cL (standardBase L)
    rw [Cubic.map_id] at hev
    intro hzero
    apply hbaseL
    exact hev.symm.trans (by simpa [p] using hzero)
  obtain ⟨x, hroots, hxinj, hxform, -⟩ :=
    exists_standard_twelve_split_projectivelyDistinct_roots
      f cK hbase hdirection hsep
  have hroots' : ∀ i j k,
      p.eval (x i j k) = 0 ∧ q.eval (x i j k) = 0 ∧
        r.eval (x i j k) = 0 := by
    intro i j k
    have hev := Cubic.eval_toMvPolynomial (RingHom.id L) cL (x i j k)
    rw [Cubic.map_id] at hev
    exact ⟨by simpa [p, cL] using hev.trans (hroots i j k).1,
      by simpa [q] using (hroots i j k).2.1,
      by simpa [r] using (hroots i j k).2.2⟩
  have hfinite : IsFinite (toBase I) := by
    exact standardFourLines_finite p hp hpbase
  letI : IsFinite (toBase I) := hfinite
  have hx0 : x 0 0 0 ≠ 0 := by
    obtain ⟨t, -, ht⟩ := hxform 0 0 0
    rw [ht]
    exact standardFourLines_genuine 0 0 t
  have hnonempty : Nonempty (scheme I) := by
    obtain ⟨z, -⟩ := point_of_coordinates I (RingHom.id L)
      (x 0 0 0) hx0 (by
        exact tripleCompleteIntersection_vector_zero_of_generators
          p q r hp hq hr (x 0 0 0)
            (hroots' 0 0 0).1 (hroots' 0 0 0).2.1 (hroots' 0 0 0).2.2)
    exact ⟨z (IsLocalRing.closedPoint L)⟩
  have hrank : finiteSchemeRank (toBase I) = 12 :=
    cubicTwoQuadrics_finite_nonempty_rank_twelve p q r hp hq hr hnonempty
  have hetale : Etale (toBase I) := by
    exact cubic_two_quadric_etale_of_sheared_four_line_root_equations
      p q r hp hq hr hrank (standardBase L) (by simp [standardBase])
        x hxinj (fun i j k => by
          obtain ⟨t, -, ht⟩ := hxform i j k
          exact ⟨t, ht⟩) hroots'
  exact ⟨hfinite, hrank, hetale⟩

/-- The selected eight roots and the finite étale split complete
intersection can be obtained from the same coordinate change. -/
theorem exists_linear_change_geometricEight_and_standard_split_etale_of_smooth
    {K : Type u} [Field K] [CharZero K]
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) (hF0 : F ≠ 0)
    (c : Cubic K 4) (hc : c.toMvPolynomial = F)
    [Smooth (hypersurfaceToBase F hF)] :
    ∃ (M : Matrix (Fin 4) (Fin 4) K)
      (y : Fin 8 → Fin 4 → AlgebraicClosure K),
      IsUnit M.det ∧
      Function.Surjective
        (homogeneousSectionRestriction (K := AlgebraicClosure K)
          (fun (j : Fin 4) (i : Fin 8) => y i j) 2) ∧
      (∀ i, ((c.compLinear M).map
        (algebraMap K (AlgebraicClosure K))).toMvPolynomial.eval (y i) = 0) ∧
      (∀ i, (X 1 * X 2 :
          MvPolynomial (Fin 4) (AlgebraicClosure K)).eval (y i) = 0 ∧
        (X 3 * (X 1 + X 2 + X 3) :
          MvPolynomial (Fin 4) (AlgebraicClosure K)).eval (y i) = 0) ∧
      (∀ i, y i ≠ 0) ∧
      (∀ i j, i ≠ j → ∀ a : AlgebraicClosure K, a • y i ≠ y j) ∧
      let L := AlgebraicClosure K
      let cL := (c.compLinear M).map (algebraMap K L)
      let p := cL.toMvPolynomial
      let hp := cubic_toMvPolynomial_isHomogeneous_three cL
      let q : MvPolynomial (Fin 4) L := X 1 * X 2
      let r : MvPolynomial (Fin 4) L := X 3 * (X 1 + X 2 + X 3)
      let hq : q.IsHomogeneous 2 :=
        (isHomogeneous_X L 1).mul (isHomogeneous_X L 2)
      let hr : r.IsHomogeneous 2 :=
        (isHomogeneous_X L 3).mul
          (((isHomogeneous_X L 1).add (isHomogeneous_X L 2)).add
            (isHomogeneous_X L 3))
      let I := tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr
      ∃ hfinite : IsFinite (toBase I),
        letI : IsFinite (toBase I) := hfinite
        finiteSchemeRank (toBase I) = 12 ∧ Etale (toBase I) := by
  obtain ⟨M, hM, hbase, hdirection, hsep⟩ :=
    exists_linear_change_with_standard_four_separable_nonzero_lines_of_smooth
      F hF hF0 c hc
  let f : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K)
  let cK := c.compLinear M
  obtain ⟨x, hroots, hxinj, hxform, -⟩ :=
    exists_standard_twelve_split_projectivelyDistinct_roots
      f cK hbase hdirection hsep
  obtain ⟨y, hsurj, hquadrics, hy0, hdistinct, hselected⟩ :=
    standard_fourLine_roots_exists_finEight_quadratic_witness x hxinj hxform
  have hzero : ∀ i,
      (cK.map f).toMvPolynomial.eval (y i) = 0 := by
    intro i
    obtain ⟨a, b, k, hy⟩ := hselected i
    rw [hy]
    let cL := cK.map f
    have hev := Cubic.eval_toMvPolynomial
      (RingHom.id (AlgebraicClosure K)) cL (x a b k)
    have hmap : cL.map (RingHom.id (AlgebraicClosure K)) = cL := by
      funext n
      rfl
    rw [hmap] at hev
    have hroot : cL.eval (x a b k) = 0 := (hroots a b k).1
    change cL.toMvPolynomial.eval (x a b k) = 0
    exact hev.trans hroot
  have hEtale := standard_split_finiteEtale_of_four_line_witness
    f cK hbase hdirection hsep
  exact ⟨M, y, hM, hsurj, hzero, hquadrics, hy0, hdistinct, hEtale⟩

/-- The four-line construction gives a finite étale length-twelve standard
split complete intersection after algebraic closure. -/
theorem exists_linear_change_standard_split_finiteEtale_of_smooth
    {K : Type u} [Field K] [CharZero K]
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) (hF0 : F ≠ 0)
    (c : Cubic K 4) (hc : c.toMvPolynomial = F)
    [Smooth (hypersurfaceToBase F hF)] :
    ∃ M : Matrix (Fin 4) (Fin 4) K,
      IsUnit M.det ∧
      let L := AlgebraicClosure K
      let cL := (c.compLinear M).map (algebraMap K L)
      let p := cL.toMvPolynomial
      let hp := cubic_toMvPolynomial_isHomogeneous_three cL
      let q : MvPolynomial (Fin 4) L := X 1 * X 2
      let r : MvPolynomial (Fin 4) L := X 3 * (X 1 + X 2 + X 3)
      let hq : q.IsHomogeneous 2 :=
        (isHomogeneous_X L 1).mul (isHomogeneous_X L 2)
      let hr : r.IsHomogeneous 2 :=
        (isHomogeneous_X L 3).mul
          (((isHomogeneous_X L 1).add (isHomogeneous_X L 2)).add
            (isHomogeneous_X L 3))
      let I := tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr
      ∃ hfinite : IsFinite (toBase I),
        letI : IsFinite (toBase I) := hfinite
        finiteSchemeRank (toBase I) = 12 ∧ Etale (toBase I) := by
  obtain ⟨M, hM, hbase, hdirection, hsep⟩ :=
    exists_linear_change_with_standard_four_separable_nonzero_lines_of_smooth
      F hF hF0 c hc
  refine ⟨M, hM, ?_⟩
  dsimp only
  let L : Type u := AlgebraicClosure K
  let f : K →+* L := algebraMap K L
  let cK := c.compLinear M
  let cL := cK.map f
  let p := cL.toMvPolynomial
  let hp := cubic_toMvPolynomial_isHomogeneous_three cL
  let q : MvPolynomial (Fin 4) L := X 1 * X 2
  let r : MvPolynomial (Fin 4) L := X 3 * (X 1 + X 2 + X 3)
  let hq : q.IsHomogeneous 2 :=
    (isHomogeneous_X L 1).mul (isHomogeneous_X L 2)
  let hr : r.IsHomogeneous 2 :=
    (isHomogeneous_X L 3).mul
      (((isHomogeneous_X L 1).add (isHomogeneous_X L 2)).add
        (isHomogeneous_X L 3))
  let I := tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr
  have hbaseL : cL.eval (standardBase L) ≠ 0 := by
    have hev := Cubic.eval_map f cK (standardBase K)
    rw [standardBase_map f] at hev
    intro hzero
    apply hbase
    apply f.injective
    simpa [cK, cL] using hev.symm.trans hzero
  have hpbase : p.eval (standardBase L) ≠ 0 := by
    have hev := Cubic.eval_toMvPolynomial (RingHom.id L) cL (standardBase L)
    have hmap : cL.map (RingHom.id L) = cL := by funext i; rfl
    rw [hmap] at hev
    intro hzero
    apply hbaseL
    exact hev.symm.trans (by simpa [p] using hzero)
  obtain ⟨x, hroots, hxinj, hxform, -⟩ :=
    exists_standard_twelve_split_projectivelyDistinct_roots
      f cK hbase hdirection hsep
  have hroots' : ∀ i j k,
      p.eval (x i j k) = 0 ∧ q.eval (x i j k) = 0 ∧
        r.eval (x i j k) = 0 := by
    intro i j k
    have hev := Cubic.eval_toMvPolynomial (RingHom.id L) cL (x i j k)
    have hmap : cL.map (RingHom.id L) = cL := by funext n; rfl
    rw [hmap] at hev
    exact ⟨by simpa [p, cL] using hev.trans (hroots i j k).1,
      by simpa [q] using (hroots i j k).2.1,
      by simpa [r] using (hroots i j k).2.2⟩
  have hfinite : IsFinite (toBase I) := by
    exact standardFourLines_finite p hp hpbase
  letI : IsFinite (toBase I) := hfinite
  have hx0 : x 0 0 0 ≠ 0 := by
    obtain ⟨t, -, ht⟩ := hxform 0 0 0
    rw [ht]
    exact standardFourLines_genuine 0 0 t
  have hnonempty : Nonempty (scheme I) := by
    obtain ⟨z, -⟩ := point_of_coordinates I (RingHom.id L)
      (x 0 0 0) hx0 (by
        exact tripleCompleteIntersection_vector_zero_of_generators
          p q r hp hq hr (x 0 0 0)
            (hroots' 0 0 0).1 (hroots' 0 0 0).2.1 (hroots' 0 0 0).2.2)
    exact ⟨z (IsLocalRing.closedPoint L)⟩
  have hrank : finiteSchemeRank (toBase I) = 12 :=
    cubicTwoQuadrics_finite_nonempty_rank_twelve p q r hp hq hr hnonempty
  have hetale : Etale (toBase I) := by
    exact cubic_two_quadric_etale_of_sheared_four_line_root_equations
      p q r hp hq hr hrank (standardBase L) (by simp [standardBase])
        x hxinj (fun i j k => by
          obtain ⟨t, -, ht⟩ := hxform i j k
          exact ⟨t, ht⟩) hroots'
  exact ⟨hfinite, hrank, hetale⟩

end PfaffianDescent
