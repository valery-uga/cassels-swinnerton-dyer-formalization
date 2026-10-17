import PfaffianDescent.VoisinFourLineQuadraticCoordinates
import PfaffianDescent.VoisinGenericSmoothSplitWitness

/-!
# Eight quadratic evaluations from the explicit generic split roots

The four-line interpolation calculation replaces the radicality assumption
in the generic twelve-to-eight quadratic evaluation argument.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u

theorem generic_split_exists_eight_surjective_quadratic_evaluations_direct
    (K : Type u) [Field K] [CharZero K]
    {L : Type u} [Field L] [CharZero L] [IsAlgClosed L]
    (φ : FractionRing (CubicTensorCoefficients K) →+* L) :
    ∃ (x : Fin 12 → Fin 4 → L) (κ : Type) (a : κ → Fin 12)
      (inst : Fintype κ),
      Function.Injective a ∧ @Fintype.card κ inst = 8 ∧
      Function.Surjective
        (homogeneousSectionRestriction (K := L)
          (fun (j : Fin 4) (t : κ) => x (a t) j) 2) ∧
      (∀ n, ((genericCubicTensor K).map φ).toMvPolynomial.eval (x n) = 0 ∧
        (X 1 * X 2 : MvPolynomial (Fin 4) L).eval (x n) = 0 ∧
        (X 3 * (X 1 + X 2 + X 3) : MvPolynomial (Fin 4) L).eval (x n) = 0) ∧
      (∀ n, x n ≠ 0) ∧
      (∀ m n, m ≠ n → ∀ c : L, c • x m ≠ x n) := by
  classical
  obtain ⟨x₀, hinj, hcubic, hform, -⟩ :=
    exists_generic_four_line_root_triples K φ
  have hform' : ∀ i j k, ∃ t : L,
      x₀ i j k = t • (Pi.single 0 1 : Fin 4 → L) + lineDirection i j := by
    intro i j k
    obtain ⟨t, ht⟩ := hform i j k
    refine ⟨t, ?_⟩
    rwa [genericFourLineBase_baseChange_eq K φ,
      genericFourLineDirection_baseChange_eq K φ i j] at ht
  let e : Fin 12 ≃ Fin 2 × Fin 2 × Fin 3 :=
    (Fintype.equivFinOfCardEq (by decide :
      Fintype.card (Fin 2 × Fin 2 × Fin 3) = 12)).symm
  let x : Fin 12 → Fin 4 → L :=
    fun n => x₀ (e n).1 (e n).2.1 (e n).2.2
  let q : MvPolynomial (Fin 4) L := X 1 * X 2
  let r : MvPolynomial (Fin 4) L := X 3 * (X 1 + X 2 + X 3)
  let hq : q.IsHomogeneous 2 :=
    (isHomogeneous_X L 1).mul (isHomogeneous_X L 2)
  let hr : r.IsHomogeneous 2 :=
    (isHomogeneous_X L 3).mul
      (((isHomogeneous_X L 1).add (isHomogeneous_X L 2)).add
        (isHomogeneous_X L 3))
  have hqr : LinearIndependent L
      ![(⟨q, hq⟩ : homogeneousSubmodule (Fin 4) L 2), ⟨r, hr⟩] :=
    homogeneous_quadric_pair_linearIndependent_of_polynomials
      q r hq hr standard_split_quadric_pair_linearIndependent
  have hkeriff : ∀ s : homogeneousSubmodule (Fin 4) L 2,
      s ∈ LinearMap.ker
        (homogeneousSectionRestriction (K := L)
          (fun j n => x n j : Fin 4 → Fin 12 → L) 2) ↔
        ∃ a b : L, s.1 = C a * q + C b * r := by
    intro s
    constructor
    · intro hs
      have hzero : ∀ i j k, s.1.eval (x₀ i j k) = 0 := by
        intro i j k
        have hv := congrArg (fun f : Fin 12 → L => f (e.symm (i, j, k)))
          (LinearMap.mem_ker.mp hs)
        simpa [x, homogeneousSectionRestriction_apply,
          twelve_point_product_evaluation_apply] using hv
      obtain ⟨a, b, hab⟩ :=
        generic_fourLine_roots_quadratic_kernel_eq_split_pencil
          K φ x₀ hinj hcubic hform' s.1 s.2 hzero
      exact ⟨a, b, by simpa [q, r, mul_assoc] using hab⟩
    · rintro ⟨a, b, hab⟩
      apply LinearMap.mem_ker.mpr
      apply _root_.funext
      intro n
      obtain ⟨t, ht⟩ := hform' (e n).1 (e n).2.1 (e n).2.2
      have hqr0 := standard_split_quadrics_zero_on_line
        (e n).1 (e n).2.1 t
      have hx : x n = t • (Pi.single 0 1 : Fin 4 → L) +
          lineDirection (e n).1 (e n).2.1 := ht
      simp [homogeneousSectionRestriction_apply,
        twelve_point_product_evaluation_apply, hab, x, hx,
        q, r, hqr0.1, hqr0.2]
  have hker : Module.finrank L (LinearMap.ker
      (homogeneousSectionRestriction (K := L)
        (fun j n => x n j : Fin 4 → Fin 12 → L) 2)) = 2 :=
    twelve_point_homogeneousSectionRestriction_ker_finrank_eq_two_of_kernel_iff
      q r hq hr hqr x hkeriff
  obtain ⟨κ, a, inst, ha, hcard, hsurj, -⟩ :=
    twelve_point_exists_eight_split_restriction_surjective_of_kernel_finrank
      x hker
  have hpoints : ∀ n,
      ((genericCubicTensor K).map φ).toMvPolynomial.eval (x n) = 0 ∧
      (X 1 * X 2 : MvPolynomial (Fin 4) L).eval (x n) = 0 ∧
      (X 3 * (X 1 + X 2 + X 3) : MvPolynomial (Fin 4) L).eval (x n) = 0 := by
    intro n
    obtain ⟨t, ht⟩ := hform' (e n).1 (e n).2.1 (e n).2.2
    have hsplit := standard_split_quadrics_zero_on_line
      (e n).1 (e n).2.1 t
    have hpzero := hcubic (e n).1 (e n).2.1 (e n).2.2
    rw [ht] at hpzero
    have hev := Cubic.eval_toMvPolynomial (RingHom.id L)
      ((genericCubicTensor K).map φ)
      (t • (Pi.single 0 1 : Fin 4 → L) +
        lineDirection (e n).1 (e n).2.1)
    change ((genericCubicTensor K).map φ).toMvPolynomial.eval
      (t • (Pi.single 0 1 : Fin 4 → L) +
        lineDirection (e n).1 (e n).2.1) =
        ((genericCubicTensor K).map φ).eval
          (t • (Pi.single 0 1 : Fin 4 → L) +
            lineDirection (e n).1 (e n).2.1) at hev
    change ((genericCubicTensor K).map φ).toMvPolynomial.eval (x n) = 0 ∧
      q.eval (x n) = 0 ∧ r.eval (x n) = 0
    rw [show x n = t • (Pi.single 0 1 : Fin 4 → L) +
      lineDirection (e n).1 (e n).2.1 from ht]
    exact ⟨hev.trans hpzero, hsplit.1, hsplit.2⟩
  have hnonzero : ∀ n, x n ≠ 0 := by
    intro n
    obtain ⟨t, ht⟩ := hform' (e n).1 (e n).2.1 (e n).2.2
    change x₀ (e n).1 (e n).2.1 (e n).2.2 ≠ 0
    rw [ht]
    exact standardFourLines_genuine (e n).1 (e n).2.1 t
  have hprojective : ∀ m n, m ≠ n → ∀ c : L, c • x m ≠ x n := by
    intro m n hmn c
    have hindex : e m ≠ e n := fun h => hmn (e.injective h)
    exact shearedFourLines_twelve_roots_projectively_distinct
      (Pi.single 0 1 : Fin 4 → L) (by simp) x₀ hinj hform' hindex c
  exact ⟨x, κ, a, inst, ha, hcard, hsurj,
    hpoints, hnonzero, hprojective⟩

/-- A single generic coefficient choice supports a smooth cubic, a finite
étale length-twelve split intersection, and a surjective eight-point
quadratic evaluation map. -/
theorem generic_smooth_split_witness_with_eight_evaluations
    (K : Type u) [Field K] [CharZero K]
    {L : Type u} [Field L] [CharZero L] [IsAlgClosed L]
    (φ : FractionRing (CubicTensorCoefficients K) →+* L) :
    let p := ((genericCubicTensor K).map φ).toMvPolynomial
    let q : MvPolynomial (Fin 4) L := X 1 * X 2
    let r : MvPolynomial (Fin 4) L := X 3 * (X 1 + X 2 + X 3)
    let hp := cubic_toMvPolynomial_isHomogeneous_three ((genericCubicTensor K).map φ)
    let hq := (isHomogeneous_X L 1).mul (isHomogeneous_X L 2)
    let hr := (isHomogeneous_X L 3).mul
      (((isHomogeneous_X L 1).add (isHomogeneous_X L 2)).add
        (isHomogeneous_X L 3))
    let I := tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr
    Smooth (hypersurfaceToBase p hp) ∧
      ∃ hfinite : IsFinite (toBase I),
        letI : IsFinite (toBase I) := hfinite
        finiteSchemeRank (toBase I) = 12 ∧ Etale (toBase I) ∧
          Module.finrank L (grading I 2) = 8 ∧
          ∃ (x : Fin 12 → Fin 4 → L) (κ : Type) (a : κ → Fin 12)
            (inst : Fintype κ),
            Function.Injective a ∧ @Fintype.card κ inst = 8 ∧
            Function.Surjective
              (homogeneousSectionRestriction (K := L)
                (fun (j : Fin 4) (t : κ) => x (a t) j) 2) ∧
            (∀ n, p.eval (x n) = 0 ∧ q.eval (x n) = 0 ∧
              r.eval (x n) = 0) ∧
            (∀ n, x n ≠ 0) ∧
            (∀ m n, m ≠ n → ∀ c : L, c • x m ≠ x n) := by
  dsimp only
  obtain ⟨hsmooth, hfinite, hrank, hetale, hdim⟩ :=
    generic_smooth_split_twelve_point_witness K φ
  obtain ⟨x, κ, a, inst, ha, hcard, hsurj,
    hpoints, hnonzero, hprojective⟩ :=
    generic_split_exists_eight_surjective_quadratic_evaluations_direct K φ
  exact ⟨hsmooth, hfinite, hrank, hetale, hdim,
    x, κ, a, inst, ha, hcard, hsurj,
    hpoints, hnonzero, hprojective⟩

/-- Reindex the selected roots by `Fin 8`, the index type of Voisin's
ordered eight-point configuration. -/
theorem generic_split_exists_finEight_projectively_distinct_quadratic_witness
    (K : Type u) [Field K] [CharZero K]
    {L : Type u} [Field L] [CharZero L] [IsAlgClosed L]
    (φ : FractionRing (CubicTensorCoefficients K) →+* L) :
    ∃ y : Fin 8 → Fin 4 → L,
      Function.Surjective
        (homogeneousSectionRestriction (K := L)
          (fun (j : Fin 4) (i : Fin 8) => y i j) 2) ∧
      (∀ i, ((genericCubicTensor K).map φ).toMvPolynomial.eval (y i) = 0) ∧
      (∀ i, (X 1 * X 2 : MvPolynomial (Fin 4) L).eval (y i) = 0 ∧
        (X 3 * (X 1 + X 2 + X 3) : MvPolynomial (Fin 4) L).eval (y i) = 0) ∧
      (∀ i, y i ≠ 0) ∧
      (∀ i j, i ≠ j → ∀ c : L, c • y i ≠ y j) := by
  obtain ⟨x, κ, a, inst, ha, hcard, hsurj,
    hpoints, hnonzero, hprojective⟩ :=
    generic_split_exists_eight_surjective_quadratic_evaluations_direct K φ
  letI : Fintype κ := inst
  let e : Fin 8 ≃ κ := (Fintype.equivFinOfCardEq hcard).symm
  let y : Fin 8 → Fin 4 → L := fun i => x (a (e i))
  refine ⟨y, ?_, (fun i => (hpoints (a (e i))).1),
    (fun i => (hpoints (a (e i))).2),
    (fun i => hnonzero (a (e i))), ?_⟩
  · intro f
    obtain ⟨s, hs⟩ := hsurj (fun t : κ => f (e.symm t))
    refine ⟨s, ?_⟩
    apply _root_.funext
    intro i
    have hi := congrFun hs (e i)
    simpa [y, homogeneousSectionRestriction_apply,
      finite_product_evaluation_apply] using hi
  · intro i j hij c
    have hindex : a (e i) ≠ a (e j) :=
      fun h => hij (e.injective (ha h))
    exact hprojective (a (e i)) (a (e j)) hindex c

/-- The two split quadrics lie in the actual quadratic evaluation kernel
of the selected eight vectors, and surjectivity makes that kernel a pencil. -/
theorem generic_split_exists_finEight_kernel_pencil_witness
    (K : Type u) [Field K] [CharZero K]
    {L : Type u} [Field L] [CharZero L] [IsAlgClosed L]
    (φ : FractionRing (CubicTensorCoefficients K) →+* L) :
    ∃ y : Fin 8 → Fin 4 → L,
      let x : Fin 4 → Fin 8 → L := fun j i => y i j
      Function.Surjective (homogeneousSectionRestriction (K := L) x 2) ∧
      (⟨(X 1 * X 2 : MvPolynomial (Fin 4) L),
        (isHomogeneous_X L 1).mul (isHomogeneous_X L 2)⟩ :
        homogeneousSubmodule (Fin 4) L 2) ∈
          LinearMap.ker (homogeneousSectionRestriction (K := L) x 2) ∧
      (⟨(X 3 * (X 1 + X 2 + X 3) : MvPolynomial (Fin 4) L),
        (isHomogeneous_X L 3).mul
          (((isHomogeneous_X L 1).add (isHomogeneous_X L 2)).add
            (isHomogeneous_X L 3))⟩ :
        homogeneousSubmodule (Fin 4) L 2) ∈
          LinearMap.ker (homogeneousSectionRestriction (K := L) x 2) ∧
      Module.finrank L (LinearMap.ker
        (homogeneousSectionRestriction (K := L) x 2)) = 2 := by
  obtain ⟨y, hsurj, -, hquadrics, -, -⟩ :=
    generic_split_exists_finEight_projectively_distinct_quadratic_witness K φ
  let x : Fin 4 → Fin 8 → L := fun j i => y i j
  refine ⟨y, hsurj, ?_, ?_, ?_⟩
  · apply LinearMap.mem_ker.mpr
    apply _root_.funext
    intro i
    simpa [x, homogeneousSectionRestriction_apply,
      finite_product_evaluation_apply] using (hquadrics i).1
  · apply LinearMap.mem_ker.mpr
    apply _root_.funext
    intro i
    simpa [x, homogeneousSectionRestriction_apply,
      finite_product_evaluation_apply] using (hquadrics i).2
  · exact quadric_degree_eight_vanishing_sections_finrank_eq_two_of_surjective
      x (by simp) hsurj

/-- On any eight vector points imposing independent quadratic conditions,
two linearly independent vanishing quadrics span the entire quadratic
evaluation kernel. -/
theorem quadrics_span_eight_evaluation_kernel
    {L : Type u} [Field L]
    (y : Fin 8 → Fin 4 → L)
    (q r : MvPolynomial (Fin 4) L)
    (hq : q.IsHomogeneous 2) (hr : r.IsHomogeneous 2)
    (hlin : LinearIndependent L
      ![(⟨q, hq⟩ : homogeneousSubmodule (Fin 4) L 2), ⟨r, hr⟩])
    (hsurj : Function.Surjective (homogeneousSectionRestriction (K := L)
      (fun j i => y i j : Fin 4 → Fin 8 → L) 2))
    (hquad : ∀ i, q.eval (y i) = 0 ∧ r.eval (y i) = 0) :
    let Q : Fin 2 → homogeneousSubmodule (Fin 4) L 2 :=
      ![(⟨q, hq⟩), (⟨r, hr⟩)]
    LinearMap.ker (homogeneousSectionRestriction (K := L)
      (fun j i => y i j : Fin 4 → Fin 8 → L) 2) =
        Submodule.span L (Set.range Q) := by
  dsimp only
  let x : Fin 4 → Fin 8 → L := fun j i => y i j
  let Q : Fin 2 → homogeneousSubmodule (Fin 4) L 2 :=
    ![(⟨q, hq⟩), (⟨r, hr⟩)]
  have hkerdim : Module.finrank L (LinearMap.ker
      (homogeneousSectionRestriction (K := L) x 2)) = 2 :=
    quadric_degree_eight_vanishing_sections_finrank_eq_two_of_surjective
      x (by simp) hsurj
  have hspandim : Module.finrank L (Submodule.span L (Set.range Q)) = 2 := by
    rw [finrank_span_eq_card hlin]
    norm_num
  have hle : Submodule.span L (Set.range Q) ≤
      LinearMap.ker (homogeneousSectionRestriction (K := L) x 2) := by
    apply Submodule.span_le.mpr
    rintro s ⟨i, rfl⟩
    fin_cases i
    · apply LinearMap.mem_ker.mpr
      apply _root_.funext
      intro j
      simpa [Q, x, homogeneousSectionRestriction_apply,
        finite_product_evaluation_apply] using (hquad j).1
    · apply LinearMap.mem_ker.mpr
      apply _root_.funext
      intro j
      simpa [Q, x, homogeneousSectionRestriction_apply,
        finite_product_evaluation_apply] using (hquad j).2
  symm
  exact Submodule.eq_of_le_of_finrank_eq hle (by rw [hspandim, hkerdim])

/-- The preceding kernel theorem for the standard split pair. -/
theorem split_quadrics_span_eight_evaluation_kernel
    {L : Type u} [Field L]
    (y : Fin 8 → Fin 4 → L)
    (hsurj : Function.Surjective (homogeneousSectionRestriction (K := L)
      (fun j i => y i j : Fin 4 → Fin 8 → L) 2))
    (hquad : ∀ i,
      (X 1 * X 2 : MvPolynomial (Fin 4) L).eval (y i) = 0 ∧
      (X 3 * (X 1 + X 2 + X 3) : MvPolynomial (Fin 4) L).eval (y i) = 0) :
    let Q : Fin 2 → homogeneousSubmodule (Fin 4) L 2 :=
      ![(⟨(X 1 * X 2 : MvPolynomial (Fin 4) L),
        (isHomogeneous_X L 1).mul (isHomogeneous_X L 2)⟩),
        (⟨(X 3 * (X 1 + X 2 + X 3) : MvPolynomial (Fin 4) L),
          (isHomogeneous_X L 3).mul
            (((isHomogeneous_X L 1).add (isHomogeneous_X L 2)).add
              (isHomogeneous_X L 3))⟩)]
    LinearMap.ker (homogeneousSectionRestriction (K := L)
      (fun j i => y i j : Fin 4 → Fin 8 → L) 2) =
        Submodule.span L (Set.range Q) := by
  dsimp only
  let x : Fin 4 → Fin 8 → L := fun j i => y i j
  let q : MvPolynomial (Fin 4) L := X 1 * X 2
  let r : MvPolynomial (Fin 4) L := X 3 * (X 1 + X 2 + X 3)
  let hq : q.IsHomogeneous 2 :=
    (isHomogeneous_X L 1).mul (isHomogeneous_X L 2)
  let hr : r.IsHomogeneous 2 :=
    (isHomogeneous_X L 3).mul
      (((isHomogeneous_X L 1).add (isHomogeneous_X L 2)).add
        (isHomogeneous_X L 3))
  let Q : Fin 2 → homogeneousSubmodule (Fin 4) L 2 :=
    ![(⟨q, hq⟩), (⟨r, hr⟩)]
  have hlin : LinearIndependent L Q :=
    homogeneous_quadric_pair_linearIndependent_of_polynomials
      q r hq hr standard_split_quadric_pair_linearIndependent
  have hkerdim : Module.finrank L (LinearMap.ker
      (homogeneousSectionRestriction (K := L) x 2)) = 2 :=
    quadric_degree_eight_vanishing_sections_finrank_eq_two_of_surjective
      x (by simp) hsurj
  have hspandim : Module.finrank L (Submodule.span L (Set.range Q)) = 2 := by
    rw [finrank_span_eq_card hlin]
    norm_num
  have hle : Submodule.span L (Set.range Q) ≤
      LinearMap.ker (homogeneousSectionRestriction (K := L) x 2) := by
    apply Submodule.span_le.mpr
    rintro s ⟨i, rfl⟩
    fin_cases i
    · apply LinearMap.mem_ker.mpr
      apply _root_.funext
      intro j
      convert (hquad j).1 using 1 <;>
        simp [Q, q, x, homogeneousSectionRestriction_apply,
          finite_product_evaluation_apply]
    · apply LinearMap.mem_ker.mpr
      apply _root_.funext
      intro j
      convert (hquad j).2 using 1 <;>
        simp [Q, r, x, homogeneousSectionRestriction_apply,
          finite_product_evaluation_apply]
  symm
  exact Submodule.eq_of_le_of_finrank_eq hle (by rw [hspandim, hkerdim])

end PfaffianDescent
