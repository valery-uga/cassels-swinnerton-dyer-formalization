import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceGridEtale
import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceGridDetection
import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceGridCubicSpan

/-! # The actual grid's cubic evaluation has rank seventeen -/

noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective

namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

def voisinDegreeTenSelectedAvoidance_gridCubicEvaluation
    {L : Type u} [Field L] (x : Fin 27 → Fin 4 → L) :
    homogeneousSubmodule (Fin 4) L 3 →ₗ[L] (Fin 27 → L) where
  toFun s i := MvPolynomial.aeval (x i) s.1
  map_add' s t := by ext i; simp
  map_smul' a s := by ext i; simp

set_option backward.isDefEq.respectTransparency false in
/-- The explicit grid supplies actual distinct normalized points for which
vanishing of a cubic is equivalent to membership in the literal grid ideal. -/
theorem voisinDegreeTenSelectedAvoidance_exists_grid_cubic_detection
    {K L : Type u} [Field K] [CharZero K] [Field L] [Algebra K L] [IsAlgClosed L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [Smooth (hypersurfaceToBase p hp)]
    (hno : ¬ ∃ s : Spec (.of K) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _) :
    ∃ x : Fin 27 → Fin 4 → L,
      Function.Injective x ∧ (∀ i, x i 0 = 1) ∧
      (∀ i, x i ∈ MvPolynomial.zeroLocus L
        (voisinDegreeTenSelectedAvoidance_gridIdeal (p.map (algebraMap K L))
          (hp.map (algebraMap K L))).toIdeal) ∧
      ∀ s : homogeneousSubmodule (Fin 4) L 3,
        voisinDegreeTenSelectedAvoidance_gridCubicEvaluation x s = 0 ↔
          s.1 ∈ (voisinDegreeTenSelectedAvoidance_gridIdeal (p.map (algebraMap K L))
            (hp.map (algebraMap K L))).toIdeal := by
  obtain ⟨x, hxin, hx0, hxzero, hxcover⟩ :=
    voisinDegreeTenSelectedAvoidance_exists_twenty_seven_grid_points (L := L) p hp hno
  let P := p.map (algebraMap K L)
  let hP := hp.map (algebraMap K L)
  let q := voisinDegreeTenSelectedAvoidance_gridCubic L 1
  let r := voisinDegreeTenSelectedAvoidance_gridCubic L 2
  let hq := voisinDegreeTenSelectedAvoidance_gridCubic_homogeneous L 1
  let hr := voisinDegreeTenSelectedAvoidance_gridCubic_homogeneous L 2
  let J := tripleCompleteIntersectionHomogeneousIdeal P q r hP hq hr
  letI : IsFinite (toBase J) :=
    voisinDegreeTenSelectedAvoidance_grid_geometric_finite (L := L) p hp hno
  letI : IsReduced (scheme J) :=
    voisinDegreeTenSelectedAvoidance_grid_geometric_reduced (L := L) p hp hno
  have hnonempty : Nonempty (scheme J) :=
    ⟨projectiveUnitVectorSchemePointAt J (x 0) (hxzero 0) 0 (hx0 0)
      (IsLocalRing.closedPoint L)⟩
  have hlin := tripleCompleteIntersection_linearIndependent_of_finite_of_nonempty
    P q r hP hq hr hnonempty
  have hP0 : P ≠ 0 := by
    simpa only [Matrix.cons_val_zero] using hlin.ne_zero 0
  have hq0 : q ≠ 0 := voisinDegreeTenSelectedAvoidance_gridCubic_one_ne_zero L
  have hrel := tripleCompleteIntersection_isRelPrime_of_finite_of_nonempty_algClosed
    P q r hP hq hr (by decide) hnonempty
  have hregular := third_regular_of_finite_degrees
    P q r hP hq hr (by decide) (by decide) hnonempty
  refine ⟨x, hxin, hx0, hxzero, ?_⟩
  intro s
  constructor
  · intro hs
    apply voisinDegreeTenSelectedAvoidance_mem_triple_of_evaluations_zero x
      s.1 P q r (by decide) s.2 hP hq hr hP0 hq0 hrel hregular hxcover
    intro i
    exact congrFun hs i
  · intro hs
    ext i
    exact hxzero i s.1 hs

set_option backward.isDefEq.respectTransparency false in
/-- The twenty-seven-point cubic evaluation has its actual native ideal
piece as kernel, of dimension three, hence its image has dimension seventeen. -/
theorem voisinDegreeTenSelectedAvoidance_exists_grid_cubic_rank_seventeen
    {K L : Type u} [Field K] [CharZero K] [Field L] [Algebra K L] [IsAlgClosed L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [Smooth (hypersurfaceToBase p hp)]
    (hno : ¬ ∃ s : Spec (.of K) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _) :
    ∃ x : Fin 27 → Fin 4 → L,
      Function.Injective x ∧ (∀ i, x i 0 = 1) ∧
      (∀ i, x i ∈ MvPolynomial.zeroLocus L
        (voisinDegreeTenSelectedAvoidance_gridIdeal (p.map (algebraMap K L))
          (hp.map (algebraMap K L))).toIdeal) ∧
      LinearMap.ker (voisinDegreeTenSelectedAvoidance_gridCubicEvaluation x) =
        homogeneousIdealPiece (voisinDegreeTenSelectedAvoidance_gridIdeal
          (p.map (algebraMap K L)) (hp.map (algebraMap K L))) 3 ∧
      finrank L (LinearMap.range (voisinDegreeTenSelectedAvoidance_gridCubicEvaluation x)) = 17 := by
  obtain ⟨x, hxin, hx0, hxzero, hxdetect⟩ :=
    voisinDegreeTenSelectedAvoidance_exists_grid_cubic_detection (L := L) p hp hno
  let P := p.map (algebraMap K L)
  let hP := hp.map (algebraMap K L)
  let q := voisinDegreeTenSelectedAvoidance_gridCubic L 1
  let r := voisinDegreeTenSelectedAvoidance_gridCubic L 2
  let hq := voisinDegreeTenSelectedAvoidance_gridCubic_homogeneous L 1
  let hr := voisinDegreeTenSelectedAvoidance_gridCubic_homogeneous L 2
  let J := tripleCompleteIntersectionHomogeneousIdeal P q r hP hq hr
  letI : IsFinite (toBase J) :=
    voisinDegreeTenSelectedAvoidance_grid_geometric_finite (L := L) p hp hno
  have hnonempty : Nonempty (scheme J) :=
    ⟨projectiveUnitVectorSchemePointAt J (x 0) (hxzero 0) 0 (hx0 0)
      (IsLocalRing.closedPoint L)⟩
  let Q : Fin 3 → MvPolynomial (Fin 4) L := ![P, q, r]
  have hQ : ∀ i, (Q i).IsHomogeneous 3 := by
    intro i
    fin_cases i
    · exact hP
    · exact hq
    · exact hr
  have hIQ : J.toIdeal = Ideal.span (Set.range Q) := by
    change Ideal.span ({P, q, r} : Set (MvPolynomial (Fin 4) L)) = _
    congr 1
    ext s
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range]
    constructor
    · rintro (rfl | rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp [Q]
  have hlin : LinearIndependent L Q :=
    tripleCompleteIntersection_linearIndependent_of_finite_of_nonempty P q r hP hq hr hnonempty
  have hpiece : finrank L (homogeneousIdealPiece J 3) = 3 :=
    voisinDegreeTenSelectedAvoidance_homogeneous_piece_finrank_three J 3 Q hQ hIQ hlin
  have hker : LinearMap.ker (voisinDegreeTenSelectedAvoidance_gridCubicEvaluation x) =
      homogeneousIdealPiece J 3 := by
    ext s
    exact hxdetect s
  letI : FiniteDimensional L (homogeneousSubmodule (Fin 4) L 3) :=
    (Submodule.fg_iff_finiteDimensional _).mp (homogeneousSubmodule_fg (Fin 4) L 3)
  have hdim := (voisinDegreeTenSelectedAvoidance_gridCubicEvaluation x).finrank_range_add_finrank_ker
  rw [hker, hpiece, four_variable_homogeneous_finrank] at hdim
  refine ⟨x, hxin, hx0, hxzero, hker, ?_⟩
  norm_num [Nat.choose] at hdim
  omega

end PfaffianDescent
