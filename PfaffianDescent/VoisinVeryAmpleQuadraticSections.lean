import PfaffianDescent.CubicSurfacePointEvaluation
import PfaffianDescent.VoisinBaseLocusNumerics

/-!
# Two-point separation by quadratic sections

The disjoint fixed-component branch of Voisin's Lemma `leeffective` uses
that a nonzero curve imposes at least two conditions on a very ample system.
For the required cubic-surface application the system is `O(2)`.  This file
proves the corresponding concrete statement: two distinct projective
directions impose two independent conditions on homogeneous quadrics, both
in the polynomial space and in the quadratic graded piece of a cubic
surface.
-/

namespace PfaffianDescent

open MvPolynomial Module
open AllCharacteristics.HomogeneousProjective

universe u

variable {K : Type u} [Field K]

/-- A linear functional on affine four-space, written as its homogeneous
linear polynomial in the coordinate variables. -/
noncomputable def dualHomogeneousLinearForm
    (φ : (Fin 4 → K) →ₗ[K] K) : MvPolynomial (Fin 4) K :=
  homogeneousLinearForm (fun i => φ (Pi.single i 1))

/-- Evaluation of the polynomial attached to a dual vector is evaluation of
the original linear functional. -/
theorem dualHomogeneousLinearForm_eval
    (φ : (Fin 4 → K) →ₗ[K] K) (x : Fin 4 → K) :
    MvPolynomial.aeval x (dualHomogeneousLinearForm φ) = φ x := by
  classical
  rw [dualHomogeneousLinearForm, homogeneousLinearForm_eval]
  have hx : x = ∑ i, x i • Pi.single i (1 : K) := by
    calc
      x = ∑ i, Pi.single i (x i) := (Finset.univ_sum_single x).symm
      _ = ∑ i, x i • Pi.single i (1 : K) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [← Pi.single_smul]
        simp
  calc
    ∑ i, φ (Pi.single i 1) * x i =
        ∑ i, φ (x i • Pi.single i (1 : K)) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [map_smul, smul_eq_mul]
          exact mul_comm _ _
    _ = φ (∑ i, x i • Pi.single i (1 : K)) := by rw [map_sum]
    _ = φ x := by rw [← hx]

/-- The polynomial attached to a dual vector is homogeneous of degree one. -/
theorem dualHomogeneousLinearForm_isHomogeneous
    (φ : (Fin 4 → K) →ₗ[K] K) :
    (dualHomogeneousLinearForm φ).IsHomogeneous 1 :=
  homogeneousLinearForm_isHomogeneous _

/-- Evaluation of homogeneous quadrics at an ordered pair of affine-cone
representatives. -/
noncomputable def homogeneousQuadraticPairEvaluation
    (x y : Fin 4 → K) :
    homogeneousSubmodule (Fin 4) K 2 →ₗ[K] (Fin 2 → K) where
  toFun q i := MvPolynomial.aeval (![x, y] i) q.1
  map_add' q r := by
    ext i
    simp
  map_smul' a q := by
    ext i
    simp

/-- Two linearly independent affine-cone directions impose independent
conditions on homogeneous quadrics. -/
theorem homogeneousQuadraticPairEvaluation_surjective
    (x y : Fin 4 → K) (hli : LinearIndependent K ![x, y]) :
    Function.Surjective (homogeneousQuadraticPairEvaluation x y) := by
  let v : Fin 2 → (Fin 4 → K) := ![x, y]
  let c : (Fin 2 → K) →ₗ[K] (Fin 4 → K) :=
    Fintype.linearCombination K v
  have hc : Function.Injective c := by
    exact hli.fintypeLinearCombination_injective
  let g : (Fin 4 → K) →ₗ[K] (Fin 2 → K) :=
    c.leftInverse
  have hgc (z : Fin 2 → K) : g (c z) = z := by
    exact c.leftInverse_apply_of_inj (LinearMap.ker_eq_bot.mpr hc) z
  let φ : Fin 2 → ((Fin 4 → K) →ₗ[K] K) := fun i =>
    (LinearMap.proj i).comp g
  have hφ (i j : Fin 2) : φ i (v j) = if i = j then 1 else 0 := by
    have hcj : c (Pi.single j 1) = v j := by
      change Fintype.linearCombination K v (Pi.single j 1) = v j
      rw [Fintype.linearCombination_apply_single]
      simp
    rw [← hcj]
    change g (c (Pi.single j 1)) i = _
    rw [hgc]
    by_cases hij : i = j
    · subst j
      simp
    · have hji : j ≠ i := Ne.symm hij
      simp [hij]
  let ell : Fin 2 → MvPolynomial (Fin 4) K := fun i =>
    dualHomogeneousLinearForm (φ i)
  have hellhom (i : Fin 2) : (ell i).IsHomogeneous 1 :=
    dualHomogeneousLinearForm_isHomogeneous (φ i)
  have hell (i j : Fin 2) : MvPolynomial.aeval (v j) (ell i) =
      if i = j then 1 else 0 := by
    change MvPolynomial.aeval (v j) (dualHomogeneousLinearForm (φ i)) = _
    rw [dualHomogeneousLinearForm_eval, hφ]
  intro z
  let q0 : homogeneousSubmodule (Fin 4) K 2 :=
    ⟨(ell 0) ^ 2, by simpa using (hellhom 0).pow 2⟩
  let q1 : homogeneousSubmodule (Fin 4) K 2 :=
    ⟨(ell 1) ^ 2, by simpa using (hellhom 1).pow 2⟩
  refine ⟨z 0 • q0 + z 1 • q1, ?_⟩
  ext i
  fin_cases i
  · have h00 : MvPolynomial.aeval x (ell 0) = 1 := by
      simpa [v] using hell 0 0
    have h10 : MvPolynomial.aeval x (ell 1) = 0 := by
      simpa [v] using hell 1 0
    change MvPolynomial.aeval x
      ((z 0 • q0 + z 1 • q1 : homogeneousSubmodule (Fin 4) K 2).1) = z 0
    simp only [Submodule.coe_add, Submodule.coe_smul, map_add, map_smul,
      q0, q1, map_pow, h00, h10]
    simp
  · have h01 : MvPolynomial.aeval y (ell 0) = 0 := by
      simpa [v] using hell 0 1
    have h11 : MvPolynomial.aeval y (ell 1) = 1 := by
      simpa [v] using hell 1 1
    change MvPolynomial.aeval y
      ((z 0 • q0 + z 1 • q1 : homogeneousSubmodule (Fin 4) K 2).1) = z 1
    simp only [Submodule.coe_add, Submodule.coe_smul, map_add, map_smul,
      q0, q1, map_pow, h01, h11]
    simp

/-- Projectively distinct nonzero vectors impose independent conditions on
homogeneous quadrics. -/
theorem homogeneousQuadraticPairEvaluation_surjective_of_directions
    (x y : Fin 4 → K) (hx : x ≠ 0)
    (hxy : ∀ a : K, a • x ≠ y) :
    Function.Surjective (homogeneousQuadraticPairEvaluation x y) := by
  apply homogeneousQuadraticPairEvaluation_surjective x y
  exact (LinearIndependent.pair_iff' hx).mpr hxy

/-- The quadrics vanishing at two distinct projective directions form an
eight-dimensional subspace of the ten-dimensional quadratic system. -/
theorem homogeneousQuadraticPairEvaluation_ker_finrank
    (x y : Fin 4 → K) (hli : LinearIndependent K ![x, y]) :
    finrank K (LinearMap.ker (homogeneousQuadraticPairEvaluation x y)) = 8 := by
  let e := homogeneousQuadraticPairEvaluation x y
  have hsurj : Function.Surjective e :=
    homogeneousQuadraticPairEvaluation_surjective x y hli
  have hrange : LinearMap.range e = ⊤ := LinearMap.range_eq_top.mpr hsurj
  have hdim := e.finrank_range_add_finrank_ker
  dsimp only [e] at hdim
  rw [hrange, finrank_top, Module.finrank_pi_fintype,
    Module.finrank_self] at hdim
  have hquad : finrank K (homogeneousSubmodule (Fin 4) K 2) = 10 := by
    rw [four_variable_homogeneous_finrank]
    decide
  rw [hquad] at hdim
  norm_num at hdim
  omega

/-- Any quadratic subsystem whose members vanish at two distinct projective
directions has dimension at most eight.  This is the concrete very-ampleness
bound used in the disjoint fixed-curve branch of `leeffective`. -/
theorem homogeneousQuadraticSubmodule_finrank_le_eight_of_vanishes_pair
    (x y : Fin 4 → K) (hli : LinearIndependent K ![x, y])
    (W : Submodule K (homogeneousSubmodule (Fin 4) K 2))
    (hW : W ≤ LinearMap.ker (homogeneousQuadraticPairEvaluation x y)) :
    finrank K W ≤ 8 := by
  rw [← homogeneousQuadraticPairEvaluation_ker_finrank x y hli]
  exact Submodule.finrank_mono hW

/-- A polynomial submodule consisting of homogeneous quadrics and vanishing
at two distinct projective directions has dimension at most eight.  This
form is convenient for a moving divisor system after it has been lifted from
the cubic surface's coordinate ring to homogeneous polynomials. -/
theorem homogeneousQuadraticPolynomialSubmodule_finrank_le_eight_of_pointwise_vanishing
    (p : MvPolynomial (Fin 4) K)
    (x y : cubicSurfaceAffinePoints p)
    (hdir : ∀ a : K, y.1 ≠ a • x.1)
    (W : Submodule K (MvPolynomial (Fin 4) K))
    (hhom : ∀ q ∈ W, q.IsHomogeneous 2)
    (hvan : ∀ q : W,
      MvPolynomial.aeval x.1 q.1 = 0 ∧
      MvPolynomial.aeval y.1 q.1 = 0) :
    finrank K W ≤ 8 := by
  let lift : W →ₗ[K] homogeneousSubmodule (Fin 4) K 2 :=
    { toFun := fun q => ⟨q.1, hhom q.1 q.2⟩
      map_add' := by intro q r; ext <;> rfl
      map_smul' := by intro a q; ext <;> rfl }
  have hlift : Function.Injective lift := by
    intro q r hqr
    apply Subtype.ext
    have hqr' := congrArg
      (fun z : homogeneousSubmodule (Fin 4) K 2 => z.1) hqr
    change q.1 = r.1 at hqr'
    exact hqr'
  let W' : Submodule K (homogeneousSubmodule (Fin 4) K 2) :=
    LinearMap.range lift
  have hW' : W' ≤ LinearMap.ker
      (homogeneousQuadraticPairEvaluation x.1 y.1) := by
    intro q hq
    obtain ⟨w, rfl⟩ := hq
    apply LinearMap.mem_ker.mpr
    ext i
    fin_cases i
    · exact (hvan w).1
    · exact (hvan w).2
  have hli : LinearIndependent K ![x.1, y.1] :=
    (LinearIndependent.pair_iff' x.2.2).mpr (fun a => (hdir a).symm)
  have hbound : finrank K W' ≤ 8 :=
    homogeneousQuadraticSubmodule_finrank_le_eight_of_vanishes_pair
      x.1 y.1 hli W' hW'
  rw [LinearMap.finrank_range_of_inj hlift] at hbound
  exact hbound

section CubicSurface

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Evaluation of quadratic coordinate-ring sections on a cubic surface at
an ordered pair of affine-cone points. -/
noncomputable def cubicSurfaceQuadraticPairEvaluation
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (x y : cubicSurfaceAffinePoints p) :
    grading (equationIdeal p hp) 2 →ₗ[K] (Fin 2 → K) where
  toFun q i := cubicSurfaceCoordinatePointEvaluation p hp q (![x, y] i)
  map_add' q r := by
    ext i
    simp [cubicSurfaceCoordinatePointEvaluation]
  map_smul' a q := by
    ext i
    simp [cubicSurfaceCoordinatePointEvaluation]

/-- Evaluation of quadratic coordinate-ring sections at one affine-cone
point of the cubic surface. -/
noncomputable def cubicSurfaceQuadraticEvaluationAt
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (x : cubicSurfaceAffinePoints p) :
    grading (equationIdeal p hp) 2 →ₗ[K] K :=
  (cubicSurfacePointCoordinateRingEvaluation p hp x).comp
    (grading (equationIdeal p hp) 2).subtype

/-- Evaluation at a projective point is a nonzero functional on quadratic
sections.  A square of a coordinate nonzero at the chosen cone
representative is an explicit witness. -/
theorem cubicSurfaceQuadraticEvaluationAt_ne_zero
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (x : cubicSurfaceAffinePoints p) :
    cubicSurfaceQuadraticEvaluationAt p hp x ≠ 0 := by
  obtain ⟨i, hi⟩ : ∃ i, x.1 i ≠ 0 := by
    by_contra h
    push Not at h
    apply x.2.2
    funext i
    exact h i
  let Q : homogeneousSubmodule (Fin 4) K 2 :=
    ⟨MvPolynomial.X i ^ 2, MvPolynomial.isHomogeneous_X_pow i 2⟩
  let q := cubicSurfaceHomogeneousCoordinateProjection p hp 2 Q
  intro hzero
  have hq := LinearMap.congr_fun hzero q
  change MvPolynomial.aeval x.1 (MvPolynomial.X i ^ 2) = 0 at hq
  simp only [map_pow, aeval_X] at hq
  exact pow_ne_zero 2 hi hq

/-- Distinct projective directions on a cubic surface impose two independent
conditions on its actual quadratic coordinate-ring sections. -/
theorem cubicSurfaceQuadraticPairEvaluation_surjective
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (x y : cubicSurfaceAffinePoints p)
    (hli : LinearIndependent K ![x.1, y.1]) :
    Function.Surjective (cubicSurfaceQuadraticPairEvaluation p hp x y) := by
  intro z
  obtain ⟨q, hq⟩ :=
    homogeneousQuadraticPairEvaluation_surjective x.1 y.1 hli z
  refine ⟨cubicSurfaceHomogeneousCoordinateProjection p hp 2 q, ?_⟩
  ext i
  change MvPolynomial.aeval (![x, y] i).1 q.1 = z i
  have hqi := congrFun hq i
  change MvPolynomial.aeval (![x.1, y.1] i) q.1 = z i at hqi
  fin_cases i <;> exact hqi

set_option linter.style.haveILetI false in
/-- The common kernel of evaluation at two distinct projective points of a
cubic surface has dimension eight. -/
theorem cubicSurfaceQuadraticPairEvaluation_ker_finrank
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (x y : cubicSurfaceAffinePoints p)
    (hli : LinearIndependent K ![x.1, y.1]) :
    finrank K (LinearMap.ker
      (cubicSurfaceQuadraticPairEvaluation p hp x y)) = 8 := by
  letI : Module.Finite K (grading (equationIdeal p hp) 2) :=
    Module.Finite.of_surjective
      (cubicSurfaceHomogeneousCoordinateProjection p hp 2)
      (cubicSurfaceHomogeneousCoordinateProjection_surjective p hp 2)
  let e := cubicSurfaceQuadraticPairEvaluation p hp x y
  have hsurj : Function.Surjective e :=
    cubicSurfaceQuadraticPairEvaluation_surjective p hp x y hli
  have hrange : LinearMap.range e = ⊤ := LinearMap.range_eq_top.mpr hsurj
  have hdim := e.finrank_range_add_finrank_ker
  dsimp only [e] at hdim
  rw [hrange, finrank_top, Module.finrank_pi_fintype,
    Module.finrank_self, cubicSurface_grade_two_finrank p hp hne] at hdim
  norm_num at hdim
  omega

set_option linter.style.haveILetI false in
/-- Every subsystem of quadratic sections on a cubic surface vanishing at
two distinct projective points has dimension at most eight. -/
theorem cubicSurfaceQuadraticSubmodule_finrank_le_eight_of_vanishes_pair
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (x y : cubicSurfaceAffinePoints p)
    (hli : LinearIndependent K ![x.1, y.1])
    (W : Submodule K (grading (equationIdeal p hp) 2))
    (hW : W ≤ LinearMap.ker
      (cubicSurfaceQuadraticPairEvaluation p hp x y)) :
    finrank K W ≤ 8 := by
  letI : Module.Finite K (grading (equationIdeal p hp) 2) :=
    Module.Finite.of_surjective
      (cubicSurfaceHomogeneousCoordinateProjection p hp 2)
      (cubicSurfaceHomogeneousCoordinateProjection_surjective p hp 2)
  rw [← cubicSurfaceQuadraticPairEvaluation_ker_finrank p hp hne x y hli]
  exact Submodule.finrank_mono hW

set_option linter.style.haveILetI false in
/-- Pointwise formulation of the same dimension bound.  It accepts exactly
the condition obtained when every member of a quadratic subsystem vanishes
along a curve containing the two marked projective points. -/
theorem cubicSurfaceQuadraticSubmodule_finrank_le_eight_of_pointwise_vanishing
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (x y : cubicSurfaceAffinePoints p)
    (hdir : ∀ a : K, y.1 ≠ a • x.1)
    (W : Submodule K (grading (equationIdeal p hp) 2))
    (hvan : ∀ q : W,
      cubicSurfaceCoordinatePointEvaluation p hp q.1 x = 0 ∧
      cubicSurfaceCoordinatePointEvaluation p hp q.1 y = 0) :
    finrank K W ≤ 8 := by
  letI : Module.Finite K (grading (equationIdeal p hp) 2) :=
    Module.Finite.of_surjective
      (cubicSurfaceHomogeneousCoordinateProjection p hp 2)
      (cubicSurfaceHomogeneousCoordinateProjection_surjective p hp 2)
  have hli : LinearIndependent K ![x.1, y.1] :=
    (LinearIndependent.pair_iff' x.2.2).mpr (fun a => (hdir a).symm)
  apply cubicSurfaceQuadraticSubmodule_finrank_le_eight_of_vanishes_pair
    p hp hne x y hli W
  intro q hq
  apply LinearMap.mem_ker.mpr
  ext i
  fin_cases i
  · exact (hvan ⟨q, hq⟩).1
  · exact (hvan ⟨q, hq⟩).2

set_option linter.style.haveILetI false in
/-- Consequently, a quadratic subsystem of dimension at least nine cannot
vanish along a curve containing two distinct projective points.  This is the
very-ampleness contradiction in the disjoint fixed-component branch of the
degree-eight `leeffective` argument, after choosing two points on the fixed
curve. -/
theorem cubicSurface_not_nine_le_finrank_quadraticSubmodule_of_pointwise_vanishing
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (x y : cubicSurfaceAffinePoints p)
    (hdir : ∀ a : K, y.1 ≠ a • x.1)
    (W : Submodule K (grading (equationIdeal p hp) 2))
    (hvan : ∀ q : W,
      cubicSurfaceCoordinatePointEvaluation p hp q.1 x = 0 ∧
      cubicSurfaceCoordinatePointEvaluation p hp q.1 y = 0)
    (hnine : 9 ≤ finrank K W) : False := by
  have height :=
    cubicSurfaceQuadraticSubmodule_finrank_le_eight_of_pointwise_vanishing
      p hp hne x y hdir W hvan
  omega

/-! ## Fixed-component endpoints for the degree-eight generic system -/

set_option linter.style.haveILetI false in
/-- In the branch where the fixed component contains the generic
length-eight subscheme, surjective evaluation and one nonzero vanishing
section force at least nine fixed-part sections.  A moving pencil then
contradicts the proper fixed-plus-moving family bound in the ten-dimensional
quadratic system. -/
theorem cubicSurface_degreeEight_fixedComponent_meets_contradiction
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (fixed moving : Submodule K (grading (equationIdeal p hp) 2))
    (ev : fixed →ₗ[K] (Fin 8 → K))
    (heval : Function.Surjective ev)
    (hsection : ∃ q : fixed, q ≠ 0 ∧ ev q = 0)
    (hpencil : 2 ≤ finrank K moving)
    (hproper : finrank K fixed + finrank K moving ≤
      finrank K (grading (equationIdeal p hp) 2)) : False := by
  letI : Module.Finite K (grading (equationIdeal p hp) 2) :=
    Module.Finite.of_surjective
      (cubicSurfaceHomogeneousCoordinateProjection p hp 2)
      (cubicSurfaceHomogeneousCoordinateProjection_surjective p hp 2)
  have hgeneric : 9 ≤ finrank K fixed := by
    simpa using
      succ_le_finrank_of_surjective_evaluation_with_nonzero_kernel
        (K := K) (V := fixed) 8 ev heval hsection
  exact voisin_degreeEight_fixedComponent_meets_numerical_contradiction
    p hp hne (finrank K fixed) (finrank K moving)
      hgeneric hpencil hproper

set_option linter.style.haveILetI false in
/-- Geometric-subspace form of the meeting branch.  The fixed and moving
images meet in at most a line, and their span is a proper subsystem of the
quadratic system.  These two facts imply the dimension bound used by the
numerical contradiction, so it need not be supplied separately. -/
theorem
    cubicSurface_degreeEight_fixedComponent_meets_contradiction_of_overlap_and_properSpan
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (fixed moving : Submodule K (grading (equationIdeal p hp) 2))
    (ev : fixed →ₗ[K] (Fin 8 → K))
    (heval : Function.Surjective ev)
    (hsection : ∃ q : fixed, q ≠ 0 ∧ ev q = 0)
    (hpencil : 2 ≤ finrank K moving)
    (hoverlap : finrank K ↥(fixed ⊓ moving) ≤ 1)
    (hproperSpan : fixed ⊔ moving ≠ ⊤) : False := by
  letI : Module.Finite K (grading (equationIdeal p hp) 2) :=
    Module.Finite.of_surjective
      (cubicSurfaceHomogeneousCoordinateProjection p hp 2)
      (cubicSurfaceHomogeneousCoordinateProjection_surjective p hp 2)
  apply cubicSurface_degreeEight_fixedComponent_meets_contradiction
    p hp hne fixed moving ev heval hsection hpencil
  exact finrank_add_le_finrank_of_inf_finrank_le_one_of_sup_ne_top
    fixed moving hoverlap hproperSpan

set_option linter.style.haveILetI false in
/-- Evaluation form of the same fixed/moving contradiction.  A nonzero
common section supplies the overlap, while containment in the kernel of one
nonzero linear functional proves that the combined subsystem is proper.
This is the linear-algebraic content of choosing a common base point of the
fixed and moving divisors. -/
theorem
    cubicSurface_degreeEight_fixedComponent_meets_contradiction_of_commonSection_and_vanishing
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (fixed moving : Submodule K (grading (equationIdeal p hp) 2))
    (ev : fixed →ₗ[K] (Fin 8 → K))
    (heval : Function.Surjective ev)
    (hsection : ∃ q : fixed, q ≠ 0 ∧ ev q = 0)
    (hpencil : 2 ≤ finrank K moving)
    (q : grading (equationIdeal p hp) 2)
    (hq0 : q ≠ 0)
    (hintersection : fixed ⊓ moving = Submodule.span K {q})
    (atBasePoint : grading (equationIdeal p hp) 2 →ₗ[K] K)
    (hatBasePoint : atBasePoint ≠ 0)
    (hfixedVanishes : fixed ≤ LinearMap.ker atBasePoint)
    (hmovingVanishes : moving ≤ LinearMap.ker atBasePoint) : False := by
  letI : Module.Finite K (grading (equationIdeal p hp) 2) :=
    Module.Finite.of_surjective
      (cubicSurfaceHomogeneousCoordinateProjection p hp 2)
      (cubicSurfaceHomogeneousCoordinateProjection_surjective p hp 2)
  apply
    cubicSurface_degreeEight_fixedComponent_meets_contradiction_of_overlap_and_properSpan
      p hp hne fixed moving ev heval hsection hpencil
  · rw [hintersection]
    rw [finrank_span_singleton hq0]
  · intro htop
    have hle : fixed ⊔ moving ≤ LinearMap.ker atBasePoint :=
      sup_le hfixedVanishes hmovingVanishes
    have hker : LinearMap.ker atBasePoint = ⊤ := by
      apply top_unique
      rw [← htop]
      exact hle
    exact hatBasePoint (LinearMap.ker_eq_top.mp hker)

set_option linter.style.haveILetI false in
/-- Pointwise form of the meeting-branch contradiction.  If the two image
systems intersect in their common product line and every section in both
systems vanishes at one cubic-surface point, point evaluation itself proves
that their span is proper. -/
theorem
    cubicSurface_degreeEight_fixedComponent_meets_contradiction_of_commonSection_and_basePoint
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (fixed moving : Submodule K (grading (equationIdeal p hp) 2))
    (ev : fixed →ₗ[K] (Fin 8 → K))
    (heval : Function.Surjective ev)
    (hsection : ∃ q : fixed, q ≠ 0 ∧ ev q = 0)
    (hpencil : 2 ≤ finrank K moving)
    (q : grading (equationIdeal p hp) 2) (hq0 : q ≠ 0)
    (hintersection : fixed ⊓ moving = Submodule.span K {q})
    (x : cubicSurfaceAffinePoints p)
    (hfixedVanishes : ∀ r : fixed,
      cubicSurfacePointCoordinateRingEvaluation p hp x r.1 = 0)
    (hmovingVanishes : ∀ r : moving,
      cubicSurfacePointCoordinateRingEvaluation p hp x r.1 = 0) : False := by
  apply
    cubicSurface_degreeEight_fixedComponent_meets_contradiction_of_commonSection_and_vanishing
      p hp hne fixed moving ev heval hsection hpencil q hq0 hintersection
      (cubicSurfaceQuadraticEvaluationAt p hp x)
      (cubicSurfaceQuadraticEvaluationAt_ne_zero p hp x)
  · intro r hr
    apply LinearMap.mem_ker.mpr
    exact hfixedVanishes ⟨r, hr⟩
  · intro r hr
    apply LinearMap.mem_ker.mpr
    exact hmovingVanishes ⟨r, hr⟩

set_option linter.style.haveILetI false in
/-- Multiplication-map form of the meeting-branch contradiction.  The two
maps model multiplication
`H⁰(O(C)) → H⁰(O(H))` and `H⁰(O(H-C)) → H⁰(O(H))` by fixed defining
sections of the complementary divisors.  Cancellation identifies their
intersection with the common product line, so that equality of image
subspaces no longer has to be supplied as a separate geometric premise. -/
theorem
    cubicSurface_degreeEight_fixedComponent_meets_contradiction_of_productMaps
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    {A B : Type u} [AddCommGroup A] [Module K A]
    [AddCommGroup B] [Module K B] [FiniteDimensional K B]
    (fixedMap : A →ₗ[K] grading (equationIdeal p hp) 2)
    (movingMap : B →ₗ[K] grading (equationIdeal p hp) 2)
    (a₀ : A) (b₀ : B)
    (ev : LinearMap.range fixedMap →ₗ[K] (Fin 8 → K))
    (heval : Function.Surjective ev)
    (hsection : ∃ q : LinearMap.range fixedMap,
      q ≠ 0 ∧ ev q = 0)
    (htwo : 2 ≤ finrank K B)
    (hmovingInjective : Function.Injective movingMap)
    (hq0 : fixedMap a₀ ≠ 0)
    (hcommon : fixedMap a₀ = movingMap b₀)
    (hcross : ∀ a b, fixedMap a = movingMap b →
      ∃ c : K, a = c • a₀ ∧ b = c • b₀)
    (x : cubicSurfaceAffinePoints p)
    (hfixedVanishes : ∀ a,
      cubicSurfacePointCoordinateRingEvaluation p hp x (fixedMap a) = 0)
    (hmovingVanishes : ∀ b,
      cubicSurfacePointCoordinateRingEvaluation p hp x (movingMap b) = 0) :
    False := by
  apply
    cubicSurface_degreeEight_fixedComponent_meets_contradiction_of_commonSection_and_basePoint
      p hp hne (LinearMap.range fixedMap) (LinearMap.range movingMap)
      ev heval hsection
      (by simpa [LinearMap.finrank_range_of_inj hmovingInjective] using htwo)
      (fixedMap a₀) hq0
      (range_inf_range_eq_span_of_common_line
        fixedMap movingMap a₀ b₀ hcommon hcross)
      x
  · intro r
    obtain ⟨a, ha⟩ := r.2
    rw [← ha]
    exact hfixedVanishes a
  · intro r
    obtain ⟨b, hb⟩ := r.2
    rw [← hb]
    exact hmovingVanishes b

set_option linter.style.haveILetI false in
/-- Bilinear multiplication form of the meeting-branch contradiction.  This
is the direct section-space interface: `product a b` is multiplication of a
section of `O(C)` by a section of `O(H-C)`.  Fixing either distinguished
defining section produces the two maps in the preceding theorem, and their
common product agrees definitionally. -/
theorem
    cubicSurface_degreeEight_fixedComponent_meets_contradiction_of_bilinearProduct
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    {A B : Type u} [AddCommGroup A] [Module K A]
    [AddCommGroup B] [Module K B] [FiniteDimensional K B]
    (product : A →ₗ[K] B →ₗ[K] grading (equationIdeal p hp) 2)
    (a₀ : A) (b₀ : B)
    (ev : LinearMap.range (product.flip b₀) →ₗ[K] (Fin 8 → K))
    (heval : Function.Surjective ev)
    (hsection : ∃ q : LinearMap.range (product.flip b₀),
      q ≠ 0 ∧ ev q = 0)
    (htwo : 2 ≤ finrank K B)
    (hmovingInjective : Function.Injective (product a₀))
    (hq0 : product a₀ b₀ ≠ 0)
    (hcross : ∀ a b, product a b₀ = product a₀ b →
      ∃ c : K, a = c • a₀ ∧ b = c • b₀)
    (x : cubicSurfaceAffinePoints p)
    (hfixedVanishes : ∀ a,
      cubicSurfacePointCoordinateRingEvaluation p hp x (product a b₀) = 0)
    (hmovingVanishes : ∀ b,
      cubicSurfacePointCoordinateRingEvaluation p hp x (product a₀ b) = 0) :
    False := by
  exact
    cubicSurface_degreeEight_fixedComponent_meets_contradiction_of_productMaps
      p hp hne (product.flip b₀) (product a₀) a₀ b₀ ev heval hsection
      htwo hmovingInjective hq0 rfl hcross x hfixedVanishes hmovingVanishes

set_option linter.style.haveILetI false in
/-- In the disjoint branch, generic evaluation similarly forces at least
nine moving sections.  If the fixed curve contains two distinct projective
points, every moving section vanishes at both, while two-point separation by
quadrics bounds the moving space by eight. -/
theorem cubicSurface_degreeEight_fixedComponent_disjoint_contradiction
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (moving : Submodule K (grading (equationIdeal p hp) 2))
    (ev : moving →ₗ[K] (Fin 8 → K))
    (heval : Function.Surjective ev)
    (hsection : ∃ q : moving, q ≠ 0 ∧ ev q = 0)
    (x y : cubicSurfaceAffinePoints p)
    (hdir : ∀ a : K, y.1 ≠ a • x.1)
    (hvan : ∀ q : moving,
      cubicSurfaceCoordinatePointEvaluation p hp q.1 x = 0 ∧
      cubicSurfaceCoordinatePointEvaluation p hp q.1 y = 0) : False := by
  letI : Module.Finite K (grading (equationIdeal p hp) 2) :=
    Module.Finite.of_surjective
      (cubicSurfaceHomogeneousCoordinateProjection p hp 2)
      (cubicSurfaceHomogeneousCoordinateProjection_surjective p hp 2)
  have hnine : 9 ≤ finrank K moving := by
    simpa using
      succ_le_finrank_of_surjective_evaluation_with_nonzero_kernel
        (K := K) (V := moving) 8 ev heval hsection
  exact
    cubicSurface_not_nine_le_finrank_quadraticSubmodule_of_pointwise_vanishing
      p hp hne x y hdir moving hvan hnine

end CubicSurface

end PfaffianDescent
