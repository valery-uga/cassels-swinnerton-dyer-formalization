import PfaffianDescent.VoisinVeryAmpleQuadraticSections

/-!
# Three-point separation by cubic sections

Three distinct projective directions impose three independent conditions on
cubic sections of a cubic surface, even when the points lie on one line. This
gives the dimension bound needed in the disjoint fixed-curve branch of the
sixteen-point construction.
-/

namespace PfaffianDescent

open MvPolynomial Module
open AllCharacteristics.HomogeneousProjective

universe u

variable {K : Type u} [Field K]

/-- A homogeneous linear form taking value one at the first nonzero
direction and zero at the second, given linear independence of the two
directions. -/
theorem exists_homogeneousLinearForm_separating_pair
    (x y : Fin 4 → K) (hli : LinearIndependent K ![x, y]) :
    ∃ ell : MvPolynomial (Fin 4) K,
      ell.IsHomogeneous 1 ∧
      MvPolynomial.aeval x ell = 1 ∧
      MvPolynomial.aeval y ell = 0 := by
  let v : Fin 2 → (Fin 4 → K) := ![x, y]
  let c : (Fin 2 → K) →ₗ[K] (Fin 4 → K) :=
    Fintype.linearCombination K v
  have hc : Function.Injective c := hli.fintypeLinearCombination_injective
  let g : (Fin 4 → K) →ₗ[K] (Fin 2 → K) := c.leftInverse
  have hgc (z : Fin 2 → K) : g (c z) = z :=
    c.leftInverse_apply_of_inj (LinearMap.ker_eq_bot.mpr hc) z
  let φ : (Fin 4 → K) →ₗ[K] K := (LinearMap.proj 0).comp g
  have hc0 : c (Pi.single 0 1) = x := by
    change Fintype.linearCombination K v (Pi.single 0 1) = x
    rw [Fintype.linearCombination_apply_single]
    simp [v]
  have hc1 : c (Pi.single 1 1) = y := by
    change Fintype.linearCombination K v (Pi.single 1 1) = y
    rw [Fintype.linearCombination_apply_single]
    simp [v]
  refine ⟨dualHomogeneousLinearForm φ,
    dualHomogeneousLinearForm_isHomogeneous φ, ?_, ?_⟩
  · rw [dualHomogeneousLinearForm_eval, ← hc0]
    change g (c (Pi.single 0 1)) 0 = 1
    rw [hgc]
    simp
  · rw [dualHomogeneousLinearForm_eval, ← hc1]
    change g (c (Pi.single 1 1)) 0 = 0
    rw [hgc]
    simp

/-- Pairwise distinct nonzero projective directions admit separating
linear forms in every ordered pair. -/
theorem exists_homogeneousLinearForm_separating_directions
    (x y : Fin 4 → K) (hx : x ≠ 0)
    (hxy : ∀ a : K, a • x ≠ y) :
    ∃ ell : MvPolynomial (Fin 4) K,
      ell.IsHomogeneous 1 ∧
      MvPolynomial.aeval x ell = 1 ∧
      MvPolynomial.aeval y ell = 0 := by
  exact exists_homogeneousLinearForm_separating_pair x y
    ((LinearIndependent.pair_iff' hx).mpr hxy)

/-- Evaluation of homogeneous cubic polynomials at three cone points. -/
noncomputable def homogeneousCubicTripleEvaluation
    (v : Fin 3 → Fin 4 → K) :
    homogeneousSubmodule (Fin 4) K 3 →ₗ[K] (Fin 3 → K) where
  toFun q i := MvPolynomial.aeval (v i) q.1
  map_add' q r := by ext i; simp
  map_smul' a q := by ext i; simp

/-- Cubics interpolate arbitrary values at three pairwise distinct
projective directions. The three vectors need not be linearly independent. -/
theorem homogeneousCubicTripleEvaluation_surjective
    (v : Fin 3 → Fin 4 → K)
    (hzero : ∀ i, v i ≠ 0)
    (hdir : ∀ i j, i ≠ j → ∀ a : K, a • v i ≠ v j) :
    Function.Surjective (homogeneousCubicTripleEvaluation v) := by
  let L01 := Classical.choose
    (exists_homogeneousLinearForm_separating_directions (v 0) (v 1)
      (hzero 0) (hdir 0 1 (by decide)))
  let L02 := Classical.choose
    (exists_homogeneousLinearForm_separating_directions (v 0) (v 2)
      (hzero 0) (hdir 0 2 (by decide)))
  let L10 := Classical.choose
    (exists_homogeneousLinearForm_separating_directions (v 1) (v 0)
      (hzero 1) (hdir 1 0 (by decide)))
  let L12 := Classical.choose
    (exists_homogeneousLinearForm_separating_directions (v 1) (v 2)
      (hzero 1) (hdir 1 2 (by decide)))
  let L20 := Classical.choose
    (exists_homogeneousLinearForm_separating_directions (v 2) (v 0)
      (hzero 2) (hdir 2 0 (by decide)))
  let L21 := Classical.choose
    (exists_homogeneousLinearForm_separating_directions (v 2) (v 1)
      (hzero 2) (hdir 2 1 (by decide)))
  have h01 := Classical.choose_spec
    (exists_homogeneousLinearForm_separating_directions (v 0) (v 1)
      (hzero 0) (hdir 0 1 (by decide)))
  have h02 := Classical.choose_spec
    (exists_homogeneousLinearForm_separating_directions (v 0) (v 2)
      (hzero 0) (hdir 0 2 (by decide)))
  have h10 := Classical.choose_spec
    (exists_homogeneousLinearForm_separating_directions (v 1) (v 0)
      (hzero 1) (hdir 1 0 (by decide)))
  have h12 := Classical.choose_spec
    (exists_homogeneousLinearForm_separating_directions (v 1) (v 2)
      (hzero 1) (hdir 1 2 (by decide)))
  have h20 := Classical.choose_spec
    (exists_homogeneousLinearForm_separating_directions (v 2) (v 0)
      (hzero 2) (hdir 2 0 (by decide)))
  have h21 := Classical.choose_spec
    (exists_homogeneousLinearForm_separating_directions (v 2) (v 1)
      (hzero 2) (hdir 2 1 (by decide)))
  change L01.IsHomogeneous 1 ∧
    MvPolynomial.aeval (v 0) L01 = 1 ∧
    MvPolynomial.aeval (v 1) L01 = 0 at h01
  change L02.IsHomogeneous 1 ∧
    MvPolynomial.aeval (v 0) L02 = 1 ∧
    MvPolynomial.aeval (v 2) L02 = 0 at h02
  change L10.IsHomogeneous 1 ∧
    MvPolynomial.aeval (v 1) L10 = 1 ∧
    MvPolynomial.aeval (v 0) L10 = 0 at h10
  change L12.IsHomogeneous 1 ∧
    MvPolynomial.aeval (v 1) L12 = 1 ∧
    MvPolynomial.aeval (v 2) L12 = 0 at h12
  change L20.IsHomogeneous 1 ∧
    MvPolynomial.aeval (v 2) L20 = 1 ∧
    MvPolynomial.aeval (v 0) L20 = 0 at h20
  change L21.IsHomogeneous 1 ∧
    MvPolynomial.aeval (v 2) L21 = 1 ∧
    MvPolynomial.aeval (v 1) L21 = 0 at h21
  simp only [MvPolynomial.aeval_eq_eval] at h01 h02 h10 h12 h20 h21
  let Q0 : homogeneousSubmodule (Fin 4) K 3 :=
    ⟨L01 ^ 2 * L02, by simpa using (h01.1.pow 2).mul h02.1⟩
  let Q1 : homogeneousSubmodule (Fin 4) K 3 :=
    ⟨L10 ^ 2 * L12, by simpa using (h10.1.pow 2).mul h12.1⟩
  let Q2 : homogeneousSubmodule (Fin 4) K 3 :=
    ⟨L20 ^ 2 * L21, by simpa using (h20.1.pow 2).mul h21.1⟩
  intro z
  refine ⟨z 0 • Q0 + z 1 • Q1 + z 2 • Q2, ?_⟩
  ext i
  fin_cases i
  · change MvPolynomial.aeval (v 0)
      ((z 0 • Q0 + z 1 • Q1 + z 2 • Q2 :
        homogeneousSubmodule (Fin 4) K 3).1) = z 0
    simp [Q0, Q1, Q2, map_mul, map_pow,
      h01.2.1, h02.2.1, h10.2.2, h20.2.2]
  · change MvPolynomial.aeval (v 1)
      ((z 0 • Q0 + z 1 • Q1 + z 2 • Q2 :
        homogeneousSubmodule (Fin 4) K 3).1) = z 1
    simp [Q0, Q1, Q2, map_mul, map_pow,
      h01.2.2, h10.2.1, h12.2.1, h21.2.2]
  · change MvPolynomial.aeval (v 2)
      ((z 0 • Q0 + z 1 • Q1 + z 2 • Q2 :
        homogeneousSubmodule (Fin 4) K 3).1) = z 2
    simp [Q0, Q1, Q2, map_mul, map_pow,
      h02.2.2, h12.2.2, h20.2.1, h21.2.1]

section CubicSurface

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Evaluation of actual cubic coordinate-ring sections at three points of
the cubic surface. -/
noncomputable def cubicSurfaceCubicTripleEvaluation
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (x : Fin 3 → cubicSurfaceAffinePoints p) :
    grading (equationIdeal p hp) 3 →ₗ[K] (Fin 3 → K) where
  toFun q i := cubicSurfaceCoordinatePointEvaluation p hp q (x i)
  map_add' q r := by
    ext i
    simp [cubicSurfaceCoordinatePointEvaluation]
  map_smul' a q := by
    ext i
    simp [cubicSurfaceCoordinatePointEvaluation]

/-- Three projectively distinct points impose independent conditions on
actual cubic sections of the cubic surface. -/
theorem cubicSurfaceCubicTripleEvaluation_surjective
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (x : Fin 3 → cubicSurfaceAffinePoints p)
    (hdir : ∀ i j, i ≠ j → ∀ a : K, a • (x i).1 ≠ (x j).1) :
    Function.Surjective (cubicSurfaceCubicTripleEvaluation p hp x) := by
  let v : Fin 3 → Fin 4 → K := fun i => (x i).1
  have hsurj : Function.Surjective (homogeneousCubicTripleEvaluation v) :=
    homogeneousCubicTripleEvaluation_surjective v
      (fun i => (x i).2.2) hdir
  intro z
  obtain ⟨q, hq⟩ := hsurj z
  refine ⟨cubicSurfaceHomogeneousCoordinateProjection p hp 3 q, ?_⟩
  ext i
  change MvPolynomial.aeval (x i).1 q.1 = z i
  exact congrFun hq i

set_option linter.style.haveILetI false in
/-- The cubics vanishing at three projectively distinct points form a
sixteen-dimensional subspace of the nineteen cubic sections on a cubic
surface. -/
theorem cubicSurfaceCubicTripleEvaluation_ker_finrank
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (x : Fin 3 → cubicSurfaceAffinePoints p)
    (hdir : ∀ i j, i ≠ j → ∀ a : K, a • (x i).1 ≠ (x j).1) :
    finrank K (LinearMap.ker
      (cubicSurfaceCubicTripleEvaluation p hp x)) = 16 := by
  letI : Module.Finite K (grading (equationIdeal p hp) 3) :=
    Module.Finite.of_surjective
      (cubicSurfaceHomogeneousCoordinateProjection p hp 3)
      (cubicSurfaceHomogeneousCoordinateProjection_surjective p hp 3)
  let e := cubicSurfaceCubicTripleEvaluation p hp x
  have hsurj : Function.Surjective e :=
    cubicSurfaceCubicTripleEvaluation_surjective p hp x hdir
  have hrange : LinearMap.range e = ⊤ := LinearMap.range_eq_top.mpr hsurj
  have hdim := e.finrank_range_add_finrank_ker
  dsimp only [e] at hdim
  rw [hrange, finrank_top, Module.finrank_pi_fintype,
    Module.finrank_self, cubicSurface_grade_three_finrank p hp hne] at hdim
  norm_num at hdim
  omega

set_option linter.style.haveILetI false in
/-- A cubic subsystem vanishing at three projectively distinct surface
points has at most sixteen sections. -/
theorem cubicSurfaceCubicSubmodule_finrank_le_sixteen_of_pointwise_vanishing
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (x : Fin 3 → cubicSurfaceAffinePoints p)
    (hdir : ∀ i j, i ≠ j → ∀ a : K, a • (x i).1 ≠ (x j).1)
    (W : Submodule K (grading (equationIdeal p hp) 3))
    (hvan : ∀ q : W, ∀ i,
      cubicSurfaceCoordinatePointEvaluation p hp q.1 (x i) = 0) :
    finrank K W ≤ 16 := by
  letI : Module.Finite K (grading (equationIdeal p hp) 3) :=
    Module.Finite.of_surjective
      (cubicSurfaceHomogeneousCoordinateProjection p hp 3)
      (cubicSurfaceHomogeneousCoordinateProjection_surjective p hp 3)
  have hW : W ≤ LinearMap.ker (cubicSurfaceCubicTripleEvaluation p hp x) := by
    intro q hq
    apply LinearMap.mem_ker.mpr
    ext i
    exact hvan ⟨q, hq⟩ i
  rw [← cubicSurfaceCubicTripleEvaluation_ker_finrank p hp hne x hdir]
  exact Submodule.finrank_mono hW

set_option linter.style.haveILetI false in
/-- The same three-point bound for a homogeneous polynomial frame that is
independent modulo the defining cubic. This is the form needed to combine
with generic finite-incidence avoidance. -/
theorem homogeneousCubicPolynomialSubmodule_finrank_le_sixteen_of_pointwise_vanishing
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (x : Fin 3 → cubicSurfaceAffinePoints p)
    (hdir : ∀ i j, i ≠ j → ∀ a : K, a • (x i).1 ≠ (x j).1)
    (W : Submodule K (MvPolynomial (Fin 4) K))
    [FiniteDimensional K W]
    (hhom : ∀ q ∈ W, q.IsHomogeneous 3)
    (hseparate : ∀ q ∈ W,
      q ∈ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) → q = 0)
    (hvan : ∀ q : W, ∀ i, MvPolynomial.aeval (x i).1 q.1 = 0) :
    finrank K W ≤ 16 := by
  letI : Module.Finite K (grading (equationIdeal p hp) 3) :=
    Module.Finite.of_surjective
      (cubicSurfaceHomogeneousCoordinateProjection p hp 3)
      (cubicSurfaceHomogeneousCoordinateProjection_surjective p hp 3)
  let lift : W →ₗ[K] homogeneousSubmodule (Fin 4) K 3 :=
    { toFun := fun q => ⟨q.1, hhom q.1 q.2⟩
      map_add' := by intro q r; ext <;> rfl
      map_smul' := by intro a q; ext <;> rfl }
  let f : W →ₗ[K] grading (equationIdeal p hp) 3 :=
    (cubicSurfaceHomogeneousCoordinateProjection p hp 3).comp lift
  have hf : Function.Injective f := by
    apply (LinearMap.ker_eq_bot).mp
    ext q
    constructor
    · intro hq
      have hqzero : f q = 0 := LinearMap.mem_ker.mp hq
      have hqquot : Ideal.Quotient.mk (equationIdeal p hp).toIdeal q.1 = 0 := by
        exact congrArg Subtype.val hqzero
      have hqideal : q.1 ∈ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) := by
        exact Ideal.Quotient.eq_zero_iff_mem.mp hqquot
      exact Subtype.ext (hseparate q.1 q.2 hqideal)
    · intro hq
      have hq0 : q = 0 := by simpa only [Submodule.mem_bot] using hq
      simp [hq0]
  have hbound : finrank K (LinearMap.range f) ≤ 16 := by
    apply cubicSurfaceCubicSubmodule_finrank_le_sixteen_of_pointwise_vanishing
      p hp hne x hdir
    intro r i
    obtain ⟨q, hq⟩ := r.property
    change cubicSurfaceCoordinatePointEvaluation p hp r.1 (x i) = 0
    rw [← hq]
    exact hvan q i
  rw [LinearMap.finrank_range_of_inj hf] at hbound
  exact hbound

end CubicSurface

end PfaffianDescent
