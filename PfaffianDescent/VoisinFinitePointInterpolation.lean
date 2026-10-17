import PfaffianDescent.VoisinVeryAmpleCubicSections
import PfaffianDescent.VoisinSectionLinearAlgebra
import PfaffianDescent.VoisinGenericSixteenFixedCurveCubicSections

/-!
# Interpolation at finitely many projective points

The disjoint-curve branch of Voisin's Lemma 3.3 needs a curve to impose at
least `l + 2` conditions on degree-`l + 1` sections.  This file proves the
finite-point part: any `l + 2` distinct geometric projective points impose
independent conditions on homogeneous forms of that degree.
-/

namespace PfaffianDescent

open AlgebraicGeometry MvPolynomial Module
open AllCharacteristics.HomogeneousProjective

universe u

variable {K : Type u} [Field K]

/-- Evaluation of homogeneous forms of degree `r - 1` at `r` affine-cone
representatives. -/
noncomputable def homogeneousFinitePointEvaluation
    (r : ℕ) (v : Fin r → Fin 4 → K) :
    homogeneousSubmodule (Fin 4) K (r - 1) →ₗ[K] (Fin r → K) where
  toFun q i := MvPolynomial.aeval (v i) q.1
  map_add' q q' := by ext i; simp
  map_smul' a q := by ext i; simp

/-- Polynomial interpolation works at any positive number of pairwise
distinct projective directions; no linear independence of all directions is
required. -/
theorem homogeneousFinitePointEvaluation_surjective
    (r : ℕ) (v : Fin r → Fin 4 → K)
    (hzero : ∀ i, v i ≠ 0)
    (hdir : ∀ i j, i ≠ j → ∀ a : K, a • v i ≠ v j) :
    Function.Surjective (homogeneousFinitePointEvaluation r v) := by
  classical
  let L : Fin r → Fin r → MvPolynomial (Fin 4) K := fun i j =>
    if h : i = j then 0 else
      Classical.choose
        (exists_homogeneousLinearForm_separating_directions
          (v i) (v j) (hzero i) (hdir i j h))
  have hL (i j : Fin r) (hij : i ≠ j) :
      (L i j).IsHomogeneous 1 ∧
      MvPolynomial.aeval (v i) (L i j) = 1 ∧
      MvPolynomial.aeval (v j) (L i j) = 0 := by
    dsimp [L]
    simp only [dif_neg hij]
    exact Classical.choose_spec
      (exists_homogeneousLinearForm_separating_directions
        (v i) (v j) (hzero i) (hdir i j hij))
  let Q : Fin r → MvPolynomial (Fin 4) K := fun i =>
    ∏ j ∈ Finset.univ.erase i, L i j
  have hQhom (i : Fin r) : (Q i).IsHomogeneous (r - 1) := by
    have hprod : (Q i).IsHomogeneous
        (∑ _j ∈ Finset.univ.erase i, (1 : ℕ)) := by
      apply IsHomogeneous.prod
      intro j hj
      exact (hL i j (Finset.mem_erase.mp hj).1.symm).1
    simpa [Finset.sum_const, Finset.card_erase_of_mem,
      Finset.mem_univ] using hprod
  have hQeval (i j : Fin r) :
      MvPolynomial.aeval (v j) (Q i) = if j = i then 1 else 0 := by
    by_cases hji : j = i
    · subst j
      simp only [Q, MvPolynomial.aeval_prod]
      apply Finset.prod_eq_one
      intro k hk
      exact (hL i k (Finset.mem_erase.mp hk).1.symm).2.1
    · have hjmem : j ∈ Finset.univ.erase i :=
        Finset.mem_erase.mpr ⟨hji, Finset.mem_univ _⟩
      simp only [if_neg hji, Q, MvPolynomial.aeval_prod]
      exact Finset.prod_eq_zero hjmem (hL i j (Ne.symm hji)).2.2
  intro z
  let q : homogeneousSubmodule (Fin 4) K (r - 1) :=
    ∑ i : Fin r, z i • ⟨Q i, hQhom i⟩
  refine ⟨q, ?_⟩
  ext j
  change MvPolynomial.aeval (v j) q.1 = z j
  simp only [q, Submodule.coe_sum, Submodule.coe_smul,
    MvPolynomial.aeval_sum, map_smul, hQeval]
  simp

section CubicSurface

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Evaluation of the degree-`r - 1` coordinate-ring sections of a cubic
surface at `r` geometric points. -/
noncomputable def cubicSurfaceFinitePointEvaluation
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (r : ℕ) (x : Fin r → cubicSurfaceAffinePoints p) :
    grading (equationIdeal p hp) (r - 1) →ₗ[K] (Fin r → K) where
  toFun q i := cubicSurfaceCoordinatePointEvaluation p hp q (x i)
  map_add' q q' := by
    ext i
    simp [cubicSurfaceCoordinatePointEvaluation]
  map_smul' a q := by
    ext i
    simp [cubicSurfaceCoordinatePointEvaluation]

/-- Distinct points impose independent conditions on actual cubic-surface
sections of degree `r - 1`. -/
theorem cubicSurfaceFinitePointEvaluation_surjective
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (r : ℕ) (x : Fin r → cubicSurfaceAffinePoints p)
    (hdir : ∀ i j, i ≠ j → ∀ a : K,
      a • (x i).1 ≠ (x j).1) :
    Function.Surjective (cubicSurfaceFinitePointEvaluation p hp r x) := by
  let v : Fin r → Fin 4 → K := fun i => (x i).1
  have hsurj : Function.Surjective (homogeneousFinitePointEvaluation r v) :=
    homogeneousFinitePointEvaluation_surjective r v
      (fun i => (x i).2.2) hdir
  intro z
  obtain ⟨q, hq⟩ := hsurj z
  refine ⟨cubicSurfaceHomogeneousCoordinateProjection p hp (r - 1) q, ?_⟩
  ext i
  change MvPolynomial.aeval (x i).1 q.1 = z i
  exact congrFun hq i

/-- Consequently the subspace of degree-`r - 1` sections vanishing at all
`r` points has codimension exactly `r`. -/
theorem cubicSurfaceFinitePointEvaluation_ker_codimension
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (r : ℕ) (x : Fin r → cubicSurfaceAffinePoints p)
    (hdir : ∀ i j, i ≠ j → ∀ a : K,
      a • (x i).1 ≠ (x j).1) :
    Module.finrank K (LinearMap.ker
      (cubicSurfaceFinitePointEvaluation p hp r x)) + r =
      Module.finrank K (grading (equationIdeal p hp) (r - 1)) := by
  letI : Module.Finite K (grading (equationIdeal p hp) (r - 1)) :=
    Module.Finite.of_surjective
      (cubicSurfaceHomogeneousCoordinateProjection p hp (r - 1))
      (cubicSurfaceHomogeneousCoordinateProjection_surjective p hp (r - 1))
  let e := cubicSurfaceFinitePointEvaluation p hp r x
  have hrange : LinearMap.range e = ⊤ :=
    LinearMap.range_eq_top.mpr
      (cubicSurfaceFinitePointEvaluation_surjective p hp r x hdir)
  have hdim := e.finrank_range_add_finrank_ker
  rw [hrange, finrank_top, Module.finrank_pi_fintype,
    Module.finrank_self] at hdim
  simpa [e, Nat.add_comm] using hdim

/-- Any subsystem whose sections vanish on `r` distinct surface points has
codimension at least `r`.  In particular, a curve containing `l + 2`
distinct geometric points imposes at least `l + 2` conditions on the
degree-`l + 1` ambient system. -/
theorem cubicSurface_sectionSubmodule_codimension_ge_of_vanishes_fin_points
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (r : ℕ) (x : Fin r → cubicSurfaceAffinePoints p)
    (hdir : ∀ i j, i ≠ j → ∀ a : K,
      a • (x i).1 ≠ (x j).1)
    (W : Submodule K (grading (equationIdeal p hp) (r - 1)))
    (hvan : W ≤ LinearMap.ker
      (cubicSurfaceFinitePointEvaluation p hp r x)) :
    Module.finrank K W + r ≤
      Module.finrank K (grading (equationIdeal p hp) (r - 1)) := by
  letI : Module.Finite K (grading (equationIdeal p hp) (r - 1)) :=
    Module.Finite.of_surjective
      (cubicSurfaceHomogeneousCoordinateProjection p hp (r - 1))
      (cubicSurfaceHomogeneousCoordinateProjection_surjective p hp (r - 1))
  have hmono := Submodule.finrank_mono hvan
  have hcodim := cubicSurfaceFinitePointEvaluation_ker_codimension
    p hp r x hdir
  omega

/-- Voisin's `l + 2` restriction count in the exact degree used by Lemma
3.3.  The hypothesis `hvan` is supplied when the subsystem consists of
sections containing a curve through these points. -/
theorem cubicSurface_curveRestriction_codimension_ge_l_add_two
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (l : ℕ) (x : Fin (l + 2) → cubicSurfaceAffinePoints p)
    (hdir : ∀ i j, i ≠ j → ∀ a : K,
      a • (x i).1 ≠ (x j).1)
    (W : Submodule K (grading (equationIdeal p hp) (l + 1)))
    (hvan : W ≤ LinearMap.ker
      (cubicSurfaceFinitePointEvaluation p hp (l + 2) x)) :
    Module.finrank K W + (l + 2) ≤
      Module.finrank K (grading (equationIdeal p hp) (l + 1)) := by
  have h := cubicSurface_sectionSubmodule_codimension_ge_of_vanishes_fin_points
    p hp (l + 2) x hdir W hvan
  exact h

/-- Combine the finite-point curve restriction count with generic
independence of the marked length-`d` points. This is the linear and
interpolation content of Voisin's disjoint-curve branch; the remaining
geometric task is to establish `hgeneric` for the relevant moving curve
family. -/
theorem cubicSurface_disjointCurve_surviving_sections_lt_two_mul
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (l d s : ℕ) (hs : 0 < s)
    (x : Fin (l + 2) → cubicSurfaceAffinePoints p)
    (hdir : ∀ i j, i ≠ j → ∀ a : K,
      a • (x i).1 ≠ (x j).1)
    {T : Type u} [AddCommGroup T] [Module K T] [FiniteDimensional K T]
    (markedEvaluation : grading (equationIdeal p hp) (l + 1) →ₗ[K]
      (Fin d → K))
    (curveRestriction : grading (equationIdeal p hp) (l + 1) →ₗ[K] T)
    (hvan : LinearMap.ker curveRestriction ≤ LinearMap.ker
      (cubicSurfaceFinitePointEvaluation p hp (l + 2) x))
    (hsource : Module.finrank K (grading (equationIdeal p hp) (l + 1)) ≤
      d + (2 * s + 1))
    (hgeneric : Function.Surjective
      (markedEvaluation.domRestrict (LinearMap.ker curveRestriction)) ∨
      Function.Injective
      (markedEvaluation.domRestrict (LinearMap.ker curveRestriction))) :
    Module.finrank K (LinearMap.ker
      (markedEvaluation.domRestrict (LinearMap.ker curveRestriction))) <
        2 * s := by
  letI : Module.Finite K (grading (equationIdeal p hp) (l + 1)) :=
    Module.Finite.of_surjective
      (cubicSurfaceHomogeneousCoordinateProjection p hp (l + 1))
      (cubicSurfaceHomogeneousCoordinateProjection_surjective p hp (l + 1))
  have hcurve := cubicSurface_curveRestriction_codimension_ge_l_add_two
    p hp l x hdir (LinearMap.ker curveRestriction) hvan
  apply fixedCurve_surviving_sections_lt_two_mul_of_maximal_rank
    markedEvaluation curveRestriction d s l hs
  · simp
  · exact hsource
  · exact hcurve
  · exact hgeneric

/-- Four distinct points on an actual fixed curve impose the four cubic
conditions required by Voisin's disjoint-curve argument at `l = 2`. This
improves the three-condition estimate in
`fixedCurveCubicSurfaceSystem_finrank_le_sixteen`. -/
theorem fixedCurveCubicSurfaceSystem_finrank_le_fifteen
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (x : Fin 4 → cubicSurfaceAffinePoints p)
    (hdir : ∀ i j, i ≠ j → ∀ a : K,
      a • (x i).1 ≠ (x j).1)
    (hx : ∀ i, ∀ f ∈ C.toIdeal,
      MvPolynomial.aeval (x i).1 f = 0) :
    Module.finrank K (fixedCurveCubicSurfaceSystem p hp C) ≤ 15 := by
  have hvan : fixedCurveCubicSurfaceSystem p hp C ≤
      LinearMap.ker (cubicSurfaceFinitePointEvaluation p hp 4 x) := by
    intro z hz
    apply LinearMap.mem_ker.mpr
    funext i
    obtain ⟨q, hqC, hqz⟩ := hz
    rw [← hqz]
    change MvPolynomial.aeval (x i).1 q.1 = 0
    exact hx i q.1 ((mem_homogeneousIdealPiece_iff C 3 q).mp hqC)
  have hcodim := cubicSurface_curveRestriction_codimension_ge_l_add_two
    p hp 2 x hdir (fixedCurveCubicSurfaceSystem p hp C) hvan
  rw [cubicSurface_grade_three_finrank p hp hne] at hcodim
  have hbound : Module.finrank K (fixedCurveCubicSurfaceSystem p hp C) + 4 ≤ 19 :=
    hcodim
  omega

end CubicSurface

end PfaffianDescent
