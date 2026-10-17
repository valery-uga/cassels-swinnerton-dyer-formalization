import PfaffianDescent.TripleCompleteIntersectionJacobian

/-!
# Jacobian selection in a moving quadratic system

The general chart Jacobian is linear in its third equation, but the original
selection API specialized that equation to a cubic.  Voisin's final
degree-eight residual instead moves a quadric.  This file records the same
linear bad-subspace machinery for an arbitrary moving degree and supplies the
explicit quadratic pointwise witness.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

variable {K : Type u} [Field K]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Evaluation of the chart Jacobian as a linear function of a homogeneous
third equation of arbitrary degree. -/
noncomputable def tripleCompleteIntersectionChartJacobianEvaluationLinearMapDegree
    {A : Type u} [CommRing A] [Algebra K A]
    (d : ℕ) (p q : MvPolynomial (Fin 4) K) (j : Fin 4)
    (e : MvPolynomial (Fin 4) K →ₐ[K] A) :
    homogeneousSubmodule (Fin 4) K d →ₗ[K] A :=
  { toFun := fun r =>
      e (tripleCompleteIntersectionChartJacobianPolynomial p q r.1 j)
    map_add' := by
      intro r s
      rw [Submodule.coe_add,
        tripleCompleteIntersectionChartJacobianPolynomial_add_right, map_add]
    map_smul' := by
      intro a r
      rw [Submodule.coe_smul]
      change e (tripleCompleteIntersectionChartJacobianPolynomial p q
        (a • r.1) j) = _
      rw [show (a • r.1 : MvPolynomial (Fin 4) K) = C a * r.1 by
        simp [smul_eq_C_mul],
        tripleCompleteIntersectionChartJacobianPolynomial_C_mul_right]
      simp [Algebra.smul_def] }

/-- Restriction of the arbitrary-degree Jacobian functional to a prescribed
linear system. -/
noncomputable def tripleCompleteIntersectionChartJacobianEvaluationLinearMapDegree_restrict
    {A : Type u} [CommRing A] [Algebra K A]
    (d : ℕ) (p q : MvPolynomial (Fin 4) K) (j : Fin 4)
    (e : MvPolynomial (Fin 4) K →ₐ[K] A)
    (W : Submodule K (homogeneousSubmodule (Fin 4) K d)) : W →ₗ[K] A :=
  (tripleCompleteIntersectionChartJacobianEvaluationLinearMapDegree
    d p q j e).comp W.subtype

theorem tripleCompleteIntersectionChartJacobianEvaluationLinearMapDegree_restrict_ne_zero_iff
    {A : Type u} [CommRing A] [Algebra K A]
    (d : ℕ) (p q : MvPolynomial (Fin 4) K) (j : Fin 4)
    (e : MvPolynomial (Fin 4) K →ₐ[K] A)
    (W : Submodule K (homogeneousSubmodule (Fin 4) K d)) :
    tripleCompleteIntersectionChartJacobianEvaluationLinearMapDegree_restrict
        d p q j e W ≠ 0 ↔
      ∃ r : W,
        e (tripleCompleteIntersectionChartJacobianPolynomial p q r.1.1 j) ≠ 0 := by
  constructor
  · intro hmap
    by_contra h
    push Not at h
    apply hmap
    ext r
    exact h r
  · rintro ⟨r, hr⟩ hmap
    apply hr
    have hvalue := congrArg (fun f : W →ₗ[K] A => f r) hmap
    simpa [tripleCompleteIntersectionChartJacobianEvaluationLinearMapDegree_restrict,
      tripleCompleteIntersectionChartJacobianEvaluationLinearMapDegree] using hvalue

/-- The linear subspace of degree-`d` equations whose chart Jacobian lands in
the chosen ideal. -/
noncomputable def tripleCompleteIntersectionChartJacobianBadSubmoduleDegree
    {A : Type u} [CommRing A] [Algebra K A]
    (d : ℕ) (p q : MvPolynomial (Fin 4) K) (j : Fin 4)
    (e : MvPolynomial (Fin 4) K →ₐ[K] A) (Q : Ideal A) :
    Submodule K (homogeneousSubmodule (Fin 4) K d) :=
  (Q.restrictScalars K).comap
    (tripleCompleteIntersectionChartJacobianEvaluationLinearMapDegree
      d p q j e)

theorem mem_tripleCompleteIntersectionChartJacobianBadSubmoduleDegree_iff
    {A : Type u} [CommRing A] [Algebra K A]
    (d : ℕ) (p q : MvPolynomial (Fin 4) K) (j : Fin 4)
    (e : MvPolynomial (Fin 4) K →ₐ[K] A) (Q : Ideal A)
    (r : homogeneousSubmodule (Fin 4) K d) :
    r ∈ tripleCompleteIntersectionChartJacobianBadSubmoduleDegree
        d p q j e Q ↔
      e (tripleCompleteIntersectionChartJacobianPolynomial p q r.1 j) ∈ Q :=
  Iff.rfl

theorem tripleCompleteIntersectionChartJacobianBadSubmoduleDegree_ne_top_iff
    {A : Type u} [CommRing A] [Algebra K A]
    (d : ℕ) (p q : MvPolynomial (Fin 4) K) (j : Fin 4)
    (e : MvPolynomial (Fin 4) K →ₐ[K] A) (Q : Ideal A) :
    tripleCompleteIntersectionChartJacobianBadSubmoduleDegree d p q j e Q ≠ ⊤ ↔
      ∃ r : homogeneousSubmodule (Fin 4) K d,
        e (tripleCompleteIntersectionChartJacobianPolynomial p q r.1 j) ∉ Q := by
  constructor
  · intro hne
    classical
    by_contra hno
    apply hne
    apply top_unique
    intro r hr
    by_contra hmem
    exact hno ⟨r, hmem⟩
  · rintro ⟨r, hr⟩ htop
    have hm : r ∈
        tripleCompleteIntersectionChartJacobianBadSubmoduleDegree
          d p q j e Q := by
      rw [htop]
      exact Submodule.mem_top
    exact hr ((mem_tripleCompleteIntersectionChartJacobianBadSubmoduleDegree_iff
      d p q j e Q r).mp hm)

/-- One degree-`d` equation avoids finitely many pointwise Jacobian bad
subspaces, with all four projective charts handled simultaneously. -/
theorem exists_homogeneous_avoiding_finite_allChart_tripleCompleteIntersectionChartJacobian_badSubmodules
    {d : ℕ} {ι : Type*} [Finite ι] [Infinite K]
    {A : Fin 4 × ι → Type u}
    [∀ z, CommRing (A z)] [∀ z, Algebra K (A z)]
    (p q : MvPolynomial (Fin 4) K)
    (e : ∀ z, MvPolynomial (Fin 4) K →ₐ[K] A z)
    (Q : ∀ z, Ideal (A z))
    (hproper : ∀ z,
      tripleCompleteIntersectionChartJacobianBadSubmoduleDegree
        d p q z.1 (e z) (Q z) ≠ ⊤) :
    ∃ r : homogeneousSubmodule (Fin 4) K d,
      ∀ (j : Fin 4) (i : ι),
        e (j, i) (tripleCompleteIntersectionChartJacobianPolynomial p q r.1 j) ∉
          Q (j, i) := by
  let bad : (Fin 4 × ι) →
      Submodule K (homogeneousSubmodule (Fin 4) K d) := fun z =>
    tripleCompleteIntersectionChartJacobianBadSubmoduleDegree
      d p q z.1 (e z) (Q z)
  obtain ⟨r, hr⟩ := exists_vector_avoiding_finite_submodules bad (by
    intro z
    exact hproper z)
  refine ⟨r, ?_⟩
  intro j i
  have hrnot : r ∉ bad (j, i) := hr (j, i)
  exact (not_congr
    (mem_tripleCompleteIntersectionChartJacobianBadSubmoduleDegree_iff
      d p q j (e (j, i)) (Q (j, i)) r)).mp hrnot

/-! ## Explicit quadratic pointwise witness -/

/-- A homogeneous quadric vanishing at `x` whose affine first derivative is
the `i`-th coordinate vector, scaled by the nonzero chart coordinate. -/
noncomputable def tripleCompleteIntersectionChartJacobianWitnessQuadric
    (x : Fin 4 → K) (j : Fin 4) (i : Fin 3) : MvPolynomial (Fin 4) K :=
  (X (j.succAbove i) - C (x (j.succAbove i) / x j) * X j) * X j

theorem tripleCompleteIntersectionChartJacobianWitnessQuadric_isHomogeneous
    (x : Fin 4 → K) (j : Fin 4) (i : Fin 3) :
    (tripleCompleteIntersectionChartJacobianWitnessQuadric x j i).IsHomogeneous 2 := by
  unfold tripleCompleteIntersectionChartJacobianWitnessQuadric
  have hlin :
      (X (j.succAbove i) - C (x (j.succAbove i) / x j) * X j).IsHomogeneous 1 := by
    apply IsHomogeneous.sub
    · exact MvPolynomial.isHomogeneous_X _ _
    · exact (MvPolynomial.isHomogeneous_C _ _).mul
        (MvPolynomial.isHomogeneous_X _ _)
  simpa using hlin.mul (MvPolynomial.isHomogeneous_X _ _)

theorem tripleCompleteIntersectionChartJacobianWitnessQuadric_eval
    (x : Fin 4 → K) (j : Fin 4) (i : Fin 3) (hxj : x j ≠ 0) :
    (tripleCompleteIntersectionChartJacobianWitnessQuadric x j i).eval x = 0 := by
  unfold tripleCompleteIntersectionChartJacobianWitnessQuadric
  simp [hxj]

theorem tripleCompleteIntersectionChartJacobianWitnessQuadric_pderiv_eval
    (x : Fin 4 → K) (j : Fin 4) (i k : Fin 3) :
    (pderiv (j.succAbove k)
      (tripleCompleteIntersectionChartJacobianWitnessQuadric x j i)).eval x =
      if k = i then x j else 0 := by
  unfold tripleCompleteIntersectionChartJacobianWitnessQuadric
  rw [pderiv_mul, (pderiv (j.succAbove k)).map_sub]
  simp only [pderiv_mul, pderiv_X, pderiv_C, eval_add, eval_sub, eval_mul,
    map_zero, map_one, eval_X, eval_C]
  by_cases hki : k = i
  · subst k
    simp
  · simp [hki]

/-- Linear independence of the first two derivative columns produces an
explicit quadratic third column with nonzero chart Jacobian. -/
theorem exists_quadric_with_nonzero_chartJacobian_eval_of_linearIndependent_derivatives
    (p q : MvPolynomial (Fin 4) K)
    (j : Fin 4) (x : Fin 4 → K) (hxj : x j ≠ 0)
    (hderiv : LinearIndependent K
      ![(fun i : Fin 3 => (pderiv (j.succAbove i) p).eval x),
        (fun i : Fin 3 => (pderiv (j.succAbove i) q).eval x)]) :
    ∃ r : homogeneousSubmodule (Fin 4) K 2,
      (tripleCompleteIntersectionChartJacobianPolynomial p q r.1 j).eval x ≠ 0 := by
  obtain ⟨i, hdeti⟩ :=
    exists_nonzero_chartJacobian_minor_of_linearIndependent_derivatives
      p q x j hderiv
  let rpoly := tripleCompleteIntersectionChartJacobianWitnessQuadric x j i
  have hrpoly : rpoly.IsHomogeneous 2 :=
    tripleCompleteIntersectionChartJacobianWitnessQuadric_isHomogeneous x j i
  refine ⟨⟨rpoly, hrpoly⟩, ?_⟩
  let ev : MvPolynomial (Fin 4) K →+* K :=
    MvPolynomial.eval₂Hom (RingHom.id K) x
  let Mpoly := tripleCompleteIntersectionChartJacobianMinorMatrix p q rpoly j
  have hM : ev.mapMatrix Mpoly =
      (tripleCompleteIntersectionChartJacobianEvaluationBaseMatrix p q x j).updateCol
        2 (fun k => if k = i then x j else 0) := by
    ext k l
    fin_cases l
    · simp [Mpoly, tripleCompleteIntersectionChartJacobianMinorMatrix,
        tripleCompleteIntersectionChartJacobianEvaluationBaseMatrix, ev]
    · simp [Mpoly, tripleCompleteIntersectionChartJacobianMinorMatrix,
        tripleCompleteIntersectionChartJacobianEvaluationBaseMatrix, ev]
    · simp [Mpoly, tripleCompleteIntersectionChartJacobianMinorMatrix,
        tripleCompleteIntersectionChartJacobianEvaluationBaseMatrix, ev]
      simpa [rpoly, ev] using
        (tripleCompleteIntersectionChartJacobianWitnessQuadric_pderiv_eval
          x j i k)
  have hdetmap : ev Mpoly.det =
      ((tripleCompleteIntersectionChartJacobianEvaluationBaseMatrix p q x j).updateCol
        2 (fun k => if k = i then x j else 0)).det := by
    rw [RingHom.map_det]
    exact congrArg Matrix.det hM
  have hcol : (fun k => if k = i then x j else 0) =
      x j • (Pi.single i 1) := by
    funext k
    by_cases hki : k = i
    · subst k
      simp
    · simp [hki]
  have hdetupdate :
      ((tripleCompleteIntersectionChartJacobianEvaluationBaseMatrix p q x j).updateCol
        2 (fun k => if k = i then x j else 0)).det =
      x j *
        ((tripleCompleteIntersectionChartJacobianEvaluationBaseMatrix p q x j).updateCol
          2 (Pi.single i 1)).det := by
    rw [hcol, Matrix.det_updateCol_smul]
  have hdetnonzero : ev Mpoly.det ≠ 0 := by
    rw [hdetmap, hdetupdate]
    exact mul_ne_zero hxj hdeti
  rw [tripleCompleteIntersectionChartJacobianPolynomial_eq_signed_minorMatrix]
  change ev ((-1 : MvPolynomial (Fin 4) K) ^ ((j : ℕ) + 3) * Mpoly.det) ≠ 0
  simp only [map_mul, map_pow, map_neg, map_one]
  exact mul_ne_zero (by simp) hdetnonzero

/-- The quadratic witness can be chosen over the ground field even when the
point and the tangent calculation live over a field extension.  Expanding an
extension-field witness in the monomial basis shows that one ground monomial
already has nonzero Jacobian evaluation. -/
theorem exists_ground_quadric_with_nonzero_chartJacobian_eval_of_fieldExtension_linearIndependent_derivatives
    {L : Type u} [Field L] [Algebra K L]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (j : Fin 4) (x : Fin 4 → L) (hxj : x j ≠ 0)
    (hderiv : LinearIndependent L
      ![(fun i : Fin 3 =>
          (pderiv (j.succAbove i) (p.map (algebraMap K L))).eval x),
        (fun i : Fin 3 =>
          (pderiv (j.succAbove i) (q.map (algebraMap K L))).eval x)]) :
    ∃ r : homogeneousSubmodule (Fin 4) K 2,
      (MvPolynomial.eval₂Hom (RingHom.id L) x)
          ((tripleCompleteIntersectionChartJacobianPolynomial p q r.1 j).map
            (algebraMap K L)) ≠ 0 := by
  let pL : MvPolynomial (Fin 4) L := p.map (algebraMap K L)
  let qL : MvPolynomial (Fin 4) L := q.map (algebraMap K L)
  obtain ⟨rL, hrL⟩ :=
    exists_quadric_with_nonzero_chartJacobian_eval_of_linearIndependent_derivatives
      pL qL j x hxj (by simpa [pL, qL] using hderiv)
  let ev : MvPolynomial (Fin 4) L →+* L := MvPolynomial.eval₂Hom (RingHom.id L) x
  let T : homogeneousSubmodule (Fin 4) L 2 →ₗ[L] L :=
    tripleCompleteIntersectionChartJacobianEvaluationLinearMapDegree
      2 pL qL j (MvPolynomial.aeval x)
  have hT : T rL ≠ 0 := by
    simpa [T, tripleCompleteIntersectionChartJacobianEvaluationLinearMapDegree,
      MvPolynomial.aeval_def, ev] using hrL
  let mon : Monomials (Fin 4) 2 → homogeneousSubmodule (Fin 4) L 2 :=
    fun m => ⟨monomial m.1 1, isHomogeneous_monomial 1 m.2⟩
  have hr_sum : ∑ m : Monomials (Fin 4) 2, rL.1.coeff m.1 • mon m = rL := by
    apply Subtype.ext
    simp only [mon, Submodule.coe_sum, Submodule.coe_smul]
    change ∑ m : Monomials (Fin 4) 2,
      rL.1.coeff m.1 • monomial m.1 1 = rL.1
    rw [show (fun m : Monomials (Fin 4) 2 =>
        rL.1.coeff m.1 • monomial m.1 (1 : L)) =
        fun m => monomial m.1 (rL.1.coeff m.1) by
      funext m
      rw [MvPolynomial.smul_monomial]
      simp]
    exact sum_monomial_coeff_eq rL.1 rL.2
  have hsome : ∃ m : Monomials (Fin 4) 2, T (mon m) ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hT
    rw [← hr_sum, map_sum]
    apply Finset.sum_eq_zero
    intro m hm
    rw [map_smul, hall m, smul_zero]
  obtain ⟨m, hm⟩ := hsome
  refine ⟨⟨monomial m.1 1, isHomogeneous_monomial 1 m.2⟩, ?_⟩
  have hmap :
      (tripleCompleteIntersectionChartJacobianPolynomial p q
        (monomial m.1 1) j).map (algebraMap K L) =
        tripleCompleteIntersectionChartJacobianPolynomial pL qL
          ((monomial m.1 1).map (algebraMap K L)) j := by
    simpa [pL, qL] using
      (tripleCompleteIntersectionChartJacobianPolynomial_map
        (algebraMap K L) p q (monomial m.1 1)
          hp hq (isHomogeneous_monomial 1 m.2) j)
  change ev ((tripleCompleteIntersectionChartJacobianPolynomial p q
    (monomial m.1 1) j).map (algebraMap K L)) ≠ 0
  rw [hmap]
  simpa [T, mon, tripleCompleteIntersectionChartJacobianEvaluationLinearMapDegree,
    MvPolynomial.aeval_def, ev] using hm

/-! ## Simultaneous selection over finite coefficient algebras -/

/-- A member of a prescribed degree-`d` linear system can be selected so that
all four chart Jacobians are units on finite coefficient algebras, provided
the restricted Jacobian functional is nonzero in every residue field.  The
argument is independent of the degrees of the first two equations. -/
theorem exists_mem_submodule_with_allChartJacobian_isUnit_of_maximalSpectraDegree
    {d : ℕ} [Infinite K]
    {A : Fin 4 → Type u} [∀ j, CommRing (A j)] [∀ j, Algebra K (A j)]
    [∀ j, Module.Finite K (A j)]
    (p q : MvPolynomial (Fin 4) K)
    (e : ∀ j, MvPolynomial (Fin 4) K →ₐ[K] A j)
    (W : Submodule K (homogeneousSubmodule (Fin 4) K d))
    (hnonzero : ∀ (j : Fin 4) (Q : MaximalSpectrum (A j)),
      tripleCompleteIntersectionChartJacobianEvaluationLinearMapDegree_restrict
        d p q j
        (MvPolynomial.aeval (tripleCompleteIntersectionResidueEvaluation (e j) Q))
        W ≠ 0) :
    ∃ r : W,
      ∀ j : Fin 4, IsUnit (e j
        (tripleCompleteIntersectionChartJacobianPolynomial p q r.1.1 j)) := by
  letI : ∀ j, IsArtinianRing (A j) := fun j => IsArtinianRing.of_finite K (A j)
  let eQ : ∀ z : Σ j, MaximalSpectrum (A j),
      MvPolynomial (Fin 4) K →ₐ[K] z.2.asIdeal.ResidueField :=
    fun z => MvPolynomial.aeval
      (tripleCompleteIntersectionResidueEvaluation (e z.1) z.2)
  let bad : ∀ z : Σ j, MaximalSpectrum (A j), Submodule K W := fun z =>
    (tripleCompleteIntersectionChartJacobianBadSubmoduleDegree
      d p q z.1 (eQ z) (⊥ : Ideal z.2.asIdeal.ResidueField)).comap W.subtype
  have hproper : ∀ z, bad z ≠ ⊤ := by
    intro z htop
    have hn := hnonzero z.1 z.2
    apply hn
    ext r
    have hmem : r ∈ bad z := by
      rw [htop]
      exact Submodule.mem_top
    change eQ z
      (tripleCompleteIntersectionChartJacobianPolynomial p q r.1.1 z.1) ∈
        (⊥ : Ideal z.2.asIdeal.ResidueField) at hmem
    simpa [tripleCompleteIntersectionChartJacobianEvaluationLinearMapDegree_restrict,
      tripleCompleteIntersectionChartJacobianEvaluationLinearMapDegree, eQ] using hmem
  obtain ⟨r, hr⟩ := exists_vector_avoiding_finite_submodules
    (V := W) bad hproper
  refine ⟨r, ?_⟩
  intro j
  by_contra hunit
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal
    (Ideal.span ({e j
      (tripleCompleteIntersectionChartJacobianPolynomial p q r.1.1 j)} : Set (A j)))
    (Ideal.span_singleton_ne_top hunit)
  let Q : MaximalSpectrum (A j) := ⟨M, hM⟩
  have haM : e j
      (tripleCompleteIntersectionChartJacobianPolynomial p q r.1.1 j) ∈ M :=
    hle (Ideal.subset_span (Set.mem_singleton _))
  have hzero : algebraMap (A j) Q.asIdeal.ResidueField
      (e j (tripleCompleteIntersectionChartJacobianPolynomial p q r.1.1 j)) = 0 :=
    Ideal.algebraMap_residueField_eq_zero.mpr haM
  have hzero' : eQ ⟨j, Q⟩
      (tripleCompleteIntersectionChartJacobianPolynomial p q r.1.1 j) = 0 := by
    rw [show eQ ⟨j, Q⟩ = MvPolynomial.aeval
      (tripleCompleteIntersectionResidueEvaluation (e j) Q) by rfl]
    rw [MvPolynomial.aeval_def]
    simpa [MvPolynomial.eval₂_map] using
      (tripleCompleteIntersectionResidueEvaluation_map_eval (e j) Q
        (tripleCompleteIntersectionChartJacobianPolynomial p q r.1.1 j)).symm.trans hzero
  have hmem : r ∈ bad ⟨j, Q⟩ := by
    change eQ ⟨j, Q⟩
      (tripleCompleteIntersectionChartJacobianPolynomial p q r.1.1 j) ∈
        (⊥ : Ideal Q.asIdeal.ResidueField)
    simpa [hzero']
  exact (hr ⟨j, Q⟩) hmem

/-- For the full quadratic system, smoothness of the cubic--quadric curve at
the residue point makes the pointwise Jacobian functional nonzero. -/
theorem tripleCompleteIntersectionChartJacobianBadSubmoduleDegree_two_ne_top_of_fieldExtension_linearIndependent_derivatives
    {L : Type u} [Field L] [Algebra K L]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (j : Fin 4) (x : Fin 4 → L) (hxj : x j ≠ 0)
    (hderiv : LinearIndependent L
      ![(fun i : Fin 3 =>
          (pderiv (j.succAbove i) (p.map (algebraMap K L))).eval x),
        (fun i : Fin 3 =>
          (pderiv (j.succAbove i) (q.map (algebraMap K L))).eval x)]) :
    tripleCompleteIntersectionChartJacobianBadSubmoduleDegree
      2 p q j (MvPolynomial.aeval x) (⊥ : Ideal L) ≠ ⊤ := by
  apply (tripleCompleteIntersectionChartJacobianBadSubmoduleDegree_ne_top_iff
    2 p q j (MvPolynomial.aeval x) (⊥ : Ideal L)).mpr
  obtain ⟨r, hr⟩ :=
    exists_ground_quadric_with_nonzero_chartJacobian_eval_of_fieldExtension_linearIndependent_derivatives
      p q hp hq j x hxj hderiv
  refine ⟨r, ?_⟩
  simpa [MvPolynomial.aeval_def] using hr

/-- Over four finite chart algebras, residue-field tangent independence
selects one ground-field quadric whose chart Jacobian is a unit everywhere.
This is the unconstrained quadratic Bertini selector; the constrained version
above replaces the tangent premise by nonvanishing on the chosen subsystem. -/
theorem exists_ground_quadric_with_allChartJacobian_isUnit_of_maximalSpectra
    [Infinite K]
    {A : Fin 4 → Type u} [∀ j, CommRing (A j)] [∀ j, Algebra K (A j)]
    [∀ j, Module.Finite K (A j)]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (e : ∀ j, MvPolynomial (Fin 4) K →ₐ[K] A j)
    (hcoord : ∀ (j : Fin 4) (Q : MaximalSpectrum (A j)),
      tripleCompleteIntersectionResidueEvaluation (e j) Q j ≠ 0)
    (hderiv : ∀ (j : Fin 4) (Q : MaximalSpectrum (A j)),
      LinearIndependent Q.asIdeal.ResidueField
        ![(fun i : Fin 3 =>
            (pderiv (j.succAbove i)
              (p.map (algebraMap K Q.asIdeal.ResidueField))).eval
                (tripleCompleteIntersectionResidueEvaluation (e j) Q)),
          (fun i : Fin 3 =>
            (pderiv (j.succAbove i)
              (q.map (algebraMap K Q.asIdeal.ResidueField))).eval
                (tripleCompleteIntersectionResidueEvaluation (e j) Q))]) :
    ∃ r : homogeneousSubmodule (Fin 4) K 2,
      ∀ j : Fin 4, IsUnit (e j
        (tripleCompleteIntersectionChartJacobianPolynomial p q r.1 j)) := by
  have hnonzero : ∀ (j : Fin 4) (Q : MaximalSpectrum (A j)),
      tripleCompleteIntersectionChartJacobianEvaluationLinearMapDegree_restrict
        2 p q j
        (MvPolynomial.aeval (tripleCompleteIntersectionResidueEvaluation (e j) Q))
        (⊤ : Submodule K (homogeneousSubmodule (Fin 4) K 2)) ≠ 0 := by
    intro j Q
    rw [tripleCompleteIntersectionChartJacobianEvaluationLinearMapDegree_restrict_ne_zero_iff]
    obtain ⟨r, hr⟩ :=
      exists_ground_quadric_with_nonzero_chartJacobian_eval_of_fieldExtension_linearIndependent_derivatives
        p q hp hq j (tripleCompleteIntersectionResidueEvaluation (e j) Q)
          (hcoord j Q) (hderiv j Q)
    refine ⟨⟨r, Submodule.mem_top⟩, ?_⟩
    simpa [MvPolynomial.aeval_def] using hr
  obtain ⟨r, hr⟩ :=
    exists_mem_submodule_with_allChartJacobian_isUnit_of_maximalSpectraDegree
      p q e (⊤ : Submodule K (homogeneousSubmodule (Fin 4) K 2)) hnonzero
  exact ⟨r.1, hr⟩

/-- Degree-two specialization to the system of quadrics vanishing on a
finite homogeneous coordinate algebra.  This is the finite base-locus
transversality selector needed in Voisin's degree-eight residual step. -/
theorem exists_quadric_in_restrictionKernel_with_allChartJacobian_isUnit_of_restrict_ne_zero
    [Infinite K]
    {B : Type u} [CommRing B] [Algebra K B]
    {A : Fin 4 → Type u} [∀ j, CommRing (A j)] [∀ j, Algebra K (A j)]
    [∀ j, Module.Finite K (A j)]
    (p q : MvPolynomial (Fin 4) K)
    (x : Fin 4 → B) (e : ∀ j, MvPolynomial (Fin 4) K →ₐ[K] A j)
    (hnonzero : ∀ (j : Fin 4) (Q : MaximalSpectrum (A j)),
      tripleCompleteIntersectionChartJacobianEvaluationLinearMapDegree_restrict
        2 p q j
        (MvPolynomial.aeval (tripleCompleteIntersectionResidueEvaluation (e j) Q))
        (LinearMap.ker (homogeneousSectionRestriction (K := K) x 2)) ≠ 0) :
    ∃ r : LinearMap.ker (homogeneousSectionRestriction (K := K) x 2),
      ∀ j : Fin 4, IsUnit (e j
        (tripleCompleteIntersectionChartJacobianPolynomial p q r.1.1 j)) := by
  exact
    exists_mem_submodule_with_allChartJacobian_isUnit_of_maximalSpectraDegree
      p q e (LinearMap.ker (homogeneousSectionRestriction (K := K) x 2)) hnonzero

end PfaffianDescent
