import PfaffianDescent.TripleCompleteIntersectionHilbert
import PfaffianDescent.HomogeneousQuotientMap
import PfaffianDescent.ProjectiveLinearSystem
import PfaffianDescent.GenericRegularSection
import PfaffianDescent.VoisinSectionRestriction
import PfaffianDescent.LinearMapImageFrame
import AllCharacteristics.AffineChartPresentation
import AllCharacteristics.ProjectiveChartBaseChange
import AllCharacteristics.JacobianLocalization
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.Data.Fin.VecNotation

/-!
# Jacobian criterion for projective three-equation intersections

On the normalized `j`-th chart of the intersection of three homogeneous
equations in `P³`, the four equations are the three original equations and
`X j - 1`.  Thus its square Jacobian is a directly checkable chartwise
criterion for the projective intersection to be étale over the coefficient
field.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

section

variable {K : Type u} [Field K] {a b c : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable local instance tripleCompleteIntersectionChartAlgebra
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous a) (hq : q.IsHomogeneous b) (hr : r.IsHomogeneous c)
    (j : Fin 4) :
    Algebra K (ChartRing (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr) j) :=
  (chartBaseMap (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr) j).toAlgebra

/-- The three equations together with the chart normalization. -/
noncomputable def tripleCompleteIntersectionChartRelations
    (p q r : MvPolynomial (Fin 4) K) (j : Fin 4) :
    Fin 4 → MvPolynomial (Fin 4) K :=
  ![p, q, r, X j - 1]

@[simp] theorem tripleCompleteIntersectionChartRelations_zero
    (p q r : MvPolynomial (Fin 4) K) (j : Fin 4) :
    tripleCompleteIntersectionChartRelations p q r j 0 = p := by
  simp [tripleCompleteIntersectionChartRelations]

@[simp] theorem tripleCompleteIntersectionChartRelations_one
    (p q r : MvPolynomial (Fin 4) K) (j : Fin 4) :
    tripleCompleteIntersectionChartRelations p q r j 1 = q := by
  simp [tripleCompleteIntersectionChartRelations]

@[simp] theorem tripleCompleteIntersectionChartRelations_two
    (p q r : MvPolynomial (Fin 4) K) (j : Fin 4) :
    tripleCompleteIntersectionChartRelations p q r j 2 = r := by
  simp [tripleCompleteIntersectionChartRelations]

@[simp] theorem tripleCompleteIntersectionChartRelations_three
    (p q r : MvPolynomial (Fin 4) K) (j : Fin 4) :
    tripleCompleteIntersectionChartRelations p q r j 3 = X j - 1 := by
  simp [tripleCompleteIntersectionChartRelations]

theorem range_tripleCompleteIntersectionChartRelations
    (p q r : MvPolynomial (Fin 4) K) (j : Fin 4) :
    Set.range (tripleCompleteIntersectionChartRelations p q r j) = {p, q, r, X j - 1} := by
  ext s
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp [tripleCompleteIntersectionChartRelations]
  · intro hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · exact ⟨0, by simp [tripleCompleteIntersectionChartRelations]⟩
    · exact ⟨1, by simp [tripleCompleteIntersectionChartRelations]⟩
    · exact ⟨2, by simp [tripleCompleteIntersectionChartRelations]⟩
    · exact ⟨3, by simp [tripleCompleteIntersectionChartRelations]⟩

theorem span_range_tripleCompleteIntersectionChartRelations
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous a) (hq : q.IsHomogeneous b) (hr : r.IsHomogeneous c)
    (j : Fin 4) :
    Ideal.span (Set.range (tripleCompleteIntersectionChartRelations p q r j)) =
      chartPresentationIdeal (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr) j := by
  rw [range_tripleCompleteIntersectionChartRelations]
  let A : Ideal (MvPolynomial (Fin 4) K) := Ideal.span {p, q, r}
  let B : Ideal (MvPolynomial (Fin 4) K) := Ideal.span {X j - 1}
  change Ideal.span {p, q, r, X j - 1} = A ⊔ B
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro s (rfl | rfl | rfl | rfl)
    · exact (show A ≤ A ⊔ B from le_sup_left) (by
        dsimp [A]
        exact Ideal.subset_span (by simp))
    · exact (show A ≤ A ⊔ B from le_sup_left) (by
        dsimp [A]
        exact Ideal.subset_span (by simp))
    · exact (show A ≤ A ⊔ B from le_sup_left) (by
        dsimp [A]
        exact Ideal.subset_span (by simp))
    · exact (show B ≤ A ⊔ B from le_sup_right) (by
        dsimp [B]
        exact Ideal.subset_span (by simp))
  · apply sup_le
    · apply Ideal.span_le.mpr
      intro s hs
      apply Ideal.subset_span
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs ⊢
      exact hs.elim Or.inl (fun h => h.elim
        (fun hq => Or.inr (Or.inl hq))
        (fun hr => Or.inr (Or.inr (Or.inl hr))))
    · apply Ideal.span_le.mpr
      intro s hs
      apply Ideal.subset_span
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs ⊢
      exact Or.inr (Or.inr (Or.inr hs))

/-- The square polynomial presentation is the actual normalized projective chart. -/
noncomputable def tripleCompleteIntersectionChartRelationsEquiv
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous a) (hq : q.IsHomogeneous b) (hr : r.IsHomogeneous c)
    (j : Fin 4) :
    (MvPolynomial (Fin 4) K ⧸
      Ideal.span (Set.range (tripleCompleteIntersectionChartRelations p q r j))) ≃ₐ[K]
        ChartRing (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr) j := by
  let e : (MvPolynomial (Fin 4) K ⧸
      Ideal.span (Set.range (tripleCompleteIntersectionChartRelations p q r j))) ≃+*
        ChartRing (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr) j :=
    (Ideal.quotEquivOfEq
      (span_range_tripleCompleteIntersectionChartRelations p q r hp hq hr j)).trans
      (chartPresentationEquiv (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr) j)
  exact
    { e with
      commutes' := by
        intro x
        change e (Ideal.Quotient.mk _ (C x)) =
          chartBaseMap (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr) j x
        simp only [e, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
          chartPresentationEquiv_mk, eval₂_C] }

@[simp] theorem tripleCompleteIntersectionChartRelationsEquiv_mk
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous a) (hq : q.IsHomogeneous b) (hr : r.IsHomogeneous c)
    (j : Fin 4) (s : MvPolynomial (Fin 4) K) :
    tripleCompleteIntersectionChartRelationsEquiv p q r hp hq hr j
      (Ideal.Quotient.mk _ s) =
      s.eval₂ (chartBaseMap (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr) j)
        (chartCoordinate (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr) j) := by
  change chartPresentationEquiv (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr) j
      (Ideal.quotEquivOfEq
        (span_range_tripleCompleteIntersectionChartRelations p q r hp hq hr j)
        (Ideal.Quotient.mk _ s)) = _
  rw [Ideal.quotEquivOfEq_mk, chartPresentationEquiv_mk]

/-- The Jacobian matrix of the three equations and the chart normalization. -/
noncomputable def tripleCompleteIntersectionChartJacobiMatrix
    (p q r : MvPolynomial (Fin 4) K) (j : Fin 4) :
    Matrix (Fin 4) (Fin 4) (MvPolynomial (Fin 4) K) :=
  fun i l => pderiv i (tripleCompleteIntersectionChartRelations p q r j l)

@[simp] theorem tripleCompleteIntersectionChartJacobiMatrix_apply
    (p q r : MvPolynomial (Fin 4) K) (j i l : Fin 4) :
    tripleCompleteIntersectionChartJacobiMatrix p q r j i l =
      pderiv i (tripleCompleteIntersectionChartRelations p q r j l) := rfl

@[simp] theorem tripleCompleteIntersectionChartJacobiMatrix_zero
    (p q r : MvPolynomial (Fin 4) K) (j i : Fin 4) :
    tripleCompleteIntersectionChartJacobiMatrix p q r j i 0 = pderiv i p := by
  simp [tripleCompleteIntersectionChartJacobiMatrix]

@[simp] theorem tripleCompleteIntersectionChartJacobiMatrix_one
    (p q r : MvPolynomial (Fin 4) K) (j i : Fin 4) :
    tripleCompleteIntersectionChartJacobiMatrix p q r j i 1 = pderiv i q := by
  simp [tripleCompleteIntersectionChartJacobiMatrix]

@[simp] theorem tripleCompleteIntersectionChartJacobiMatrix_two
    (p q r : MvPolynomial (Fin 4) K) (j i : Fin 4) :
    tripleCompleteIntersectionChartJacobiMatrix p q r j i 2 = pderiv i r := by
  simp [tripleCompleteIntersectionChartJacobiMatrix]

@[simp] theorem tripleCompleteIntersectionChartJacobiMatrix_three
    (p q r : MvPolynomial (Fin 4) K) (j i : Fin 4) :
    tripleCompleteIntersectionChartJacobiMatrix p q r j i 3 =
      if i = j then 1 else 0 := by
  classical
  by_cases hij : i = j
  · subst j
    simp [tripleCompleteIntersectionChartJacobiMatrix]
  · simp [tripleCompleteIntersectionChartJacobiMatrix, hij]

/-- The polynomial determinant of the chartwise square Jacobian. -/
noncomputable def tripleCompleteIntersectionChartJacobianPolynomial
    (p q r : MvPolynomial (Fin 4) K) (j : Fin 4) : MvPolynomial (Fin 4) K :=
  (tripleCompleteIntersectionChartJacobiMatrix p q r j).det

/- The third equation occurs in one column of the square Jacobian matrix.  Thus
   its determinant is additive and coefficient-linear in that equation.  These
   identities are the algebraic reason that a fixed-chart Jacobian failure is a
   linear condition on a moving third-cubic system. -/
theorem tripleCompleteIntersectionChartJacobianPolynomial_add_right
    (p q r s : MvPolynomial (Fin 4) K) (j : Fin 4) :
    tripleCompleteIntersectionChartJacobianPolynomial p q (r + s) j =
      tripleCompleteIntersectionChartJacobianPolynomial p q r j +
        tripleCompleteIntersectionChartJacobianPolynomial p q s j := by
  let M := tripleCompleteIntersectionChartJacobiMatrix p q 0 j
  have hMr :
      tripleCompleteIntersectionChartJacobiMatrix p q r j =
        M.updateCol 2 (fun i => pderiv i r) := by
    ext i l
    fin_cases l <;>
      simp [M, tripleCompleteIntersectionChartJacobiMatrix,
        tripleCompleteIntersectionChartRelations]
  have hMs :
      tripleCompleteIntersectionChartJacobiMatrix p q s j =
        M.updateCol 2 (fun i => pderiv i s) := by
    ext i l
    fin_cases l <;>
      simp [M, tripleCompleteIntersectionChartJacobiMatrix,
        tripleCompleteIntersectionChartRelations]
  have hMrs :
      tripleCompleteIntersectionChartJacobiMatrix p q (r + s) j =
        M.updateCol 2 (fun i => pderiv i r + pderiv i s) := by
    ext i l
    fin_cases l <;>
      simp [M, tripleCompleteIntersectionChartJacobiMatrix,
        tripleCompleteIntersectionChartRelations]
  unfold tripleCompleteIntersectionChartJacobianPolynomial
  rw [hMrs]
  change (M.updateCol 2 ((fun i => pderiv i r) + (fun i => pderiv i s))).det = _
  rw [Matrix.det_updateCol_add, ← hMr, ← hMs]

theorem tripleCompleteIntersectionChartJacobianPolynomial_C_mul_right
    (a : K) (p q r : MvPolynomial (Fin 4) K) (j : Fin 4) :
    tripleCompleteIntersectionChartJacobianPolynomial p q (C a * r) j =
      C a * tripleCompleteIntersectionChartJacobianPolynomial p q r j := by
  let M := tripleCompleteIntersectionChartJacobiMatrix p q 0 j
  have hMr :
      tripleCompleteIntersectionChartJacobiMatrix p q r j =
        M.updateCol 2 (fun i => pderiv i r) := by
    ext i l
    fin_cases l <;>
      simp [M, tripleCompleteIntersectionChartJacobiMatrix,
        tripleCompleteIntersectionChartRelations]
  have hMars :
      tripleCompleteIntersectionChartJacobiMatrix p q (C a * r) j =
        M.updateCol 2 ((C a : MvPolynomial (Fin 4) K) • fun i => pderiv i r) := by
    ext i l
    fin_cases l <;>
      simp [M, tripleCompleteIntersectionChartJacobiMatrix,
        tripleCompleteIntersectionChartRelations]
  unfold tripleCompleteIntersectionChartJacobianPolynomial
  rw [hMars]
  change (M.updateCol 2 ((C a : MvPolynomial (Fin 4) K) •
    (fun i => pderiv i r))).det = _
  have hdet := Matrix.det_updateCol_smul M 2
    (C a : MvPolynomial (Fin 4) K) (fun i => pderiv i r)
  rw [hdet, ← hMr]

theorem tripleCompleteIntersectionChartJacobianPolynomial_zero_right
    (p q : MvPolynomial (Fin 4) K) (j : Fin 4) :
    tripleCompleteIntersectionChartJacobianPolynomial p q 0 j = 0 := by
  unfold tripleCompleteIntersectionChartJacobianPolynomial
  apply Matrix.det_eq_zero_of_column_eq_zero 2
  intro i
  simp [tripleCompleteIntersectionChartJacobiMatrix,
    tripleCompleteIntersectionChartRelations]

/-- At a fixed affine point the chart Jacobian depends on the third equation
only through its first derivatives there.  This is the local comparison used
when a cubic from a constrained linear system is required to have the same
first jet as a known transverse witness. -/
theorem tripleCompleteIntersectionChartJacobianPolynomial_eval_eq_of_pderiv_eval_eq
    (p q r s : MvPolynomial (Fin 4) K) (j : Fin 4) (x : Fin 4 → K)
    (h : ∀ i : Fin 4, (pderiv i r).eval x = (pderiv i s).eval x) :
    (tripleCompleteIntersectionChartJacobianPolynomial p q r j).eval x =
      (tripleCompleteIntersectionChartJacobianPolynomial p q s j).eval x := by
  let ev : MvPolynomial (Fin 4) K →+* K := MvPolynomial.eval₂Hom (RingHom.id K) x
  change ev (tripleCompleteIntersectionChartJacobiMatrix p q r j).det =
    ev (tripleCompleteIntersectionChartJacobiMatrix p q s j).det
  rw [RingHom.map_det, RingHom.map_det]
  congr 1
  ext i l
  fin_cases l
  · simp [tripleCompleteIntersectionChartJacobiMatrix,
      tripleCompleteIntersectionChartRelations]
  · simp [tripleCompleteIntersectionChartJacobiMatrix,
      tripleCompleteIntersectionChartRelations]
  · simpa [tripleCompleteIntersectionChartJacobiMatrix,
      tripleCompleteIntersectionChartRelations, ev] using h i
  · simp [tripleCompleteIntersectionChartJacobiMatrix,
      tripleCompleteIntersectionChartRelations]

/- Evaluating the polynomial Jacobian at one fixed coefficient-chart point
   turns its dependence on the moving third cubic into a genuine linear map.
   This is the form used by pointwise Bertini: the Jacobian-bad locus cut out
   by a prime of the target chart is a linear subspace of the cubic system. -/
noncomputable def tripleCompleteIntersectionChartJacobianEvaluationLinearMap
    {A : Type u} [CommRing A] [Algebra K A]
    (p q : MvPolynomial (Fin 4) K) (j : Fin 4)
    (e : MvPolynomial (Fin 4) K →ₐ[K] A) :
    homogeneousSubmodule (Fin 4) K 3 →ₗ[K] A :=
  { toFun := fun r => e (tripleCompleteIntersectionChartJacobianPolynomial p q r.1 j)
    map_add' := by
      intro r s
      rw [Submodule.coe_add, tripleCompleteIntersectionChartJacobianPolynomial_add_right,
        map_add]
    map_smul' := by
      intro a r
      rw [Submodule.coe_smul]
      change e (tripleCompleteIntersectionChartJacobianPolynomial p q (a • r.1) j) = _
      rw [show (a • r.1 : MvPolynomial (Fin 4) K) = C a * r.1 by
        simp [smul_eq_C_mul], tripleCompleteIntersectionChartJacobianPolynomial_C_mul_right]
      simp [Algebra.smul_def] }

/-- The chart-Jacobian evaluation map restricted to a prescribed cubic
system.  Unlike the stronger first-jet-surjectivity map, nonzeroness of this
map is exactly the pointwise condition needed for a system member to be
transverse at the chosen residue point. -/
noncomputable def tripleCompleteIntersectionChartJacobianEvaluationLinearMap_restrict
    {A : Type u} [CommRing A] [Algebra K A]
    (p q : MvPolynomial (Fin 4) K) (j : Fin 4)
    (e : MvPolynomial (Fin 4) K →ₐ[K] A)
    (W : Submodule K (homogeneousSubmodule (Fin 4) K 3)) : W →ₗ[K] A :=
  (tripleCompleteIntersectionChartJacobianEvaluationLinearMap p q j e).comp W.subtype

/-- Nonzeroness of the restricted Jacobian evaluation linear map is
equivalent to the exact pointwise Bertini witness in the prescribed system. -/
theorem tripleCompleteIntersectionChartJacobianEvaluationLinearMap_restrict_ne_zero_iff
    {A : Type u} [CommRing A] [Algebra K A]
    (p q : MvPolynomial (Fin 4) K) (j : Fin 4)
    (e : MvPolynomial (Fin 4) K →ₐ[K] A)
    (W : Submodule K (homogeneousSubmodule (Fin 4) K 3)) :
    tripleCompleteIntersectionChartJacobianEvaluationLinearMap_restrict p q j e W ≠ 0 ↔
      ∃ r : W, e (tripleCompleteIntersectionChartJacobianPolynomial p q r.1.1 j) ≠ 0 := by
  constructor
  · intro hmap
    by_contra h
    push_neg at h
    apply hmap
    ext r
    exact h r
  · rintro ⟨r, hr⟩ hmap
    apply hr
    have hvalue := congrArg (fun f : W →ₗ[K] A => f r) hmap
    simpa [tripleCompleteIntersectionChartJacobianEvaluationLinearMap_restrict,
      tripleCompleteIntersectionChartJacobianEvaluationLinearMap] using hvalue

noncomputable def tripleCompleteIntersectionChartJacobianBadSubmodule
    {A : Type u} [CommRing A] [Algebra K A]
    (p q : MvPolynomial (Fin 4) K) (j : Fin 4)
    (e : MvPolynomial (Fin 4) K →ₐ[K] A) (Q : Ideal A) :
    Submodule K (homogeneousSubmodule (Fin 4) K 3) :=
  (Q.restrictScalars K).comap
    (tripleCompleteIntersectionChartJacobianEvaluationLinearMap p q j e)

theorem mem_tripleCompleteIntersectionChartJacobianBadSubmodule_iff
    {A : Type u} [CommRing A] [Algebra K A]
    (p q : MvPolynomial (Fin 4) K) (j : Fin 4)
    (e : MvPolynomial (Fin 4) K →ₐ[K] A) (Q : Ideal A)
    (r : homogeneousSubmodule (Fin 4) K 3) :
    r ∈ tripleCompleteIntersectionChartJacobianBadSubmodule p q j e Q ↔
      e (tripleCompleteIntersectionChartJacobianPolynomial p q r.1 j) ∈ Q := Iff.rfl

/- The bad submodule is proper exactly when one cubic in the system gives a
   nonvanishing Jacobian at the chosen quotient point.  This turns a concrete
   pointwise Jacobian witness into the proper-linear-subspace hypothesis used
   by the generic-section avoidance API. -/
theorem tripleCompleteIntersectionChartJacobianBadSubmodule_ne_top_iff
    {A : Type u} [CommRing A] [Algebra K A]
    (p q : MvPolynomial (Fin 4) K) (j : Fin 4)
    (e : MvPolynomial (Fin 4) K →ₐ[K] A) (Q : Ideal A) :
    tripleCompleteIntersectionChartJacobianBadSubmodule p q j e Q ≠ ⊤ ↔
      ∃ r : homogeneousSubmodule (Fin 4) K 3,
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
    have hm : r ∈ tripleCompleteIntersectionChartJacobianBadSubmodule p q j e Q := by
      rw [htop]
      exact Submodule.mem_top
    exact hr ((mem_tripleCompleteIntersectionChartJacobianBadSubmodule_iff
      p q j e Q r).mp hm)

/- The normalization row has a single nonzero entry.  Expanding along that
   row therefore identifies the square chart Jacobian with the corresponding
   three-by-three minor of the derivatives of `p`, `q`, and `r`.  This is the
   concrete form used when checking a chosen chart in the transversality
   argument. -/
theorem tripleCompleteIntersectionChartJacobianPolynomial_eq_signed_minor
    (p q r : MvPolynomial (Fin 4) K) (j : Fin 4) :
    tripleCompleteIntersectionChartJacobianPolynomial p q r j =
      (-1 : MvPolynomial (Fin 4) K) ^ ((j : ℕ) + 3) *
        ((tripleCompleteIntersectionChartJacobiMatrix p q r j).submatrix
          j.succAbove (3 : Fin 4).succAbove).det := by
  classical
  unfold tripleCompleteIntersectionChartJacobianPolynomial
  rw [Matrix.det_succ_column _ (3 : Fin 4)]
  simp only [tripleCompleteIntersectionChartJacobiMatrix_three]
  fin_cases j <;>
    simp [Fin.sum_univ_succ, Matrix.submatrix_apply, pow_succ]

theorem tripleCompleteIntersectionChartJacobianPolynomial_isUnit_iff_minor_isUnit
    (p q r : MvPolynomial (Fin 4) K) (j : Fin 4) :
    IsUnit (tripleCompleteIntersectionChartJacobianPolynomial p q r j) ↔
      IsUnit (((tripleCompleteIntersectionChartJacobiMatrix p q r j).submatrix
        j.succAbove (3 : Fin 4).succAbove).det) := by
  rw [tripleCompleteIntersectionChartJacobianPolynomial_eq_signed_minor]
  simp

/- A vector in the kernel of a three-by-four matrix controls all maximal
   minors.  If one coordinate of the vector is nonzero and the complementary
   minor vanishes, then the matrix has rank below three, so every maximal
   minor vanishes.  The explicit proof avoids any rank or finrank conversion. -/
theorem all_maximalMinors_zero_of_mulVec_eq_zero
    (A : Matrix (Fin 3) (Fin 4) K) (x : Fin 4 → K) (j : Fin 4)
    (hxj : x j ≠ 0) (hAx : A.mulVec x = 0)
    (hj : (A.submatrix id j.succAbove).det = 0) :
    ∀ k : Fin 4, (A.submatrix id k.succAbove).det = 0 := by
  intro k
  have h0 : A 0 0 * x 0 + A 0 1 * x 1 + A 0 2 * x 2 + A 0 3 * x 3 = 0 := by
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, add_assoc] using
      congrFun hAx (0 : Fin 3)
  have h1 : A 1 0 * x 0 + A 1 1 * x 1 + A 1 2 * x 2 + A 1 3 * x 3 = 0 := by
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, add_assoc] using
      congrFun hAx (1 : Fin 3)
  have h2 : A 2 0 * x 0 + A 2 1 * x 1 + A 2 2 * x 2 + A 2 3 * x 3 = 0 := by
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, add_assoc] using
      congrFun hAx (2 : Fin 3)
  let Δ : Fin 4 → Fin 4 → Fin 4 → K := fun a b c =>
    A 0 a * A 1 b * A 2 c - A 0 a * A 1 c * A 2 b -
      A 0 b * A 1 a * A 2 c + A 0 b * A 1 c * A 2 a +
      A 0 c * A 1 a * A 2 b - A 0 c * A 1 b * A 2 a
  have hcross (l m : Fin 4) :
      x 0 * Δ 0 l m + x 1 * Δ 1 l m + x 2 * Δ 2 l m + x 3 * Δ 3 l m = 0 := by
    dsimp [Δ]
    linear_combination
      h0 * (A 1 l * A 2 m - A 1 m * A 2 l) +
      h1 * (-(A 0 l * A 2 m - A 0 m * A 2 l)) +
      h2 * (A 0 l * A 1 m - A 0 m * A 1 l)
  fin_cases j <;> fin_cases k
  all_goals
    simp at hxj
    simp [Matrix.det_fin_three, Matrix.submatrix_apply, Fin.succAbove] at hj ⊢
  · exact hj
  · apply (mul_eq_zero.mp ?_).resolve_left hxj
    have hc := hcross 2 3
    dsimp [Δ] at hc
    linear_combination hc - (x 1) * hj
  · apply (mul_eq_zero.mp ?_).resolve_left hxj
    have hc := hcross 1 3
    dsimp [Δ] at hc
    linear_combination hc + (x 2) * hj
  · apply (mul_eq_zero.mp ?_).resolve_left hxj
    have hc := hcross 1 2
    dsimp [Δ] at hc
    linear_combination hc - (x 3) * hj
  · apply (mul_eq_zero.mp ?_).resolve_left hxj
    have hc := hcross 2 3
    dsimp [Δ] at hc
    linear_combination hc - (x 0) * hj
  · exact hj
  · apply (mul_eq_zero.mp ?_).resolve_left hxj
    have hc := hcross 0 3
    dsimp [Δ] at hc
    linear_combination (-1) * hc - (x 2) * hj
  · apply (mul_eq_zero.mp ?_).resolve_left hxj
    have hc := hcross 0 2
    dsimp [Δ] at hc
    linear_combination (-1) * hc + (x 3) * hj
  · apply (mul_eq_zero.mp ?_).resolve_left hxj
    have hc := hcross 1 3
    dsimp [Δ] at hc
    linear_combination (-1) * hc + (x 0) * hj
  · apply (mul_eq_zero.mp ?_).resolve_left hxj
    have hc := hcross 0 3
    dsimp [Δ] at hc
    linear_combination (-1) * hc - (x 1) * hj
  · exact hj
  · apply (mul_eq_zero.mp ?_).resolve_left hxj
    have hc := hcross 0 1
    dsimp [Δ] at hc
    linear_combination hc - (x 3) * hj
  · apply (mul_eq_zero.mp ?_).resolve_left hxj
    have hc := hcross 1 2
    dsimp [Δ] at hc
    linear_combination hc - (x 0) * hj
  · apply (mul_eq_zero.mp ?_).resolve_left hxj
    have hc := hcross 0 2
    dsimp [Δ] at hc
    linear_combination hc + (x 1) * hj
  · apply (mul_eq_zero.mp ?_).resolve_left hxj
    have hc := hcross 0 1
    dsimp [Δ] at hc
    linear_combination hc - (x 2) * hj
  · exact hj

/- The minor can be written without the auxiliary normalization equation: its
   rows are the three variables other than the chart coordinate, and its
   columns are the derivatives of `p`, `q`, and `r`. -/
noncomputable def tripleCompleteIntersectionChartJacobianMinorMatrix
    (p q r : MvPolynomial (Fin 4) K) (j : Fin 4) :
    Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 4) K) :=
  fun i l => pderiv (j.succAbove i) (![p, q, r] l)

private theorem tripleCompleteIntersectionChartJacobianMinorMatrix_entry_isHomogeneous
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3) (hr : r.IsHomogeneous 3)
    (j : Fin 4) (i l : Fin 3) :
    (tripleCompleteIntersectionChartJacobianMinorMatrix p q r j i l).IsHomogeneous 2 := by
  fin_cases l
  · simpa [tripleCompleteIntersectionChartJacobianMinorMatrix] using hp.pderiv
  · simpa [tripleCompleteIntersectionChartJacobianMinorMatrix] using hq.pderiv
  · simpa [tripleCompleteIntersectionChartJacobianMinorMatrix] using hr.pderiv

theorem tripleCompleteIntersectionChartJacobianMinorMatrix_det_isHomogeneous
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3) (hr : r.IsHomogeneous 3)
    (j : Fin 4) :
    ((tripleCompleteIntersectionChartJacobianMinorMatrix p q r j).det).IsHomogeneous 6 := by
  let M := tripleCompleteIntersectionChartJacobianMinorMatrix p q r j
  have h00 := tripleCompleteIntersectionChartJacobianMinorMatrix_entry_isHomogeneous
    p q r hp hq hr j 0 0
  have h01 := tripleCompleteIntersectionChartJacobianMinorMatrix_entry_isHomogeneous
    p q r hp hq hr j 0 1
  have h02 := tripleCompleteIntersectionChartJacobianMinorMatrix_entry_isHomogeneous
    p q r hp hq hr j 0 2
  have h10 := tripleCompleteIntersectionChartJacobianMinorMatrix_entry_isHomogeneous
    p q r hp hq hr j 1 0
  have h11 := tripleCompleteIntersectionChartJacobianMinorMatrix_entry_isHomogeneous
    p q r hp hq hr j 1 1
  have h12 := tripleCompleteIntersectionChartJacobianMinorMatrix_entry_isHomogeneous
    p q r hp hq hr j 1 2
  have h20 := tripleCompleteIntersectionChartJacobianMinorMatrix_entry_isHomogeneous
    p q r hp hq hr j 2 0
  have h21 := tripleCompleteIntersectionChartJacobianMinorMatrix_entry_isHomogeneous
    p q r hp hq hr j 2 1
  have h22 := tripleCompleteIntersectionChartJacobianMinorMatrix_entry_isHomogeneous
    p q r hp hq hr j 2 2
  have h000 : (M 0 0 * M 1 1 * M 2 2).IsHomogeneous 6 := by
    exact (h00.mul h11).mul h22
  have h001 : (M 0 0 * M 1 2 * M 2 1).IsHomogeneous 6 := by
    exact (h00.mul h12).mul h21
  have h010 : (M 0 1 * M 1 0 * M 2 2).IsHomogeneous 6 := by
    exact (h01.mul h10).mul h22
  have h011 : (M 0 1 * M 1 2 * M 2 0).IsHomogeneous 6 := by
    exact (h01.mul h12).mul h20
  have h100 : (M 0 2 * M 1 0 * M 2 1).IsHomogeneous 6 := by
    exact (h02.mul h10).mul h21
  have h101 : (M 0 2 * M 1 1 * M 2 0).IsHomogeneous 6 := by
    exact (h02.mul h11).mul h20
  rw [Matrix.det_fin_three]
  exact (((((h000.sub h001).sub h010).add h011).add h100).sub h101)

theorem tripleCompleteIntersectionChartJacobian_submatrix_eq_minorMatrix
    (p q r : MvPolynomial (Fin 4) K) (j : Fin 4) :
    (tripleCompleteIntersectionChartJacobiMatrix p q r j).submatrix
        j.succAbove (3 : Fin 4).succAbove =
      tripleCompleteIntersectionChartJacobianMinorMatrix p q r j := by
  ext i l
  fin_cases l <;>
    simp [tripleCompleteIntersectionChartJacobiMatrix,
      tripleCompleteIntersectionChartJacobianMinorMatrix,
      tripleCompleteIntersectionChartRelations, Fin.succAbove]

theorem tripleCompleteIntersectionChartJacobianPolynomial_eq_signed_minorMatrix
    (p q r : MvPolynomial (Fin 4) K) (j : Fin 4) :
    tripleCompleteIntersectionChartJacobianPolynomial p q r j =
      (-1 : MvPolynomial (Fin 4) K) ^ ((j : ℕ) + 3) *
        (tripleCompleteIntersectionChartJacobianMinorMatrix p q r j).det := by
  rw [tripleCompleteIntersectionChartJacobianPolynomial_eq_signed_minor,
    tripleCompleteIntersectionChartJacobian_submatrix_eq_minorMatrix]

/- The evaluated full derivative matrix has the three cubics as rows and all
   four projective coordinates as columns.  Its complementary maximal minors
   are the transposes of the chart Jacobian minor matrices. -/
noncomputable def tripleCompleteIntersectionFullJacobianEvaluationMatrix
    (p q r : MvPolynomial (Fin 4) K) (x : Fin 4 → K) :
    Matrix (Fin 3) (Fin 4) K := fun l i =>
  (pderiv i (![p, q, r] l)).eval x

/- Euler's identity puts the homogeneous coordinate vector in the kernel of
   the evaluated derivative matrix at a common zero of the three cubics. -/
theorem tripleCompleteIntersectionFullJacobianEvaluationMatrix_mulVec_eq_zero
    (p q r : MvPolynomial (Fin 4) K) (x : Fin 4 → K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3) (hr : r.IsHomogeneous 3)
    (hpx : p.eval x = 0) (hqx : q.eval x = 0) (hrx : r.eval x = 0) :
    (tripleCompleteIntersectionFullJacobianEvaluationMatrix p q r x).mulVec x = 0 := by
  funext l
  fin_cases l
  · have h := congrArg (MvPolynomial.eval x) hp.sum_X_mul_pderiv
    simpa [tripleCompleteIntersectionFullJacobianEvaluationMatrix,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ, add_assoc, mul_comm, hpx] using h
  · have h := congrArg (MvPolynomial.eval x) hq.sum_X_mul_pderiv
    simpa [tripleCompleteIntersectionFullJacobianEvaluationMatrix,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ, add_assoc, mul_comm, hqx] using h
  · have h := congrArg (MvPolynomial.eval x) hr.sum_X_mul_pderiv
    simpa [tripleCompleteIntersectionFullJacobianEvaluationMatrix,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ, add_assoc, mul_comm, hrx] using h

theorem tripleCompleteIntersectionFullJacobianEvaluationMatrix_minor_det_eq
    (p q r : MvPolynomial (Fin 4) K) (x : Fin 4 → K) (j : Fin 4) :
    ((tripleCompleteIntersectionFullJacobianEvaluationMatrix p q r x).submatrix
        id j.succAbove).det =
      ((tripleCompleteIntersectionChartJacobianMinorMatrix p q r j).det).eval x := by
  let ev : MvPolynomial (Fin 4) K →+* K :=
    MvPolynomial.eval₂Hom (RingHom.id K) x
  let M := tripleCompleteIntersectionChartJacobianMinorMatrix p q r j
  have hmat :
      (tripleCompleteIntersectionFullJacobianEvaluationMatrix p q r x).submatrix
          id j.succAbove =
        (ev.mapMatrix M).transpose := by
    ext l i
    simp [tripleCompleteIntersectionFullJacobianEvaluationMatrix, M,
      tripleCompleteIntersectionChartJacobianMinorMatrix, ev]
  rw [hmat, Matrix.det_transpose, ← RingHom.map_det]
  rfl

theorem tripleCompleteIntersectionChartJacobianPolynomial_eval_eq_zero_iff_fullMinor
    (p q r : MvPolynomial (Fin 4) K) (x : Fin 4 → K) (j : Fin 4) :
    (tripleCompleteIntersectionChartJacobianPolynomial p q r j).eval x = 0 ↔
      ((tripleCompleteIntersectionFullJacobianEvaluationMatrix p q r x).submatrix
        id j.succAbove).det = 0 := by
  rw [tripleCompleteIntersectionFullJacobianEvaluationMatrix_minor_det_eq]
  rw [tripleCompleteIntersectionChartJacobianPolynomial_eq_signed_minorMatrix]
  simp

/- At a common projective zero of three homogeneous cubics, failure of the
   Jacobian criterion in any affine chart containing the point is equivalent
   to simultaneous vanishing of all four maximal derivative minors.  This is
   the algebraic bridge from the global all-minor incidence locus to the four
   chartwise Jacobian conditions. -/
theorem all_tripleCompleteIntersectionChartJacobianPolynomial_eval_eq_zero_of_one
    (p q r : MvPolynomial (Fin 4) K) (x : Fin 4 → K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3) (hr : r.IsHomogeneous 3)
    (hpx : p.eval x = 0) (hqx : q.eval x = 0) (hrx : r.eval x = 0)
    (j : Fin 4) (hxj : x j ≠ 0)
    (hj : (tripleCompleteIntersectionChartJacobianPolynomial p q r j).eval x = 0) :
    ∀ k : Fin 4,
      (tripleCompleteIntersectionChartJacobianPolynomial p q r k).eval x = 0 := by
  let A := tripleCompleteIntersectionFullJacobianEvaluationMatrix p q r x
  have hAx : A.mulVec x = 0 :=
    tripleCompleteIntersectionFullJacobianEvaluationMatrix_mulVec_eq_zero
      p q r x hp hq hr hpx hqx hrx
  have hminorj : (A.submatrix id j.succAbove).det = 0 :=
    (tripleCompleteIntersectionChartJacobianPolynomial_eval_eq_zero_iff_fullMinor
      p q r x j).mp hj
  have hall := all_maximalMinors_zero_of_mulVec_eq_zero A x j hxj hAx hminorj
  intro k
  exact (tripleCompleteIntersectionChartJacobianPolynomial_eval_eq_zero_iff_fullMinor
    p q r x k).mpr (hall k)

theorem tripleCompleteIntersectionChartJacobianPolynomial_isHomogeneous
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3) (hr : r.IsHomogeneous 3)
    (j : Fin 4) :
    (tripleCompleteIntersectionChartJacobianPolynomial p q r j).IsHomogeneous 6 := by
  rw [tripleCompleteIntersectionChartJacobianPolynomial_eq_signed_minorMatrix]
  have hsign : ((-1 : MvPolynomial (Fin 4) K) ^ ((j : ℕ) + 3)).IsHomogeneous 0 := by
    simpa only [map_neg, map_one, Nat.zero_mul] using
      (MvPolynomial.isHomogeneous_C (Fin 4) (-1 : K)).pow ((j : ℕ) + 3)
  have hdet := tripleCompleteIntersectionChartJacobianMinorMatrix_det_isHomogeneous
    p q r hp hq hr j
  simpa only [zero_add] using hsign.mul hdet

/- The Jacobian construction itself is a linear map from the cubic
   coefficient space to the sextic forms.  This packages both the coefficient
   linearity and the degree-six ambient equation needed by a projective linear
   system argument. -/
noncomputable def tripleCompleteIntersectionChartJacobianHomogeneousLinearMap
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3) (j : Fin 4) :
    homogeneousSubmodule (Fin 4) K 3 →ₗ[K] homogeneousSubmodule (Fin 4) K 6 :=
  { toFun := fun r =>
      ⟨tripleCompleteIntersectionChartJacobianPolynomial p q r.1 j,
        tripleCompleteIntersectionChartJacobianPolynomial_isHomogeneous
          p q r.1 hp hq (by exact r.2) j⟩
    map_add' := by
      intro r s
      apply Subtype.ext
      change tripleCompleteIntersectionChartJacobianPolynomial p q (r.1 + s.1) j =
        tripleCompleteIntersectionChartJacobianPolynomial p q r.1 j +
          tripleCompleteIntersectionChartJacobianPolynomial p q s.1 j
      rw [tripleCompleteIntersectionChartJacobianPolynomial_add_right]
    map_smul' := by
      intro a r
      apply Subtype.ext
      change tripleCompleteIntersectionChartJacobianPolynomial p q (a • r.1) j =
        a • tripleCompleteIntersectionChartJacobianPolynomial p q r.1 j
      rw [show (a • r.1 : MvPolynomial (Fin 4) K) = C a * r.1 by
        simp [smul_eq_C_mul], tripleCompleteIntersectionChartJacobianPolynomial_C_mul_right]
      exact (MvPolynomial.smul_eq_C_mul
        (tripleCompleteIntersectionChartJacobianPolynomial p q r.1 j) a).symm }

@[simp] theorem tripleCompleteIntersectionChartJacobianHomogeneousLinearMap_apply
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3) (j : Fin 4)
    (r : homogeneousSubmodule (Fin 4) K 3) :
    (tripleCompleteIntersectionChartJacobianHomogeneousLinearMap p q hp hq j r).1 =
      tripleCompleteIntersectionChartJacobianPolynomial p q r.1 j := rfl

/-- The Jacobian-polynomial map restricted to a prescribed third-cubic
system.  For Voisin this system is the kernel of restriction to the completed
degree-sixteen datum. -/
noncomputable def tripleCompleteIntersectionChartJacobianHomogeneousLinearMap_restrict
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3) (j : Fin 4)
    (W : Submodule K (homogeneousSubmodule (Fin 4) K 3)) :
    W →ₗ[K] homogeneousSubmodule (Fin 4) K 6 :=
  (tripleCompleteIntersectionChartJacobianHomogeneousLinearMap p q hp hq j).comp W.subtype

@[simp] theorem tripleCompleteIntersectionChartJacobianHomogeneousLinearMap_restrict_apply
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3) (j : Fin 4)
    (W : Submodule K (homogeneousSubmodule (Fin 4) K 3)) (r : W) :
    (tripleCompleteIntersectionChartJacobianHomogeneousLinearMap_restrict p q hp hq j W r).1 =
      tripleCompleteIntersectionChartJacobianPolynomial p q r.1.1 j := rfl

theorem tripleCompleteIntersectionChartJacobianMinorMatrix_det_map
    {K L : Type u} [Field K] [Field L]
    (f : K →+* L) (p q r : MvPolynomial (Fin 4) K) (j : Fin 4) :
    ((tripleCompleteIntersectionChartJacobianMinorMatrix p q r j).det).map f =
      (tripleCompleteIntersectionChartJacobianMinorMatrix (p.map f) (q.map f)
        (r.map f) j).det := by
  rw [RingHom.map_det]
  congr 1
  ext i l
  fin_cases l <;>
    simp [tripleCompleteIntersectionChartJacobianMinorMatrix,
      MvPolynomial.pderiv_map]

/-- The projective chart Jacobian only uses derivatives in the three affine
coordinates of that chart.  Consequently equality of those three first-jet
coordinates is sufficient for equality of the Jacobian value. -/
theorem tripleCompleteIntersectionChartJacobianPolynomial_eval_eq_of_chart_pderiv_eval_eq
    (p q r s : MvPolynomial (Fin 4) K) (j : Fin 4) (x : Fin 4 → K)
    (h : ∀ i : Fin 3,
      (pderiv (j.succAbove i) r).eval x =
        (pderiv (j.succAbove i) s).eval x) :
    (tripleCompleteIntersectionChartJacobianPolynomial p q r j).eval x =
      (tripleCompleteIntersectionChartJacobianPolynomial p q s j).eval x := by
  let ev : MvPolynomial (Fin 4) K →+* K := MvPolynomial.eval₂Hom (RingHom.id K) x
  change ev (tripleCompleteIntersectionChartJacobianPolynomial p q r j) =
    ev (tripleCompleteIntersectionChartJacobianPolynomial p q s j)
  have hdet :
      ev ((tripleCompleteIntersectionChartJacobianMinorMatrix p q r j).det) =
        ev ((tripleCompleteIntersectionChartJacobianMinorMatrix p q s j).det) := by
    rw [RingHom.map_det, RingHom.map_det]
    apply congrArg Matrix.det
    ext i l
    fin_cases l
    · simp [tripleCompleteIntersectionChartJacobianMinorMatrix]
    · simp [tripleCompleteIntersectionChartJacobianMinorMatrix]
    · simpa [tripleCompleteIntersectionChartJacobianMinorMatrix, ev] using h i
  rw [tripleCompleteIntersectionChartJacobianPolynomial_eq_signed_minorMatrix,
    tripleCompleteIntersectionChartJacobianPolynomial_eq_signed_minorMatrix]
  simp only [map_mul, map_pow, map_neg, map_one]
  rw [hdet]

/- Coefficient change commutes with the ordinary ideal generated by the three
   equations.  This small lemma is the ideal-theoretic part of transporting a
   chart Jacobian to a generic coefficient field. -/
theorem tripleCompleteIntersectionIdeal_map
    {K L : Type u} [Field K] [Field L]
    (f : K →+* L) (p q r : MvPolynomial (Fin 4) K) :
    (tripleCompleteIntersectionIdeal p q r).map (MvPolynomial.map f) =
      tripleCompleteIntersectionIdeal (p.map f) (q.map f) (r.map f) := by
  rw [tripleCompleteIntersectionIdeal, Ideal.map_span]
  congr 1
  ext z
  constructor
  · rintro ⟨w, (rfl | rfl | rfl), rfl⟩
    · simp
    · simp
    · simp
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro (rfl | rfl | rfl)
    · exact ⟨p, by simp, rfl⟩
    · exact ⟨q, by simp, rfl⟩
    · exact ⟨r, by simp, rfl⟩

/- The polynomial determinant itself commutes with coefficient change.  The
   proof is entrywise: `pderiv_map` handles the first three equations and the
   chart-normalizing equation has coefficients only in the prime field. -/
theorem tripleCompleteIntersectionChartJacobianPolynomial_map
    {K L : Type u} [Field K] [Field L]
    (f : K →+* L)
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous a) (hq : q.IsHomogeneous b) (hr : r.IsHomogeneous c)
    (j : Fin 4) :
    (tripleCompleteIntersectionChartJacobianPolynomial p q r j).map f =
      tripleCompleteIntersectionChartJacobianPolynomial (p.map f) (q.map f) (r.map f) j := by
  unfold tripleCompleteIntersectionChartJacobianPolynomial
  rw [RingHom.map_det]
  congr 1
  apply Matrix.ext
  intro i l
  change (MvPolynomial.map f)
      (pderiv i (tripleCompleteIntersectionChartRelations p q r j l)) =
    pderiv i (tripleCompleteIntersectionChartRelations (p.map f) (q.map f) (r.map f) j l)
  fin_cases l
  · simp [tripleCompleteIntersectionChartRelations, MvPolynomial.pderiv_map]
  · simp [tripleCompleteIntersectionChartRelations, MvPolynomial.pderiv_map]
  · simp [tripleCompleteIntersectionChartRelations, MvPolynomial.pderiv_map]
  · change (MvPolynomial.map f) (pderiv i (X j - 1)) = pderiv i (X j - 1)
    rw [(pderiv i).map_sub, (pderiv i).map_sub, pderiv_X, pderiv_X]
    simp only [map_sub, map_zero]
    by_cases h : j = i <;> simp [h]

theorem tripleCompleteIntersectionChartJacobianHomogeneousLinearMap_map
    {K L : Type u} [Field K] [Field L]
    (f : K →+* L)
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3) (j : Fin 4)
    (r : homogeneousSubmodule (Fin 4) K 3) :
    (tripleCompleteIntersectionChartJacobianHomogeneousLinearMap p q hp hq j r).1.map f =
      (tripleCompleteIntersectionChartJacobianHomogeneousLinearMap
        (p.map f) (q.map f) (hp.map f) (hq.map f) j
        ⟨r.1.map f, by exact r.2.map f⟩).1 := by
  simpa only [tripleCompleteIntersectionChartJacobianHomogeneousLinearMap_apply] using
    (tripleCompleteIntersectionChartJacobianPolynomial_map f p q r.1 hp hq
      (by exact r.2) j)

/- The image of the Jacobian map is finite-dimensional.  Choosing the
   canonical finite basis of its range gives an independent sextic frame,
   which is the coefficient system to be used by projective incidence. -/
noncomputable def tripleCompleteIntersectionChartJacobianImageBasis
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3) (j : Fin 4) :
    Module.Basis
      (Fin (Module.finrank K
        (LinearMap.range (tripleCompleteIntersectionChartJacobianHomogeneousLinearMap
          p q hp hq j)))) K
      (LinearMap.range (tripleCompleteIntersectionChartJacobianHomogeneousLinearMap
        p q hp hq j)) := by
  letI : Module.Free K
      (LinearMap.range (tripleCompleteIntersectionChartJacobianHomogeneousLinearMap
        p q hp hq j)) := Module.Free.of_divisionRing K
      (LinearMap.range (tripleCompleteIntersectionChartJacobianHomogeneousLinearMap
        p q hp hq j))
  exact Module.finBasis K
    (LinearMap.range (tripleCompleteIntersectionChartJacobianHomogeneousLinearMap
      p q hp hq j))

noncomputable def tripleCompleteIntersectionChartJacobianImageFrame
    {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3) (j : Fin 4)
    (b : Module.Basis (Fin n) K
      (LinearMap.range (tripleCompleteIntersectionChartJacobianHomogeneousLinearMap
        p q hp hq j))) :
    Fin n → homogeneousSubmodule (Fin 4) K 6 :=
  fun i => (b i :
    homogeneousSubmodule (Fin 4) K 6)

private theorem linearIndependent_rangeBasis_coe
    {V W : Type u} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W]
    (L : V →ₗ[K] W) {n : ℕ}
    (b : Module.Basis (Fin n) K (LinearMap.range L)) :
    LinearIndependent K (fun i => (b i : W)) := by
  have hker : (LinearMap.range L).subtype.ker = ⊥ :=
    LinearMap.ker_eq_bot_of_injective (LinearMap.range L).subtype_injective
  change LinearIndependent K ((LinearMap.range L).subtype ∘ b)
  exact b.linearIndependent.map' (LinearMap.range L).subtype hker

theorem tripleCompleteIntersectionChartJacobianImageFrame_linearIndependent
    {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3) (j : Fin 4)
    (b : Module.Basis (Fin n) K
      (LinearMap.range (tripleCompleteIntersectionChartJacobianHomogeneousLinearMap
        p q hp hq j))) :
    LinearIndependent K (tripleCompleteIntersectionChartJacobianImageFrame p q hp hq j b) := by
  change LinearIndependent K (fun i => (b i : homogeneousSubmodule (Fin 4) K 6))
  exact linearIndependent_rangeBasis_coe
    (tripleCompleteIntersectionChartJacobianHomogeneousLinearMap p q hp hq j) b

/- Choose cubic lifts of a basis of the Jacobian image.  Passing to the image
   before choosing coordinates removes the kernel generated, in particular,
   by repetitions of the first two defining cubics. -/
noncomputable def tripleCompleteIntersectionChartJacobianImageLiftFrame
    {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3) (j : Fin 4)
    (b : Module.Basis (Fin n) K
      (LinearMap.range (tripleCompleteIntersectionChartJacobianHomogeneousLinearMap
        p q hp hq j))) :
    Fin n → homogeneousSubmodule (Fin 4) K 3 :=
  fun i => Classical.choose (b i).property

@[simp] theorem tripleCompleteIntersectionChartJacobianImageLiftFrame_map
    {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3) (j : Fin 4)
    (b : Module.Basis (Fin n) K
      (LinearMap.range (tripleCompleteIntersectionChartJacobianHomogeneousLinearMap
        p q hp hq j))) (i : Fin n) :
    tripleCompleteIntersectionChartJacobianHomogeneousLinearMap p q hp hq j
        (tripleCompleteIntersectionChartJacobianImageLiftFrame p q hp hq j b i) =
      tripleCompleteIntersectionChartJacobianImageFrame p q hp hq j b i := by
  exact Classical.choose_spec (b i).property

/- The lifted cubics are independent because their Jacobian images form a
   basis.  Hence they and the image sextics share one honest projective
   coordinate space. -/
theorem tripleCompleteIntersectionChartJacobianImageLiftFrame_linearIndependent
    {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3) (j : Fin 4)
    (b : Module.Basis (Fin n) K
      (LinearMap.range (tripleCompleteIntersectionChartJacobianHomogeneousLinearMap
        p q hp hq j))) :
    LinearIndependent K
      (tripleCompleteIntersectionChartJacobianImageLiftFrame p q hp hq j b) := by
  apply LinearIndependent.of_comp
    (tripleCompleteIntersectionChartJacobianHomogeneousLinearMap p q hp hq j)
  convert tripleCompleteIntersectionChartJacobianImageFrame_linearIndependent
    p q hp hq j b using 1
  funext i
  exact tripleCompleteIntersectionChartJacobianImageLiftFrame_map p q hp hq j b i

theorem tripleCompleteIntersectionChartJacobianImageFrame_represents
    {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3) (j : Fin 4)
    (b : Module.Basis (Fin n) K
      (LinearMap.range (tripleCompleteIntersectionChartJacobianHomogeneousLinearMap
        p q hp hq j)))
    (r : homogeneousSubmodule (Fin 4) K 3) :
    ∃ c : Fin n → K,
      ∑ i, c i • tripleCompleteIntersectionChartJacobianImageFrame p q hp hq j b i =
        tripleCompleteIntersectionChartJacobianHomogeneousLinearMap p q hp hq j r := by
  let L := tripleCompleteIntersectionChartJacobianHomogeneousLinearMap p q hp hq j
  let y : LinearMap.range L := ⟨L r, ⟨r, rfl⟩⟩
  refine ⟨b.repr y, ?_⟩
  have h := b.sum_repr y
  have h' := congrArg (fun z : LinearMap.range L =>
    (z : homogeneousSubmodule (Fin 4) K 6)) h
  change ∑ i, (b.repr y) i •
      tripleCompleteIntersectionChartJacobianImageFrame p q hp hq j b i = L r
  simpa only [L, tripleCompleteIntersectionChartJacobianImageFrame, y,
    Submodule.coe_sum, Submodule.coe_smul] using h'

/- A nonvanishing Jacobian value for any cubic in the image is already
   witnessed by one member of the canonical image frame.  This is the
   coefficient-level witness needed to turn pointwise Jacobian nonvanishing
   into a projective-system incidence witness. -/
theorem tripleCompleteIntersectionChartJacobianImageFrame_exists_not_mem_ideal_of_exists_not_mem
    {A : Type u} [CommRing A] [Algebra K A]
    {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3) (j : Fin 4)
    (b : Module.Basis (Fin n) K
      (LinearMap.range (tripleCompleteIntersectionChartJacobianHomogeneousLinearMap
        p q hp hq j)))
    (e : MvPolynomial (Fin 4) K →ₐ[K] A) (Q : Ideal A)
    (hgood : ∃ r : homogeneousSubmodule (Fin 4) K 3,
      e ((tripleCompleteIntersectionChartJacobianHomogeneousLinearMap
        p q hp hq j r).1) ∉ Q) :
    ∃ i : Fin n,
      e ((tripleCompleteIntersectionChartJacobianImageFrame p q hp hq j b i).1) ∉ Q := by
  classical
  by_contra hframe
  push_neg at hframe
  obtain ⟨r, hr⟩ := hgood
  obtain ⟨c, hc⟩ := tripleCompleteIntersectionChartJacobianImageFrame_represents
    p q hp hq j b r
  have heq := congrArg
    (fun z : homogeneousSubmodule (Fin 4) K 6 => e z.1) hc
  have heq' :
      ∑ i, (algebraMap K A) (c i) *
        e (tripleCompleteIntersectionChartJacobianImageFrame
          p q hp hq j b i).1 =
        e (tripleCompleteIntersectionChartJacobianHomogeneousLinearMap
          p q hp hq j r).1 := by
    have heq0 :
        ∑ i, e ((algebraMap K (MvPolynomial (Fin 4) K)) (c i)) *
            e (tripleCompleteIntersectionChartJacobianImageFrame
              p q hp hq j b i).1 =
          e (tripleCompleteIntersectionChartJacobianHomogeneousLinearMap
            p q hp hq j r).1 := by
      simpa only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_mul,
        map_add, MvPolynomial.map_C, Algebra.smul_def] using heq
    calc
      ∑ i, (algebraMap K A) (c i) *
          e (tripleCompleteIntersectionChartJacobianImageFrame
            p q hp hq j b i).1 =
          ∑ i, e ((algebraMap K (MvPolynomial (Fin 4) K)) (c i)) *
            e (tripleCompleteIntersectionChartJacobianImageFrame
              p q hp hq j b i).1 := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [e.commutes]
      _ = _ := heq0
  have hmem : e ((tripleCompleteIntersectionChartJacobianHomogeneousLinearMap
      p q hp hq j r).1) ∈ Q := by
    rw [← heq']
    apply Q.sum_mem
    intro i hi
    apply Q.mul_mem_left ((algebraMap K A) (c i))
    exact hframe i
  exact hr hmem

/- Properness of the pointwise Jacobian bad submodule is already detected by
   one member of the canonical finite image frame.  This is the form used by
   the projective-system argument: a proper linear condition at a moving
   chart point gives an explicitly indexed projective section outside it. -/
theorem tripleCompleteIntersectionChartJacobianImageFrame_exists_not_mem_of_badSubmodule_ne_top
    {A : Type u} [CommRing A] [Algebra K A]
    {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3) (j : Fin 4)
    (b : Module.Basis (Fin n) K
      (LinearMap.range (tripleCompleteIntersectionChartJacobianHomogeneousLinearMap
        p q hp hq j)))
    (e : MvPolynomial (Fin 4) K →ₐ[K] A) (Q : Ideal A)
    (hbad : tripleCompleteIntersectionChartJacobianBadSubmodule p q j e Q ≠ ⊤) :
    ∃ i : Fin n,
      e ((tripleCompleteIntersectionChartJacobianImageFrame p q hp hq j b i).1) ∉ Q := by
  obtain ⟨r, hr⟩ :=
    (tripleCompleteIntersectionChartJacobianBadSubmodule_ne_top_iff
      p q j e Q).mp hbad
  exact tripleCompleteIntersectionChartJacobianImageFrame_exists_not_mem_ideal_of_exists_not_mem
    p q hp hq j b e Q ⟨r, hr⟩

/- The finite image frame gives an exact criterion for properness: the
   pointwise bad submodule is proper precisely when at least one frame section
   is nonvanishing modulo the target ideal. -/
theorem tripleCompleteIntersectionChartJacobianBadSubmodule_ne_top_iff_exists_imageFrame_not_mem
    {A : Type u} [CommRing A] [Algebra K A]
    {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3) (j : Fin 4)
    (b : Module.Basis (Fin n) K
      (LinearMap.range (tripleCompleteIntersectionChartJacobianHomogeneousLinearMap
        p q hp hq j)))
    (e : MvPolynomial (Fin 4) K →ₐ[K] A) (Q : Ideal A) :
    tripleCompleteIntersectionChartJacobianBadSubmodule p q j e Q ≠ ⊤ ↔
      ∃ i : Fin n,
        e ((tripleCompleteIntersectionChartJacobianImageFrame p q hp hq j b i).1) ∉ Q := by
  constructor
  · exact tripleCompleteIntersectionChartJacobianImageFrame_exists_not_mem_of_badSubmodule_ne_top
      p q hp hq j b e Q
  · rintro ⟨i, hi⟩
    apply (tripleCompleteIntersectionChartJacobianBadSubmodule_ne_top_iff
      p q j e Q).mpr
    obtain ⟨r, hr⟩ := (b i).property
    refine ⟨r, ?_⟩
    have hpoly0 := congrArg
      (fun z : homogeneousSubmodule (Fin 4) K 6 => z.1) hr
    have hpoly :
        tripleCompleteIntersectionChartJacobianPolynomial p q r.1 j =
          (tripleCompleteIntersectionChartJacobianImageFrame p q hp hq j b i).1 := by
      simpa only [tripleCompleteIntersectionChartJacobianHomogeneousLinearMap_apply,
        tripleCompleteIntersectionChartJacobianImageFrame] using hpoly0
    simpa only [hpoly] using hi

/- A finite collection of pointwise proper Jacobian conditions can be avoided
   by one cubic.  This is the finite-union step in the Bertini argument, with
   the target rings and ideals allowed to vary from point to point. -/
theorem exists_cubic_avoiding_finite_tripleCompleteIntersectionChartJacobian_badSubmodules
    {ι : Type*} [Finite ι] [Infinite K]
    {A : ι → Type u} [∀ i, CommRing (A i)] [∀ i, Algebra K (A i)]
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3) (j : Fin 4)
    (e : ∀ i, MvPolynomial (Fin 4) K →ₐ[K] A i)
    (Q : ∀ i, Ideal (A i))
    (hproper : ∀ i,
      tripleCompleteIntersectionChartJacobianBadSubmodule p q j (e i) (Q i) ≠ ⊤) :
    ∃ r : homogeneousSubmodule (Fin 4) K 3,
      ∀ i, e i (tripleCompleteIntersectionChartJacobianPolynomial p q r.1 j) ∉ Q i := by
  let bad : ∀ i : ι, Submodule K (homogeneousSubmodule (Fin 4) K 3) := fun i =>
    tripleCompleteIntersectionChartJacobianBadSubmodule p q j (e i) (Q i)
  have hbad : ∀ i, bad i ≠ ⊤ := by
    intro i
    exact hproper i
  obtain ⟨r, hr⟩ := exists_vector_avoiding_finite_submodules bad hbad
  refine ⟨r, ?_⟩
  intro i
  have hrnot : r ∉ bad i := hr i
  exact (not_congr (mem_tripleCompleteIntersectionChartJacobianBadSubmodule_iff
    p q j (e i) (Q i) r)).mp hrnot

/- The same finite-union argument can cover all four affine charts at once.
   This is the finite chart bookkeeping needed when a transversality witness is
   checked at finitely many moving points: the target algebra and ideal may
   vary with both the chart and the point. -/
theorem exists_cubic_avoiding_finite_allChart_tripleCompleteIntersectionChartJacobian_badSubmodules
    {ι : Type*} [Finite ι] [Infinite K]
    {A : Fin 4 × ι → Type u}
    [∀ z, CommRing (A z)] [∀ z, Algebra K (A z)]
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3)
    (e : ∀ z, MvPolynomial (Fin 4) K →ₐ[K] A z)
    (Q : ∀ z, Ideal (A z))
    (hproper : ∀ z,
      tripleCompleteIntersectionChartJacobianBadSubmodule p q z.1 (e z) (Q z) ≠ ⊤) :
    ∃ r : homogeneousSubmodule (Fin 4) K 3,
      ∀ (j : Fin 4) (i : ι),
        e (j, i) (tripleCompleteIntersectionChartJacobianPolynomial p q r.1 j) ∉
          Q (j, i) := by
  let bad : (Fin 4 × ι) → Submodule K (homogeneousSubmodule (Fin 4) K 3) :=
    fun z => tripleCompleteIntersectionChartJacobianBadSubmodule p q z.1
      (e z) (Q z)
  have hbad : ∀ z, bad z ≠ ⊤ := by
    intro z
    exact hproper z
  obtain ⟨r, hr⟩ := exists_vector_avoiding_finite_submodules bad hbad
  refine ⟨r, ?_⟩
  intro j i
  have hrnot : r ∉ bad (j, i) := hr (j, i)
  exact (not_congr (mem_tripleCompleteIntersectionChartJacobianBadSubmodule_iff
    p q j (e (j, i)) (Q (j, i)) r)).mp hrnot

/- A pointwise Jacobian witness.  In chart `j`, if the first two derivative
   columns admit a nonzero cofactor after replacing the third column by a
   coordinate vector, the cubic below supplies that third column explicitly.
   This is the local calculation used when turning a cotangent-space
   independence statement into a genuine transverse third cubic. -/
noncomputable def tripleCompleteIntersectionChartJacobianWitnessCubic
    (x : Fin 4 → K) (j : Fin 4) (i : Fin 3) : MvPolynomial (Fin 4) K :=
  (X (j.succAbove i) - C (x (j.succAbove i) / x j) * X j) * X j * X j

theorem tripleCompleteIntersectionChartJacobianWitnessCubic_isHomogeneous
    (x : Fin 4 → K) (j : Fin 4) (i : Fin 3) :
    (tripleCompleteIntersectionChartJacobianWitnessCubic x j i).IsHomogeneous 3 := by
  unfold tripleCompleteIntersectionChartJacobianWitnessCubic
  have hlin : (X (j.succAbove i) - C (x (j.succAbove i) / x j) * X j).IsHomogeneous 1 := by
    apply IsHomogeneous.sub
    · exact MvPolynomial.isHomogeneous_X _ _
    · exact (MvPolynomial.isHomogeneous_C _ _).mul (MvPolynomial.isHomogeneous_X _ _)
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    ((hlin.mul (MvPolynomial.isHomogeneous_X _ _)).mul
      (MvPolynomial.isHomogeneous_X _ _))

theorem tripleCompleteIntersectionChartJacobianWitnessCubic_pderiv_eval
    (x : Fin 4 → K) (j : Fin 4) (i k : Fin 3) :
    (pderiv (j.succAbove k)
      (tripleCompleteIntersectionChartJacobianWitnessCubic x j i)).eval x =
      if k = i then x j ^ 2 else 0 := by
  unfold tripleCompleteIntersectionChartJacobianWitnessCubic
  rw [pderiv_mul]
  rw [pderiv_mul]
  rw [(pderiv (j.succAbove k)).map_sub]
  simp only [pderiv_mul, pderiv_X, pderiv_C, eval_add, eval_sub, eval_mul,
    map_zero, map_one, eval_X, eval_C]
  by_cases hki : k = i
  · subst k
    simp [pow_two]
  · simp [hki]

noncomputable def tripleCompleteIntersectionChartJacobianEvaluationBaseMatrix
    (p q : MvPolynomial (Fin 4) K) (x : Fin 4 → K) (j : Fin 4) :
    Matrix (Fin 3) (Fin 3) K := fun i l =>
      match l with
      | 0 => (pderiv (j.succAbove i) p).eval x
      | 1 => (pderiv (j.succAbove i) q).eval x
      | 2 => 0

def tripleCompleteIntersectionChartJacobianPairMatrix
    (u v : Fin 3 → K) : Matrix (Fin 3) (Fin 3) K := fun row col =>
  match col with
  | 0 => u row
  | 1 => v row
  | 2 => 0

theorem exists_nonzero_updateCol_single_of_linearIndependent_pair
    (u v : Fin 3 → K) (h : LinearIndependent K ![u, v]) :
    ∃ i : Fin 3,
      ((tripleCompleteIntersectionChartJacobianPairMatrix u v).updateCol
        2 (Pi.single i 1)).det ≠ 0 := by
  obtain ⟨w, hw⟩ := exists_linearIndependent_snoc_of_lt_finrank h (by simp)
  let cols : Fin 3 → (Fin 3 → K) := Fin.snoc ![u, v] w
  let M : Matrix (Fin 3) (Fin 3) K := fun row col => cols col row
  have hcols : LinearIndependent K M.col := by
    change LinearIndependent K cols
    exact hw
  have hunit : IsUnit M := (Matrix.linearIndependent_cols_iff_isUnit).mp hcols
  have hdetunit : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).mp hunit
  have hdetw :
      ((tripleCompleteIntersectionChartJacobianPairMatrix u v).updateCol 2 w).det ≠ 0 := by
    change M.det ≠ 0
    exact hdetunit.ne_zero
  by_contra hall
  push_neg at hall
  have hwdecomp : w = ∑ i : Fin 3, w i • (Pi.single i 1) := by
    exact pi_eq_sum_univ' w
  let L : (Fin 3 → K) →ₗ[K] K := (LinearMap.proj 2).comp
    (Matrix.cramer (tripleCompleteIntersectionChartJacobianPairMatrix u v))
  have hLzero : L w = 0 := by
    rw [hwdecomp, map_sum]
    apply Finset.sum_eq_zero
    intro i hi
    rw [map_smul]
    change w i •
      ((tripleCompleteIntersectionChartJacobianPairMatrix u v).updateCol
        2 (Pi.single i 1)).det = 0
    rw [hall i]
    simp
  exact hdetw (by simpa [L, Matrix.cramer_apply] using hLzero)

theorem exists_nonzero_chartJacobian_minor_of_linearIndependent_derivatives
    (p q : MvPolynomial (Fin 4) K) (x : Fin 4 → K) (j : Fin 4)
    (h : LinearIndependent K
      ![(fun i : Fin 3 => (pderiv (j.succAbove i) p).eval x),
        (fun i : Fin 3 => (pderiv (j.succAbove i) q).eval x)]) :
    ∃ i : Fin 3,
      ((tripleCompleteIntersectionChartJacobianEvaluationBaseMatrix p q x j).updateCol
        2 (Pi.single i 1)).det ≠ 0 := by
  let u : Fin 3 → K := fun i => (pderiv (j.succAbove i) p).eval x
  let v : Fin 3 → K := fun i => (pderiv (j.succAbove i) q).eval x
  have huv : LinearIndependent K ![u, v] := by
    simpa [u, v] using h
  obtain ⟨i, hi⟩ := exists_nonzero_updateCol_single_of_linearIndependent_pair u v huv
  refine ⟨i, ?_⟩
  change ((tripleCompleteIntersectionChartJacobianPairMatrix u v).updateCol
    2 (Pi.single i 1)).det ≠ 0
  exact hi

theorem exists_cubic_with_nonzero_chartJacobian_eval_of_minor
    (p q : MvPolynomial (Fin 4) K) (_hp : p.IsHomogeneous 3) (_hq : q.IsHomogeneous 3)
    (j : Fin 4) (x : Fin 4 → K) (hxj : x j ≠ 0)
    (hdet : ∃ i : Fin 3,
      ((tripleCompleteIntersectionChartJacobianEvaluationBaseMatrix p q x j).updateCol
        2 (Pi.single i 1)).det ≠ 0) :
    ∃ r : homogeneousSubmodule (Fin 4) K 3,
      (tripleCompleteIntersectionChartJacobianPolynomial p q r.1 j).eval x ≠ 0 := by
  obtain ⟨i, hdeti⟩ := hdet
  let rpoly := tripleCompleteIntersectionChartJacobianWitnessCubic x j i
  have hrpoly : rpoly.IsHomogeneous 3 := by
    dsimp [rpoly]
    exact tripleCompleteIntersectionChartJacobianWitnessCubic_isHomogeneous x j i
  refine ⟨⟨rpoly, hrpoly⟩, ?_⟩
  let ev : MvPolynomial (Fin 4) K →+* K := MvPolynomial.eval₂Hom (RingHom.id K) x
  let Mpoly := tripleCompleteIntersectionChartJacobianMinorMatrix p q rpoly j
  have hM : ev.mapMatrix Mpoly =
      (tripleCompleteIntersectionChartJacobianEvaluationBaseMatrix p q x j).updateCol
        2 (fun k => if k = i then x j ^ 2 else 0) := by
    ext k l
    fin_cases l
    · simp [Mpoly, tripleCompleteIntersectionChartJacobianMinorMatrix,
        tripleCompleteIntersectionChartJacobianEvaluationBaseMatrix, ev]
    · simp [Mpoly, tripleCompleteIntersectionChartJacobianMinorMatrix,
        tripleCompleteIntersectionChartJacobianEvaluationBaseMatrix, ev]
    · simp [Mpoly, tripleCompleteIntersectionChartJacobianMinorMatrix,
        tripleCompleteIntersectionChartJacobianEvaluationBaseMatrix, ev]
      simpa [rpoly, ev] using
        (tripleCompleteIntersectionChartJacobianWitnessCubic_pderiv_eval x j i k)
  have hdetmap : ev (Mpoly.det) =
      ((tripleCompleteIntersectionChartJacobianEvaluationBaseMatrix p q x j).updateCol
        2 (fun k => if k = i then x j ^ 2 else 0)).det := by
    rw [RingHom.map_det]
    exact congrArg Matrix.det hM
  have hcol : (fun k => if k = i then x j ^ 2 else 0) =
      x j ^ 2 • (Pi.single i 1) := by
    funext k
    by_cases hki : k = i
    · subst k
      simp
    · simp [hki]
  have hdetupdate :
      ((tripleCompleteIntersectionChartJacobianEvaluationBaseMatrix p q x j).updateCol
        2 (fun k => if k = i then x j ^ 2 else 0)).det =
      x j ^ 2 * ((tripleCompleteIntersectionChartJacobianEvaluationBaseMatrix p q x j).updateCol
        2 (Pi.single i 1)).det := by
    rw [hcol, Matrix.det_updateCol_smul]
  have hdetnonzero : (ev Mpoly.det) ≠ 0 := by
    rw [hdetmap, hdetupdate]
    exact mul_ne_zero (pow_ne_zero 2 hxj) hdeti
  rw [tripleCompleteIntersectionChartJacobianPolynomial_eq_signed_minorMatrix]
  change ev ((-1 : MvPolynomial (Fin 4) K) ^ ((j : ℕ) + 3) * Mpoly.det) ≠ 0
  simp only [map_mul, map_pow, map_neg, map_one]
  exact mul_ne_zero (by simp) hdetnonzero

theorem exists_cubic_with_nonzero_chartJacobian_eval_of_linearIndependent_derivatives
    (p q : MvPolynomial (Fin 4) K) (_hp : p.IsHomogeneous 3) (_hq : q.IsHomogeneous 3)
    (j : Fin 4) (x : Fin 4 → K) (hxj : x j ≠ 0)
    (hderiv : LinearIndependent K
      ![(fun i : Fin 3 => (pderiv (j.succAbove i) p).eval x),
        (fun i : Fin 3 => (pderiv (j.succAbove i) q).eval x)]) :
    ∃ r : homogeneousSubmodule (Fin 4) K 3,
      (tripleCompleteIntersectionChartJacobianPolynomial p q r.1 j).eval x ≠ 0 := by
  obtain ⟨i, hi⟩ :=
    exists_nonzero_chartJacobian_minor_of_linearIndependent_derivatives p q x j hderiv
  exact exists_cubic_with_nonzero_chartJacobian_eval_of_minor
    p q _hp _hq j x hxj ⟨i, hi⟩

theorem exists_cubic_nonzero_chartJacobian_eval_of_finite_linearIndependent_derivatives
    {ι : Type*} [Finite ι] [Infinite K]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3)
    (x : Fin 4 × ι → Fin 4 → K)
    (hcoord : ∀ (j : Fin 4) (i : ι), x (j, i) j ≠ 0)
    (hderiv : ∀ (j : Fin 4) (i : ι), LinearIndependent K
      ![(fun k : Fin 3 => (pderiv (j.succAbove k) p).eval (x (j, i))),
        (fun k : Fin 3 => (pderiv (j.succAbove k) q).eval (x (j, i)))]) :
    ∃ r : homogeneousSubmodule (Fin 4) K 3,
      ∀ (j : Fin 4) (i : ι),
        (tripleCompleteIntersectionChartJacobianPolynomial p q r.1 j).eval
          (x (j, i)) ≠ 0 := by
  let e : ∀ z : Fin 4 × ι, MvPolynomial (Fin 4) K →ₐ[K] K :=
    fun z => MvPolynomial.aeval (x z)
  let Q : ∀ _z : Fin 4 × ι, Ideal K := fun _ => ⊥
  have hproper : ∀ z,
      tripleCompleteIntersectionChartJacobianBadSubmodule p q z.1 (e z) (Q z) ≠ ⊤ := by
    intro z
    rw [tripleCompleteIntersectionChartJacobianBadSubmodule_ne_top_iff]
    obtain ⟨r, hr⟩ :=
      exists_cubic_with_nonzero_chartJacobian_eval_of_linearIndependent_derivatives
        p q hp hq z.1 (x z) (hcoord z.1 z.2) (hderiv z.1 z.2)
    refine ⟨r, ?_⟩
    simpa [e, Q, MvPolynomial.aeval_def] using hr
  obtain ⟨r, hr⟩ :=
    exists_cubic_avoiding_finite_allChart_tripleCompleteIntersectionChartJacobian_badSubmodules
      (A := fun _ : Fin 4 × ι => K) p q hp hq e Q hproper
  refine ⟨r, ?_⟩
  intro j i
  have hnot := hr j i
  simpa [e, Q, MvPolynomial.aeval_def] using hnot

theorem exists_ground_cubic_with_nonzero_chartJacobian_eval_of_fieldExtension_linearIndependent_derivatives
    {L : Type u} [Field L] [Algebra K L]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3)
    (j : Fin 4) (x : Fin 4 → L) (hxj : x j ≠ 0)
    (hderiv : LinearIndependent L
      ![(fun i : Fin 3 => (pderiv (j.succAbove i) (p.map (algebraMap K L))).eval x),
        (fun i : Fin 3 => (pderiv (j.succAbove i) (q.map (algebraMap K L))).eval x)]) :
    ∃ r : homogeneousSubmodule (Fin 4) K 3,
      (MvPolynomial.eval₂Hom (RingHom.id L) x)
          ((tripleCompleteIntersectionChartJacobianPolynomial p q r.1 j).map
            (algebraMap K L)) ≠ 0 := by
  let pL : MvPolynomial (Fin 4) L := p.map (algebraMap K L)
  let qL : MvPolynomial (Fin 4) L := q.map (algebraMap K L)
  have hpL : pL.IsHomogeneous 3 := by
    exact hp.map (algebraMap K L)
  have hqL : qL.IsHomogeneous 3 := by
    exact hq.map (algebraMap K L)
  obtain ⟨rL, hrL⟩ :=
    exists_cubic_with_nonzero_chartJacobian_eval_of_linearIndependent_derivatives
      pL qL hpL hqL j x hxj (by simpa [pL, qL] using hderiv)
  let ev : MvPolynomial (Fin 4) L →+* L := MvPolynomial.eval₂Hom (RingHom.id L) x
  let T : homogeneousSubmodule (Fin 4) L 3 →ₗ[L] L :=
    { toFun := fun r => ev (tripleCompleteIntersectionChartJacobianPolynomial pL qL r.1 j)
      map_add' := by
        intro r s
        change ev (tripleCompleteIntersectionChartJacobianPolynomial pL qL
          (r.1 + s.1) j) = _
        rw [tripleCompleteIntersectionChartJacobianPolynomial_add_right, map_add]
      map_smul' := by
        intro a r
        change ev (tripleCompleteIntersectionChartJacobianPolynomial pL qL
          (a • r.1) j) = _
        rw [show (a • r.1 : MvPolynomial (Fin 4) L) = C a * r.1 by
          simp [smul_eq_C_mul], tripleCompleteIntersectionChartJacobianPolynomial_C_mul_right]
        simp [ev, Algebra.smul_def] }
  have hT : T rL ≠ 0 := by
    simpa [T, ev] using hrL
  let mon : Monomials (Fin 4) 3 → homogeneousSubmodule (Fin 4) L 3 :=
    fun m => ⟨monomial m.1 1, isHomogeneous_monomial 1 m.2⟩
  have hr_sum : ∑ m : Monomials (Fin 4) 3, rL.1.coeff m.1 • mon m = rL := by
    apply Subtype.ext
    simp only [mon, Submodule.coe_sum, Submodule.coe_smul]
    change ∑ m : Monomials (Fin 4) 3, rL.1.coeff m.1 • monomial m.1 1 = rL.1
    rw [show (fun m : Monomials (Fin 4) 3 =>
        rL.1.coeff m.1 • monomial m.1 (1 : L)) =
        fun m => monomial m.1 (rL.1.coeff m.1) by
      funext m
      rw [MvPolynomial.smul_monomial]
      simp]
    exact sum_monomial_coeff_eq rL.1 rL.2
  have hsome : ∃ m : Monomials (Fin 4) 3, T (mon m) ≠ 0 := by
    by_contra hall
    push_neg at hall
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
  have hTmon : T (mon m) ≠ 0 := hm
  change ev ((tripleCompleteIntersectionChartJacobianPolynomial p q
      (monomial m.1 1) j).map (algebraMap K L)) ≠ 0
  rw [hmap]
  simpa [T, mon] using hTmon

/-- If restriction of a linear system to a finite scheme is surjective,
then surjectivity of its jet map on the restriction kernel is equivalent to
surjectivity of the combined restriction-and-jet map.  This turns the
constrained first-jet condition into a single rank computation. -/
theorem surjective_kernel_restriction_iff_product_surjective
    {V A J : Type*} [AddCommGroup V] [Module K V]
    [AddCommGroup A] [Module K A] [AddCommGroup J] [Module K J]
    (f : V →ₗ[K] A) (g : V →ₗ[K] J)
    (hf : Function.Surjective f) :
    Function.Surjective (fun v : LinearMap.ker f => g v.1) ↔
      Function.Surjective (f.prod g) := by
  constructor
  · intro h a
    obtain ⟨v₀, hv₀⟩ := hf a.1
    obtain ⟨w, hw⟩ := h (a.2 - g v₀)
    refine ⟨v₀ + w.1, ?_⟩
    ext
    · simp [hv₀, w.2]
    · simp [hw]
  · intro h j
    obtain ⟨v, hv⟩ := h (0, j)
    refine ⟨⟨v, ?_⟩, ?_⟩
    · have hfst := congrArg Prod.fst hv
      simpa using hfst
    · have hsnd := congrArg Prod.snd hv
      simpa using hsnd

/-- Scalar form of the restriction-and-jet criterion.  A scalar-valued
linear functional is nonzero on the restriction kernel exactly when the
combined restriction and scalar evaluation map is surjective.  For Voisin's
transversality step, the scalar is the chart-Jacobian determinant; this is
the exact pointwise condition, weaker than surjectivity onto all three
first derivatives. -/
theorem nonzero_kernel_scalar_iff_product_surjective
    {V A : Type*} [AddCommGroup V] [Module K V]
    [AddCommGroup A] [Module K A]
    (f : V →ₗ[K] A) (g : V →ₗ[K] K)
    (hf : Function.Surjective f) :
    (g.comp f.ker.subtype ≠ 0) ↔ Function.Surjective (f.prod g) := by
  have hscalar : (g.comp f.ker.subtype ≠ 0) ↔
      Function.Surjective (g.comp f.ker.subtype) := by
    constructor
    · intro hn y
      have hex : ∃ x : LinearMap.ker f, (g.comp f.ker.subtype) x ≠ 0 := by
        by_contra h
        apply hn
        ext x
        by_contra hx
        exact (not_exists.mp h x) hx
      obtain ⟨x, hx⟩ := hex
      refine ⟨(y / (g.comp f.ker.subtype) x) • x, ?_⟩
      rw [map_smul]
      exact div_mul_cancel₀ y hx
    · intro hsurj hzero
      obtain ⟨x, hx⟩ := hsurj 1
      have hxzero : (g.comp f.ker.subtype) x = 0 := by
        rw [hzero]
        simp
      simp [hxzero] at hx
  exact hscalar.trans
    (surjective_kernel_restriction_iff_product_surjective f g hf)

/-- The three affine-coordinate first derivatives of a constrained cubic
system at one point.  Surjectivity of this finite-dimensional linear map is
the first-jet condition used to produce a transverse system member. -/
noncomputable def affineChartPderivEvaluation
    {L : Type u} [Field L] [Algebra K L]
    (j : Fin 4) (x : Fin 4 → L)
    (W : Submodule K (homogeneousSubmodule (Fin 4) K 3)) :
    W →ₗ[K] (Fin 3 → L) where
  toFun r := fun i =>
    (pderiv (j.succAbove i) (r.1.1.map (algebraMap K L))).eval x
  map_add' r s := by
    funext i
    simp
  map_smul' a r := by
    funext i
    simp [smul_eq_C_mul, Algebra.smul_def]

/-- The underlying function of `affineChartPderivEvaluation` is exactly the
first-jet evaluation used in the pointwise Jacobian selector. -/
theorem affineChartPderivEvaluation_apply
    {L : Type u} [Field L] [Algebra K L]
    (j : Fin 4) (x : Fin 4 → L)
    (W : Submodule K (homogeneousSubmodule (Fin 4) K 3))
    (r : W) (i : Fin 3) :
  affineChartPderivEvaluation j x W r i =
      (pderiv (j.succAbove i) (r.1.1.map (algebraMap K L))).eval x := rfl

/-- On a normalized affine chart, the cubic monomial attached to one chart
coordinate has derivative vector equal to the corresponding standard basis
vector. -/
theorem affineChartPderivEvaluation_chartMonomial
    {K : Type u} [Field K]
    (j : Fin 4) (x : Fin 4 → K) (hxj : x j = 1) (i : Fin 3) :
    affineChartPderivEvaluation j x
      (⊤ : Submodule K (homogeneousSubmodule (Fin 4) K 3))
      ⟨⟨X j ^ 2 * X (j.succAbove i),
        (isHomogeneous_X_pow j 2).mul (isHomogeneous_X K (j.succAbove i))⟩,
        Submodule.mem_top⟩ = Pi.single i 1 := by
  funext k
  rw [affineChartPderivEvaluation_apply]
  have hjk : j.succAbove k ≠ j := by
    intro h
    exact (Fin.succAbove_ne j k) h
  simp [pderiv_mul, hjk, Fin.succAbove_right_injective,
    Pi.single_apply, eq_comm]
  split_ifs <;> simp [hxj]

/-- The unrestricted cubic system realizes every first derivative vector at
a point of a normalized affine chart. -/
theorem affineChartPderivEvaluation_surjective_top
    {K : Type u} [Field K]
    (j : Fin 4) (x : Fin 4 → K) (hxj : x j = 1) :
    Function.Surjective
      (affineChartPderivEvaluation j x
        (⊤ : Submodule K (homogeneousSubmodule (Fin 4) K 3))) := by
  intro y
  refine ⟨∑ i : Fin 3, y i •
    (⟨⟨X j ^ 2 * X (j.succAbove i),
      (isHomogeneous_X_pow j 2).mul (isHomogeneous_X K (j.succAbove i))⟩,
      Submodule.mem_top⟩), ?_⟩
  rw [map_sum]
  ext k
  simp only [map_smul, affineChartPderivEvaluation_chartMonomial j x hxj,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
    mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single k]
  · simp
  · intro i hi hik
    simp [hik.symm]
  · simp

/-- For a finite datum with coordinate algebra `A`, the exact pointwise
transversality condition at a residue-field chart point is equivalent to
surjectivity of one combined map: cubic restriction to `A` together with the
scalar chart-Jacobian evaluation at that point.  When `A` has dimension
sixteen, this is the rank-seventeen interpolation calculation needed for
the degree-ten residual construction. -/
theorem tripleCompleteIntersectionJacobian_nonzeroOnRestrictionKernel_iff_combinedSurjective
    {F A : Type u} [Field F] [CommRing A] [Algebra F A]
    [FiniteDimensional F A]
    (p q : MvPolynomial (Fin 4) F) (j : Fin 4)
    (x : Fin 4 → A) (e : MvPolynomial (Fin 4) F →ₐ[F] F)
    (hrestriction : Function.Surjective
      (homogeneousSectionRestriction (K := F) x 3)) :
    tripleCompleteIntersectionChartJacobianEvaluationLinearMap_restrict
        (K := F) p q j e (LinearMap.ker
          (homogeneousSectionRestriction (K := F) x 3)) ≠ 0 ↔
      Function.Surjective
        ((homogeneousSectionRestriction (K := F) x 3).prod
          (tripleCompleteIntersectionChartJacobianEvaluationLinearMap (K := F) (A := F) p q j e)) := by
  exact nonzero_kernel_scalar_iff_product_surjective
    (K := F) (homogeneousSectionRestriction (K := F) x 3)
    (tripleCompleteIntersectionChartJacobianEvaluationLinearMap (K := F) (A := F) p q j e)
    hrestriction

/-- A constrained cubic system has a transverse member at a residue-field
point when it realizes every first jet there.  The ambient smoothness input
gives a transverse cubic first; jet surjectivity replaces it by a member of
the prescribed system without changing the chart Jacobian. -/
theorem exists_mem_submodule_with_nonzero_chartJacobian_eval_of_fieldExtension_of_pderiv_surjective
    {L : Type u} [Field L] [Algebra K L]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3)
    (j : Fin 4) (x : Fin 4 → L) (hxj : x j ≠ 0)
    (hderiv : LinearIndependent L
      ![(fun i : Fin 3 => (pderiv (j.succAbove i) (p.map (algebraMap K L))).eval x),
        (fun i : Fin 3 => (pderiv (j.succAbove i) (q.map (algebraMap K L))).eval x)])
    (W : Submodule K (homogeneousSubmodule (Fin 4) K 3))
    (hjet : Function.Surjective (fun r : W => fun i : Fin 3 =>
      (pderiv (j.succAbove i) (r.1.1.map (algebraMap K L))).eval x)) :
    ∃ r : W,
      (MvPolynomial.eval₂Hom (RingHom.id L) x)
          ((tripleCompleteIntersectionChartJacobianPolynomial p q r.1.1 j).map
            (algebraMap K L)) ≠ 0 := by
  let pL : MvPolynomial (Fin 4) L := p.map (algebraMap K L)
  let qL : MvPolynomial (Fin 4) L := q.map (algebraMap K L)
  have hpL : pL.IsHomogeneous 3 := hp.map (algebraMap K L)
  have hqL : qL.IsHomogeneous 3 := hq.map (algebraMap K L)
  obtain ⟨r₀, hr₀⟩ :=
    exists_ground_cubic_with_nonzero_chartJacobian_eval_of_fieldExtension_linearIndependent_derivatives
      p q hp hq j x hxj hderiv
  obtain ⟨r, hr⟩ := hjet (fun i : Fin 3 =>
    (pderiv (j.succAbove i) (r₀.1.map (algebraMap K L))).eval x)
  have hmapr :
      (tripleCompleteIntersectionChartJacobianPolynomial p q r.1.1 j).map
          (algebraMap K L) =
        tripleCompleteIntersectionChartJacobianPolynomial pL qL
          (r.1.1.map (algebraMap K L)) j := by
    simpa [pL, qL] using
      (tripleCompleteIntersectionChartJacobianPolynomial_map (algebraMap K L)
        p q r.1.1 hp hq r.1.2 j)
  have hmap₀ :
      (tripleCompleteIntersectionChartJacobianPolynomial p q r₀.1 j).map
          (algebraMap K L) =
        tripleCompleteIntersectionChartJacobianPolynomial pL qL
          (r₀.1.map (algebraMap K L)) j := by
    simpa [pL, qL] using
      (tripleCompleteIntersectionChartJacobianPolynomial_map (algebraMap K L)
        p q r₀.1 hp hq r₀.2 j)
  have hsame :
      (tripleCompleteIntersectionChartJacobianPolynomial pL qL
        (r.1.1.map (algebraMap K L)) j).eval x =
      (tripleCompleteIntersectionChartJacobianPolynomial pL qL
        (r₀.1.map (algebraMap K L)) j).eval x := by
    apply tripleCompleteIntersectionChartJacobianPolynomial_eval_eq_of_chart_pderiv_eval_eq
    intro i
    exact congrFun hr i
  refine ⟨r, ?_⟩
  rw [hmapr]
  change (tripleCompleteIntersectionChartJacobianPolynomial pL qL
    (r.1.1.map (algebraMap K L)) j).eval x ≠ 0
  rw [hsame]
  change (MvPolynomial.eval₂Hom (RingHom.id L) x)
    (tripleCompleteIntersectionChartJacobianPolynomial pL qL
      (r₀.1.map (algebraMap K L)) j) ≠ 0
  rw [← hmap₀]
  exact hr₀

/-- Linear-map form of the constrained first-jet criterion.  It exposes the
remaining condition as surjectivity of `affineChartPderivEvaluation`, so it
can be established by a rank calculation in a moving family. -/
theorem exists_mem_submodule_with_nonzero_chartJacobian_eval_of_affineChartPderivEvaluation_surjective
    {L : Type u} [Field L] [Algebra K L]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3)
    (j : Fin 4) (x : Fin 4 → L) (hxj : x j ≠ 0)
    (hderiv : LinearIndependent L
      ![(fun i : Fin 3 => (pderiv (j.succAbove i) (p.map (algebraMap K L))).eval x),
        (fun i : Fin 3 => (pderiv (j.succAbove i) (q.map (algebraMap K L))).eval x)])
    (W : Submodule K (homogeneousSubmodule (Fin 4) K 3))
    (hjet : Function.Surjective (affineChartPderivEvaluation j x W)) :
    ∃ r : W,
      (MvPolynomial.eval₂Hom (RingHom.id L) x)
          ((tripleCompleteIntersectionChartJacobianPolynomial p q r.1.1 j).map
            (algebraMap K L)) ≠ 0 := by
  apply exists_mem_submodule_with_nonzero_chartJacobian_eval_of_fieldExtension_of_pderiv_surjective
    p q hp hq j x hxj hderiv W
  exact hjet

/- Over a finite field extension, the nonzero evaluation supplied above is
   already a unit.  This is the residue-field form used when the chart
   Jacobian is recorded as an invertibility certificate rather than merely as
   a nonvanishing scalar. -/
theorem exists_ground_cubic_with_chartJacobian_isUnit_of_finiteFieldExtension
    {L : Type u} [Field L] [Algebra K L] [FiniteDimensional K L]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3)
    (j : Fin 4) (x : Fin 4 → L) (hxj : x j ≠ 0)
    (hderiv : LinearIndependent L
      ![(fun i : Fin 3 => (pderiv (j.succAbove i) (p.map (algebraMap K L))).eval x),
        (fun i : Fin 3 => (pderiv (j.succAbove i) (q.map (algebraMap K L))).eval x)]) :
    ∃ r : homogeneousSubmodule (Fin 4) K 3,
      IsUnit ((MvPolynomial.eval₂Hom (RingHom.id L) x)
        ((tripleCompleteIntersectionChartJacobianPolynomial p q r.1 j).map
          (algebraMap K L))) := by
  obtain ⟨r, hr⟩ :=
    exists_ground_cubic_with_nonzero_chartJacobian_eval_of_fieldExtension_linearIndependent_derivatives
      p q hp hq j x hxj hderiv
  exact ⟨r, isUnit_iff_ne_zero.mpr hr⟩


/-- The field-extension witness is exactly a properness certificate for the
   corresponding pointwise Jacobian bad submodule.  This is the residue-field
   form used by the global incidence construction. -/
theorem tripleCompleteIntersectionChartJacobianBadSubmodule_ne_top_of_fieldExtension_linearIndependent_derivatives
    {L : Type u} [Field L] [Algebra K L]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3)
    (j : Fin 4) (x : Fin 4 → L) (hxj : x j ≠ 0)
    (hderiv : LinearIndependent L
      ![(fun i : Fin 3 => (pderiv (j.succAbove i) (p.map (algebraMap K L))).eval x),
        (fun i : Fin 3 => (pderiv (j.succAbove i) (q.map (algebraMap K L))).eval x)]) :
    tripleCompleteIntersectionChartJacobianBadSubmodule p q j
      (MvPolynomial.aeval x) (⊥ : Ideal L) ≠ ⊤ := by
  apply (tripleCompleteIntersectionChartJacobianBadSubmodule_ne_top_iff
    p q j (MvPolynomial.aeval x) (⊥ : Ideal L)).mpr
  obtain ⟨r, hr⟩ :=
    exists_ground_cubic_with_nonzero_chartJacobian_eval_of_fieldExtension_linearIndependent_derivatives
      p q hp hq j x hxj hderiv
  refine ⟨r, ?_⟩
  simpa [MvPolynomial.aeval_def] using hr


/-- A finite family of points with possibly different residue fields admits one
   ground-field cubic whose chart Jacobian is nonzero at every point.  This is
   the finite residue-field form of the Jacobian selection step. -/
theorem exists_ground_cubic_nonzero_chartJacobian_eval_of_finite_fieldExtension_linearIndependent_derivatives
    {ι : Type*} [Finite ι] [Infinite K]
    {L : ι → Type u} [∀ i, Field (L i)] [∀ i, Algebra K (L i)]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3)
    (x : ∀ i : ι, Fin 4 → L i)
    (hcoord : ∀ (j : Fin 4) (i : ι), x i j ≠ 0)
    (hderiv : ∀ (j : Fin 4) (i : ι), LinearIndependent (L i)
      ![(fun k : Fin 3 =>
          (pderiv (j.succAbove k) (p.map (algebraMap K (L i)))).eval (x i)),
        (fun k : Fin 3 =>
          (pderiv (j.succAbove k) (q.map (algebraMap K (L i)))).eval (x i))]) :
    ∃ r : homogeneousSubmodule (Fin 4) K 3,
      ∀ (j : Fin 4) (i : ι),
        (MvPolynomial.eval₂Hom (RingHom.id (L i)) (x i))
          ((tripleCompleteIntersectionChartJacobianPolynomial p q r.1 j).map
            (algebraMap K (L i))) ≠ 0 := by
  let e : ∀ z : Fin 4 × ι, MvPolynomial (Fin 4) K →ₐ[K] L z.2 :=
    fun z => MvPolynomial.aeval (x z.2)
  let Q : ∀ z : Fin 4 × ι, Ideal (L z.2) := fun _ => ⊥
  have hproper : ∀ z,
      tripleCompleteIntersectionChartJacobianBadSubmodule p q z.1 (e z) (Q z) ≠ ⊤ := by
    intro z
    exact tripleCompleteIntersectionChartJacobianBadSubmodule_ne_top_of_fieldExtension_linearIndependent_derivatives
      p q hp hq z.1 (x z.2) (hcoord z.1 z.2) (hderiv z.1 z.2)
  obtain ⟨r, hr⟩ :=
    exists_cubic_avoiding_finite_allChart_tripleCompleteIntersectionChartJacobian_badSubmodules
      (A := fun z : Fin 4 × ι => L z.2) p q hp hq e Q hproper
  refine ⟨r, ?_⟩
  intro j i
  have hnot := hr j i
  simpa [e, Q, MvPolynomial.aeval_def] using hnot


/-- A projective point need only have one nonzero coordinate, so its affine
    chart can vary from point to point.  This is the residue-field form of the
    finite Jacobian selection step used by incidence arguments. -/
theorem exists_ground_cubic_nonzero_chartJacobian_eval_of_finite_fieldExtension_linearIndependent_derivatives_on_chosen_charts
    {ι : Type*} [Finite ι] [Infinite K]
    {L : ι → Type u} [∀ i, Field (L i)] [∀ i, Algebra K (L i)]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3)
    (x : ∀ i : ι, Fin 4 → L i) (j : ι → Fin 4)
    (hcoord : ∀ i : ι, x i (j i) ≠ 0)
    (hderiv : ∀ i : ι, LinearIndependent (L i)
      ![(fun k : Fin 3 =>
          (pderiv ((j i).succAbove k) (p.map (algebraMap K (L i)))).eval (x i)),
        (fun k : Fin 3 =>
          (pderiv ((j i).succAbove k) (q.map (algebraMap K (L i)))).eval (x i))]) :
    ∃ r : homogeneousSubmodule (Fin 4) K 3,
      ∀ i : ι,
        (MvPolynomial.eval₂Hom (RingHom.id (L i)) (x i))
          ((tripleCompleteIntersectionChartJacobianPolynomial p q r.1 (j i)).map
            (algebraMap K (L i))) ≠ 0 := by
  let e : ∀ i : ι, MvPolynomial (Fin 4) K →ₐ[K] L i :=
    fun i => MvPolynomial.aeval (x i)
  let Q : ∀ i : ι, Ideal (L i) := fun _ => ⊥
  have hproper : ∀ i,
      tripleCompleteIntersectionChartJacobianBadSubmodule p q (j i) (e i) (Q i) ≠ ⊤ := by
    intro i
    exact tripleCompleteIntersectionChartJacobianBadSubmodule_ne_top_of_fieldExtension_linearIndependent_derivatives
      p q hp hq (j i) (x i) (hcoord i) (hderiv i)
  let bad : ∀ i : ι, Submodule K (homogeneousSubmodule (Fin 4) K 3) := fun i =>
    tripleCompleteIntersectionChartJacobianBadSubmodule p q (j i) (e i) (Q i)
  have hbad : ∀ i, bad i ≠ ⊤ := by
    intro i
    exact hproper i
  obtain ⟨r, hr⟩ := exists_vector_avoiding_finite_submodules bad hbad
  refine ⟨r, ?_⟩
  intro i
  have hrnot : r ∉ bad i := hr i
  have hnot := (not_congr (mem_tripleCompleteIntersectionChartJacobianBadSubmodule_iff
    p q (j i) (e i) (Q i) r)).mp hrnot
  simpa [e, Q, MvPolynomial.aeval_def] using hnot


/-- The residue-field evaluation attached to a maximal ideal of a finite
   coefficient algebra.  It records the images of the four affine chart
   coordinates under the residue map. -/
noncomputable def tripleCompleteIntersectionResidueEvaluation
    {A : Type u} [CommRing A] [Algebra K A]
    (e : MvPolynomial (Fin 4) K →ₐ[K] A)
    (Q : MaximalSpectrum A) : Fin 4 → Q.asIdeal.ResidueField :=
  fun i => algebraMap A Q.asIdeal.ResidueField (e (X i))

/-- In a normalized projective chart, the chosen coordinate remains one in
    every residue field.  Thus its nonvanishing hypothesis in the finite
    Jacobian selector is automatic for actual chart coordinates. -/
theorem tripleCompleteIntersectionResidueEvaluation_chartCoordinate_self
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (j : Fin 4)
    (Q : MaximalSpectrum (ChartRing I j)) :
    letI : Algebra K (ChartRing I j) := (chartBaseMap I j).toAlgebra
    tripleCompleteIntersectionResidueEvaluation
      (MvPolynomial.eval₂AlgHom K (chartCoordinate I j)) Q j = 1 := by
  simp [tripleCompleteIntersectionResidueEvaluation, chartCoordinate_self]

/-- The normalized coordinate of a chart cannot vanish in any of its residue
    fields. -/
theorem tripleCompleteIntersectionResidueEvaluation_chartCoordinate_ne_zero
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (j : Fin 4)
    (Q : MaximalSpectrum (ChartRing I j)) :
    letI : Algebra K (ChartRing I j) := (chartBaseMap I j).toAlgebra
    tripleCompleteIntersectionResidueEvaluation
      (MvPolynomial.eval₂AlgHom K (chartCoordinate I j)) Q j ≠ 0 := by
  rw [tripleCompleteIntersectionResidueEvaluation_chartCoordinate_self]
  exact one_ne_zero

/-- Evaluating a ground-field polynomial after coefficient extension agrees
   with first applying the coefficient algebra map and then reducing at a
   maximal ideal.  This is the bookkeeping identity used to turn the finite
   residue-field selector into a unit certificate in the original algebra. -/
theorem tripleCompleteIntersectionResidueEvaluation_map_eval
    {A : Type u} [CommRing A] [Algebra K A]
    (e : MvPolynomial (Fin 4) K →ₐ[K] A)
    (Q : MaximalSpectrum A) (f : MvPolynomial (Fin 4) K) :
    algebraMap A Q.asIdeal.ResidueField (e f) =
      (MvPolynomial.eval₂Hom (RingHom.id Q.asIdeal.ResidueField)
        (tripleCompleteIntersectionResidueEvaluation e Q))
        (f.map (algebraMap K Q.asIdeal.ResidueField)) := by
  let E : MvPolynomial (Fin 4) K →ₐ[K] Q.asIdeal.ResidueField :=
    (IsScalarTower.toAlgHom K A Q.asIdeal.ResidueField).comp e
  let F : MvPolynomial (Fin 4) K →ₐ[K] Q.asIdeal.ResidueField :=
    { toRingHom := (MvPolynomial.eval₂Hom (RingHom.id Q.asIdeal.ResidueField)
        (tripleCompleteIntersectionResidueEvaluation e Q)).comp
          (MvPolynomial.map (algebraMap K Q.asIdeal.ResidueField))
      commutes' := by intro c; simp }
  have hEF : E = F := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [E, F, tripleCompleteIntersectionResidueEvaluation]
  change E f = F f
  rw [hEF]


/- A single ground-field cubic can be selected simultaneously for all four
   normalized charts and all maximal points of their finite coefficient
   algebras.  The dependent sum below is finite, so the pointwise residue-field
   Jacobian witnesses combine into one global unit certificate. -/
theorem exists_ground_cubic_with_allChartJacobian_isUnit_of_maximalSpectra
    [Infinite K]
    {A : Fin 4 → Type u} [∀ j, CommRing (A j)] [∀ j, Algebra K (A j)]
    [∀ j, Module.Finite K (A j)]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3)
    (e : ∀ j, MvPolynomial (Fin 4) K →ₐ[K] A j)
    (hcoord : ∀ (j : Fin 4) (Q : MaximalSpectrum (A j)),
      tripleCompleteIntersectionResidueEvaluation (e j) Q j ≠ 0)
    (hderiv : ∀ (j : Fin 4) (Q : MaximalSpectrum (A j)),
      LinearIndependent Q.asIdeal.ResidueField
      ![(fun i : Fin 3 =>
          (pderiv (j.succAbove i) (p.map (algebraMap K Q.asIdeal.ResidueField))).eval
            (tripleCompleteIntersectionResidueEvaluation (e j) Q)),
        (fun i : Fin 3 =>
          (pderiv (j.succAbove i) (q.map (algebraMap K Q.asIdeal.ResidueField))).eval
            (tripleCompleteIntersectionResidueEvaluation (e j) Q))]) :
    ∃ r : homogeneousSubmodule (Fin 4) K 3,
      ∀ j : Fin 4, IsUnit (e j (tripleCompleteIntersectionChartJacobianPolynomial p q r.1 j)) := by
  letI : ∀ j, IsArtinianRing (A j) := fun j => IsArtinianRing.of_finite K (A j)
  let eQ : ∀ z : Σ j, MaximalSpectrum (A j),
      MvPolynomial (Fin 4) K →ₐ[K] z.2.asIdeal.ResidueField :=
    fun z => MvPolynomial.aeval (tripleCompleteIntersectionResidueEvaluation (e z.1) z.2)
  let bad : ∀ z : Σ j, MaximalSpectrum (A j),
      Submodule K (homogeneousSubmodule (Fin 4) K 3) := fun z =>
    tripleCompleteIntersectionChartJacobianBadSubmodule p q z.1 (eQ z) (⊥ : Ideal z.2.asIdeal.ResidueField)
  have hproper : ∀ z, bad z ≠ ⊤ := by
    intro z
    exact tripleCompleteIntersectionChartJacobianBadSubmodule_ne_top_of_fieldExtension_linearIndependent_derivatives
      p q hp hq z.1 (tripleCompleteIntersectionResidueEvaluation (e z.1) z.2)
      (hcoord z.1 z.2) (hderiv z.1 z.2)
  obtain ⟨r, hr⟩ := exists_vector_avoiding_finite_submodules bad hproper
  refine ⟨r, ?_⟩
  intro j
  by_contra hunit
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal
    (Ideal.span ({e j (tripleCompleteIntersectionChartJacobianPolynomial p q r.1 j)} : Set (A j)))
    (Ideal.span_singleton_ne_top hunit)
  let Q : MaximalSpectrum (A j) := ⟨M, hM⟩
  have haM : e j (tripleCompleteIntersectionChartJacobianPolynomial p q r.1 j) ∈ M :=
    hle (Ideal.subset_span (Set.mem_singleton _))
  have hzero : algebraMap (A j) Q.asIdeal.ResidueField
      (e j (tripleCompleteIntersectionChartJacobianPolynomial p q r.1 j)) = 0 :=
    Ideal.algebraMap_residueField_eq_zero.mpr haM
  have hzero' : eQ ⟨j, Q⟩ (tripleCompleteIntersectionChartJacobianPolynomial p q r.1 j) = 0 := by
    rw [show eQ ⟨j, Q⟩ = MvPolynomial.aeval
      (tripleCompleteIntersectionResidueEvaluation (e j) Q) by rfl]
    rw [MvPolynomial.aeval_def]
    simpa [MvPolynomial.eval₂_map] using
      (tripleCompleteIntersectionResidueEvaluation_map_eval (e j) Q
        (tripleCompleteIntersectionChartJacobianPolynomial p q r.1 j)).symm.trans hzero
  have hmem : r ∈ bad ⟨j, Q⟩ := by
    change eQ ⟨j, Q⟩ (tripleCompleteIntersectionChartJacobianPolynomial p q r.1 j) ∈
      (⊥ : Ideal Q.asIdeal.ResidueField)
    simpa [hzero']
  exact (hr ⟨j, Q⟩) hmem


/-- The finite residue-field Jacobian selector can be restricted to a prescribed
linear system of cubics.  This is the form relevant to Voisin's third cubic:
the chosen equation must remain in the cubic system through the completed
finite datum, rather than merely in the ambient space of all cubics.  The
pointwise premise says exactly that this smaller system is not contained in
the Jacobian-bad hyperplane at any residue point. -/
theorem exists_mem_submodule_with_allChartJacobian_isUnit_of_maximalSpectra
    [Infinite K]
    {A : Fin 4 → Type u} [∀ j, CommRing (A j)] [∀ j, Algebra K (A j)]
    [∀ j, Module.Finite K (A j)]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3)
    (e : ∀ j, MvPolynomial (Fin 4) K →ₐ[K] A j)
    (W : Submodule K (homogeneousSubmodule (Fin 4) K 3))
    (hwitness : ∀ (j : Fin 4) (Q : MaximalSpectrum (A j)),
      ∃ r : W,
        (MvPolynomial.aeval
          (tripleCompleteIntersectionResidueEvaluation (e j) Q))
          (tripleCompleteIntersectionChartJacobianPolynomial p q r.1 j) ≠ 0) :
    ∃ r : W,
      ∀ j : Fin 4, IsUnit (e j
        (tripleCompleteIntersectionChartJacobianPolynomial p q r.1 j)) := by
  letI : ∀ j, IsArtinianRing (A j) := fun j => IsArtinianRing.of_finite K (A j)
  let eQ : ∀ z : Σ j, MaximalSpectrum (A j),
      MvPolynomial (Fin 4) K →ₐ[K] z.2.asIdeal.ResidueField :=
    fun z => MvPolynomial.aeval (tripleCompleteIntersectionResidueEvaluation (e z.1) z.2)
  let bad : ∀ z : Σ j, MaximalSpectrum (A j),
      Submodule K (homogeneousSubmodule (Fin 4) K 3) := fun z =>
    tripleCompleteIntersectionChartJacobianBadSubmodule p q z.1 (eQ z)
      (⊥ : Ideal z.2.asIdeal.ResidueField)
  let badW : ∀ z : Σ j, MaximalSpectrum (A j), Submodule K W := fun z =>
    (bad z).comap W.subtype
  have hproper : ∀ z, badW z ≠ ⊤ := by
    intro z htop
    obtain ⟨r, hr⟩ := hwitness z.1 z.2
    have hmem : r ∈ badW z := by rw [htop]; exact Submodule.mem_top
    have hzero : eQ z
        (tripleCompleteIntersectionChartJacobianPolynomial p q r.1 z.1) = 0 := by
      change eQ z
        (tripleCompleteIntersectionChartJacobianPolynomial p q r.1 z.1) ∈
          (⊥ : Ideal z.2.asIdeal.ResidueField) at hmem
      simpa using hmem
    exact hr (by simpa [eQ] using hzero)
  obtain ⟨r, hr⟩ := exists_vector_avoiding_finite_submodules
    (V := W) badW hproper
  refine ⟨r, ?_⟩
  intro j
  by_contra hunit
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal
    (Ideal.span ({e j
      (tripleCompleteIntersectionChartJacobianPolynomial p q r.1 j)} : Set (A j)))
    (Ideal.span_singleton_ne_top hunit)
  let Q : MaximalSpectrum (A j) := ⟨M, hM⟩
  have haM : e j (tripleCompleteIntersectionChartJacobianPolynomial p q r.1 j) ∈ M :=
    hle (Ideal.subset_span (Set.mem_singleton _))
  have hzero : algebraMap (A j) Q.asIdeal.ResidueField
      (e j (tripleCompleteIntersectionChartJacobianPolynomial p q r.1 j)) = 0 :=
    Ideal.algebraMap_residueField_eq_zero.mpr haM
  have hzero' : eQ ⟨j, Q⟩
      (tripleCompleteIntersectionChartJacobianPolynomial p q r.1 j) = 0 := by
    rw [show eQ ⟨j, Q⟩ = MvPolynomial.aeval
      (tripleCompleteIntersectionResidueEvaluation (e j) Q) by rfl]
    rw [MvPolynomial.aeval_def]
    simpa [MvPolynomial.eval₂_map] using
      (tripleCompleteIntersectionResidueEvaluation_map_eval (e j) Q
        (tripleCompleteIntersectionChartJacobianPolynomial p q r.1 j)).symm.trans hzero
  have hmem : r ∈ badW ⟨j, Q⟩ := by
    change eQ ⟨j, Q⟩
      (tripleCompleteIntersectionChartJacobianPolynomial p q r.1 j) ∈
        (⊥ : Ideal Q.asIdeal.ResidueField)
    simpa [hzero']
  exact (hr ⟨j, Q⟩) hmem

/-- Exact linear-map form of the constrained finite Jacobian selector.  At
each residue point, the restriction of the Jacobian evaluation functional to
the prescribed cubic system need only be nonzero. -/
theorem exists_mem_submodule_with_allChartJacobian_isUnit_of_maximalSpectra_of_restrict_ne_zero
    [Infinite K]
    {A : Fin 4 → Type u} [∀ j, CommRing (A j)] [∀ j, Algebra K (A j)]
    [∀ j, Module.Finite K (A j)]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3)
    (e : ∀ j, MvPolynomial (Fin 4) K →ₐ[K] A j)
    (W : Submodule K (homogeneousSubmodule (Fin 4) K 3))
    (hnonzero : ∀ (j : Fin 4) (Q : MaximalSpectrum (A j)),
      tripleCompleteIntersectionChartJacobianEvaluationLinearMap_restrict p q j
        (MvPolynomial.aeval (tripleCompleteIntersectionResidueEvaluation (e j) Q)) W ≠ 0) :
    ∃ r : W,
      ∀ j : Fin 4, IsUnit (e j
        (tripleCompleteIntersectionChartJacobianPolynomial p q r.1 j)) := by
  apply exists_mem_submodule_with_allChartJacobian_isUnit_of_maximalSpectra
    p q hp hq e W
  intro j Q
  exact (tripleCompleteIntersectionChartJacobianEvaluationLinearMap_restrict_ne_zero_iff
    p q j (MvPolynomial.aeval (tripleCompleteIntersectionResidueEvaluation (e j) Q)) W).mp
      (hnonzero j Q)

/-- First-jet surjectivity of a constrained cubic system supplies the
pointwise witness required by the finite maximal-spectrum selector.  This
reduces its geometric premise to the usual jet-interpolation statement on
the moving cubic system. -/
theorem exists_mem_submodule_with_allChartJacobian_isUnit_of_maximalSpectra_of_pderiv_surjective
    [Infinite K]
    {A : Fin 4 → Type u} [∀ j, CommRing (A j)] [∀ j, Algebra K (A j)]
    [∀ j, Module.Finite K (A j)]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3)
    (e : ∀ j, MvPolynomial (Fin 4) K →ₐ[K] A j)
    (W : Submodule K (homogeneousSubmodule (Fin 4) K 3))
    (hcoord : ∀ (j : Fin 4) (Q : MaximalSpectrum (A j)),
      tripleCompleteIntersectionResidueEvaluation (e j) Q j ≠ 0)
    (hderiv : ∀ (j : Fin 4) (Q : MaximalSpectrum (A j)),
      LinearIndependent Q.asIdeal.ResidueField
        ![(fun i : Fin 3 =>
            (pderiv (j.succAbove i) (p.map (algebraMap K Q.asIdeal.ResidueField))).eval
              (tripleCompleteIntersectionResidueEvaluation (e j) Q)),
          (fun i : Fin 3 =>
            (pderiv (j.succAbove i) (q.map (algebraMap K Q.asIdeal.ResidueField))).eval
              (tripleCompleteIntersectionResidueEvaluation (e j) Q))])
    (hjet : ∀ (j : Fin 4) (Q : MaximalSpectrum (A j)),
      Function.Surjective (fun r : W => fun i : Fin 3 =>
        (pderiv (j.succAbove i) (r.1.1.map (algebraMap K Q.asIdeal.ResidueField))).eval
          (tripleCompleteIntersectionResidueEvaluation (e j) Q))) :
    ∃ r : W,
      ∀ j : Fin 4, IsUnit (e j
        (tripleCompleteIntersectionChartJacobianPolynomial p q r.1 j)) := by
  apply exists_mem_submodule_with_allChartJacobian_isUnit_of_maximalSpectra
    p q hp hq e W
  intro j Q
  obtain ⟨r, hr⟩ :=
    exists_mem_submodule_with_nonzero_chartJacobian_eval_of_fieldExtension_of_pderiv_surjective
      p q hp hq j (tripleCompleteIntersectionResidueEvaluation (e j) Q)
      (hcoord j Q) (hderiv j Q) W (hjet j Q)
  refine ⟨r, ?_⟩
  simpa [MvPolynomial.aeval_def] using hr


/-- Specialization of the constrained selector to the actual cubic linear
system through finite homogeneous coordinates.  The chosen cubic is an
element of the restriction kernel, so its vanishing on the completed finite
datum is retained by type while its chart Jacobians are made units. -/
theorem exists_cubic_in_restrictionKernel_with_allChartJacobian_isUnit_of_maximalSpectra
    [Infinite K]
    {B : Type u} [CommRing B] [Algebra K B]
    {A : Fin 4 → Type u} [∀ j, CommRing (A j)] [∀ j, Algebra K (A j)]
    [∀ j, Module.Finite K (A j)]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3)
    (x : Fin 4 → B) (e : ∀ j, MvPolynomial (Fin 4) K →ₐ[K] A j)
    (hwitness : ∀ (j : Fin 4) (Q : MaximalSpectrum (A j)),
      ∃ r : LinearMap.ker (homogeneousSectionRestriction (K := K) x 3),
        (MvPolynomial.aeval
          (tripleCompleteIntersectionResidueEvaluation (e j) Q))
          (tripleCompleteIntersectionChartJacobianPolynomial p q r.1.1 j) ≠ 0) :
    ∃ r : LinearMap.ker (homogeneousSectionRestriction (K := K) x 3),
      ∀ j : Fin 4, IsUnit (e j
        (tripleCompleteIntersectionChartJacobianPolynomial p q r.1.1 j)) := by
  exact exists_mem_submodule_with_allChartJacobian_isUnit_of_maximalSpectra
    p q hp hq e (LinearMap.ker (homogeneousSectionRestriction (K := K) x 3)) hwitness

/-- Exact local-linear-map form of the completed-datum selector.  The
restriction-kernel system supplies a global transverse cubic as soon as its
Jacobian evaluation functional is nonzero at every relevant residue point. -/
theorem exists_cubic_in_restrictionKernel_with_allChartJacobian_isUnit_of_restrict_ne_zero
    [Infinite K]
    {B : Type u} [CommRing B] [Algebra K B]
    {A : Fin 4 → Type u} [∀ j, CommRing (A j)] [∀ j, Algebra K (A j)]
    [∀ j, Module.Finite K (A j)]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3)
    (x : Fin 4 → B) (e : ∀ j, MvPolynomial (Fin 4) K →ₐ[K] A j)
    (hnonzero : ∀ (j : Fin 4) (Q : MaximalSpectrum (A j)),
      tripleCompleteIntersectionChartJacobianEvaluationLinearMap_restrict p q j
        (MvPolynomial.aeval (tripleCompleteIntersectionResidueEvaluation (e j) Q))
        (LinearMap.ker (homogeneousSectionRestriction (K := K) x 3)) ≠ 0) :
    ∃ r : LinearMap.ker (homogeneousSectionRestriction (K := K) x 3),
      ∀ j : Fin 4, IsUnit (e j
        (tripleCompleteIntersectionChartJacobianPolynomial p q r.1.1 j)) := by
  exact exists_mem_submodule_with_allChartJacobian_isUnit_of_maximalSpectra_of_restrict_ne_zero
    p q hp hq e (LinearMap.ker (homogeneousSectionRestriction (K := K) x 3)) hnonzero

/-- The completed-datum selector in first-jet form.  At this point the sole
new local geometric input is surjectivity of the cubic system through the
datum onto first jets at the relevant residue points. -/
theorem exists_cubic_in_restrictionKernel_with_allChartJacobian_isUnit_of_maximalSpectra_of_pderiv_surjective
    [Infinite K]
    {B : Type u} [CommRing B] [Algebra K B]
    {A : Fin 4 → Type u} [∀ j, CommRing (A j)] [∀ j, Algebra K (A j)]
    [∀ j, Module.Finite K (A j)]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3)
    (x : Fin 4 → B) (e : ∀ j, MvPolynomial (Fin 4) K →ₐ[K] A j)
    (hcoord : ∀ (j : Fin 4) (Q : MaximalSpectrum (A j)),
      tripleCompleteIntersectionResidueEvaluation (e j) Q j ≠ 0)
    (hderiv : ∀ (j : Fin 4) (Q : MaximalSpectrum (A j)),
      LinearIndependent Q.asIdeal.ResidueField
        ![(fun i : Fin 3 =>
            (pderiv (j.succAbove i) (p.map (algebraMap K Q.asIdeal.ResidueField))).eval
              (tripleCompleteIntersectionResidueEvaluation (e j) Q)),
          (fun i : Fin 3 =>
            (pderiv (j.succAbove i) (q.map (algebraMap K Q.asIdeal.ResidueField))).eval
              (tripleCompleteIntersectionResidueEvaluation (e j) Q))])
    (hjet : ∀ (j : Fin 4) (Q : MaximalSpectrum (A j)),
      Function.Surjective
        (fun r : LinearMap.ker (homogeneousSectionRestriction (K := K) x 3) =>
          fun i : Fin 3 =>
            (pderiv (j.succAbove i)
              (r.1.1.map (algebraMap K Q.asIdeal.ResidueField))).eval
              (tripleCompleteIntersectionResidueEvaluation (e j) Q))) :
    ∃ r : LinearMap.ker (homogeneousSectionRestriction (K := K) x 3),
      ∀ j : Fin 4, IsUnit (e j
        (tripleCompleteIntersectionChartJacobianPolynomial p q r.1.1 j)) := by
  exact exists_mem_submodule_with_allChartJacobian_isUnit_of_maximalSpectra_of_pderiv_surjective
    p q hp hq e (LinearMap.ker (homogeneousSectionRestriction (K := K) x 3))
      hcoord hderiv hjet

/-- Rank form of the sufficient completed-datum first-jet criterion.  The
restriction-kernel cubic system realizes all three affine first derivatives
at every residue point.  This is a concrete determinantal sufficient
condition for the local Bertini witness; it can be stronger than necessary
over a nontrivial residue-field extension. -/
theorem exists_cubic_in_restrictionKernel_with_allChartJacobian_isUnit_of_affineChartPderivEvaluation_range_eq_top
    [Infinite K]
    {B : Type u} [CommRing B] [Algebra K B]
    {A : Fin 4 → Type u} [∀ j, CommRing (A j)] [∀ j, Algebra K (A j)]
    [∀ j, Module.Finite K (A j)]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3)
    (x : Fin 4 → B) (e : ∀ j, MvPolynomial (Fin 4) K →ₐ[K] A j)
    (hcoord : ∀ (j : Fin 4) (Q : MaximalSpectrum (A j)),
      tripleCompleteIntersectionResidueEvaluation (e j) Q j ≠ 0)
    (hderiv : ∀ (j : Fin 4) (Q : MaximalSpectrum (A j)),
      LinearIndependent Q.asIdeal.ResidueField
        ![(fun i : Fin 3 =>
            (pderiv (j.succAbove i) (p.map (algebraMap K Q.asIdeal.ResidueField))).eval
              (tripleCompleteIntersectionResidueEvaluation (e j) Q)),
          (fun i : Fin 3 =>
            (pderiv (j.succAbove i) (q.map (algebraMap K Q.asIdeal.ResidueField))).eval
              (tripleCompleteIntersectionResidueEvaluation (e j) Q))])
    (hjet : ∀ (j : Fin 4) (Q : MaximalSpectrum (A j)),
      LinearMap.range (affineChartPderivEvaluation j
        (tripleCompleteIntersectionResidueEvaluation (e j) Q)
        (LinearMap.ker (homogeneousSectionRestriction (K := K) x 3))) = ⊤) :
    ∃ r : LinearMap.ker (homogeneousSectionRestriction (K := K) x 3),
      ∀ j : Fin 4, IsUnit (e j
        (tripleCompleteIntersectionChartJacobianPolynomial p q r.1.1 j)) := by
  apply exists_cubic_in_restrictionKernel_with_allChartJacobian_isUnit_of_maximalSpectra_of_pderiv_surjective
    p q hp hq x e hcoord hderiv
  intro j Q
  exact LinearMap.range_eq_top.mp (hjet j Q)


/-- If the first two derivative columns are independent in every residue
   field of a finite-dimensional coefficient algebra, one ground-field cubic
   makes the chart Jacobian a unit in that algebra.  This is the finite
   maximal-spectrum passage from the residue-field Bertini calculation to a
   global Jacobian certificate. -/
theorem exists_ground_cubic_with_chartJacobian_isUnit_of_maximalSpectrum
    [Infinite K]
    {A : Type u} [CommRing A] [Algebra K A] [Module.Finite K A]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3)
    (j : Fin 4)
    (e : MvPolynomial (Fin 4) K →ₐ[K] A)
    (hcoord : ∀ Q : MaximalSpectrum A,
      tripleCompleteIntersectionResidueEvaluation e Q j ≠ 0)
    (hderiv : ∀ Q : MaximalSpectrum A, LinearIndependent Q.asIdeal.ResidueField
      ![(fun i : Fin 3 =>
          (pderiv (j.succAbove i) (p.map (algebraMap K Q.asIdeal.ResidueField))).eval
            (tripleCompleteIntersectionResidueEvaluation e Q)),
        (fun i : Fin 3 =>
          (pderiv (j.succAbove i) (q.map (algebraMap K Q.asIdeal.ResidueField))).eval
            (tripleCompleteIntersectionResidueEvaluation e Q))]) :
    ∃ r : homogeneousSubmodule (Fin 4) K 3,
      IsUnit (e (tripleCompleteIntersectionChartJacobianPolynomial p q r.1 j)) := by
  letI : IsArtinianRing A := IsArtinianRing.of_finite K A
  let eQ : ∀ Q : MaximalSpectrum A,
      MvPolynomial (Fin 4) K →ₐ[K] Q.asIdeal.ResidueField :=
    fun Q => MvPolynomial.aeval (tripleCompleteIntersectionResidueEvaluation e Q)
  have hproper : ∀ Q : MaximalSpectrum A,
      tripleCompleteIntersectionChartJacobianBadSubmodule p q j (eQ Q)
        (⊥ : Ideal Q.asIdeal.ResidueField) ≠ ⊤ := by
    intro Q
    apply tripleCompleteIntersectionChartJacobianBadSubmodule_ne_top_of_fieldExtension_linearIndependent_derivatives
      p q hp hq j (tripleCompleteIntersectionResidueEvaluation e Q)
      (hcoord Q) (hderiv Q)
  obtain ⟨r, hr⟩ :=
    exists_cubic_avoiding_finite_tripleCompleteIntersectionChartJacobian_badSubmodules
      (A := fun Q : MaximalSpectrum A => Q.asIdeal.ResidueField)
      p q hp hq j eQ (fun _ => (⊥ : Ideal _)) hproper
  refine ⟨r, ?_⟩
  by_contra hunit
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal
    (Ideal.span ({e (tripleCompleteIntersectionChartJacobianPolynomial p q r.1 j)} : Set A))
    (Ideal.span_singleton_ne_top hunit)
  let Q : MaximalSpectrum A := ⟨M, hM⟩
  have haM : e (tripleCompleteIntersectionChartJacobianPolynomial p q r.1 j) ∈ M :=
    hle (Ideal.subset_span (Set.mem_singleton _))
  have hzero : algebraMap A Q.asIdeal.ResidueField
      (e (tripleCompleteIntersectionChartJacobianPolynomial p q r.1 j)) = 0 :=
    Ideal.algebraMap_residueField_eq_zero.mpr haM
  have hzero' : eQ Q (tripleCompleteIntersectionChartJacobianPolynomial p q r.1 j) = 0 := by
    rw [show eQ Q = MvPolynomial.aeval
      (tripleCompleteIntersectionResidueEvaluation e Q) by rfl]
    rw [MvPolynomial.aeval_def]
    simpa [MvPolynomial.eval₂_map] using
      (tripleCompleteIntersectionResidueEvaluation_map_eval e Q
        (tripleCompleteIntersectionChartJacobianPolynomial p q r.1 j)).symm.trans hzero
  have hmem : eQ Q (tripleCompleteIntersectionChartJacobianPolynomial p q r.1 j) ∈
      (⊥ : Ideal Q.asIdeal.ResidueField) := by simpa [hzero']
  exact (hr Q) hmem

/-- The degree-six Jacobian frame induced by a finite collection of cubics in
a prescribed third-cubic system.  This is the direct input for the generic
projective-incidence API once the moving system supplies an independent image
frame. -/
noncomputable def tripleCompleteIntersectionChartJacobianRestrictedFrame
    {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3) (j : Fin 4)
    (W : Submodule K (homogeneousSubmodule (Fin 4) K 3))
    (v : Fin n → W) :
    Fin n → homogeneousSubmodule (Fin 4) K 6 :=
  fun i => tripleCompleteIntersectionChartJacobianHomogeneousLinearMap_restrict
    p q hp hq j W (v i)

@[simp] theorem tripleCompleteIntersectionChartJacobianRestrictedFrame_apply
    {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3) (j : Fin 4)
    (W : Submodule K (homogeneousSubmodule (Fin 4) K 3))
    (v : Fin n → W) (i : Fin n) :
    tripleCompleteIntersectionChartJacobianRestrictedFrame p q hp hq j W v i =
      tripleCompleteIntersectionChartJacobianHomogeneousLinearMap_restrict
        p q hp hq j W (v i) := rfl

/-- An independent finite frame in the constrained Jacobian image gives a
closed projective system of sextics.  This is the projective parameter map to
which the configuration-incidence theorems apply. -/
noncomputable def tripleCompleteIntersectionChartJacobianRestrictedFrameProjectiveSystem
    {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3) (j : Fin 4)
    (W : Submodule K (homogeneousSubmodule (Fin 4) K 3))
    (v : Fin n → W)
    (hv : LinearIndependent K
      (tripleCompleteIntersectionChartJacobianRestrictedFrame p q hp hq j W v)) :
    projectiveLinearSystemParameters (K := K) (τ := Fin n) ⟶
      projectiveParameters K (Fin 4) 6 := by
  let e : Fin (Fintype.card (Monomials (Fin 4) 6)) ≃ Monomials (Fin 4) 6 :=
    (Fintype.equivFin _).symm
  exact homogeneousFrameToParameters 6 e
    (tripleCompleteIntersectionChartJacobianRestrictedFrame p q hp hq j W v) hv

instance tripleCompleteIntersectionChartJacobianRestrictedFrameProjectiveSystem_isClosedImmersion
    {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3) (j : Fin 4)
    (W : Submodule K (homogeneousSubmodule (Fin 4) K 3))
    (v : Fin n → W)
    (hv : LinearIndependent K
      (tripleCompleteIntersectionChartJacobianRestrictedFrame p q hp hq j W v)) :
    IsClosedImmersion
      (tripleCompleteIntersectionChartJacobianRestrictedFrameProjectiveSystem
        p q hp hq j W v hv) := by
  unfold tripleCompleteIntersectionChartJacobianRestrictedFrameProjectiveSystem
  infer_instance

/-- The constrained Jacobian projective system is proper over the coefficient
field.  It can therefore serve as the parameter scheme in the closed
finite-incidence construction. -/
instance tripleCompleteIntersectionChartJacobianRestrictedFrameProjectiveSystem_isProper
    {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3) (j : Fin 4)
    (W : Submodule K (homogeneousSubmodule (Fin 4) K 3))
    (v : Fin n → W)
    (hv : LinearIndependent K
      (tripleCompleteIntersectionChartJacobianRestrictedFrame p q hp hq j W v)) :
    IsProper
      (tripleCompleteIntersectionChartJacobianRestrictedFrameProjectiveSystem
        p q hp hq j W v hv ≫ projectiveParametersToBase K (Fin 4) 6) := by
  infer_instance

/- The canonical image frame therefore has an actual projective parameter
   space and a closed embedding into the full degree-six equation space. -/
noncomputable def tripleCompleteIntersectionChartJacobianImageProjectiveSystem
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3) (j : Fin 4) :
    projectiveLinearSystemParameters (K := K)
        (τ := Fin (Module.finrank K
          (LinearMap.range (tripleCompleteIntersectionChartJacobianHomogeneousLinearMap
            p q hp hq j)))) ⟶
      projectiveParameters K (Fin 4) 6 := by
  let b := tripleCompleteIntersectionChartJacobianImageBasis p q hp hq j
  let e : Fin (Fintype.card (Monomials (Fin 4) 6)) ≃ Monomials (Fin 4) 6 :=
    (Fintype.equivFin _).symm
  exact homogeneousFrameToParameters 6 e
    (tripleCompleteIntersectionChartJacobianImageFrame p q hp hq j b)
    (tripleCompleteIntersectionChartJacobianImageFrame_linearIndependent
      p q hp hq j b)

instance tripleCompleteIntersectionChartJacobianImageProjectiveSystem_isClosedImmersion
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3) (j : Fin 4) :
    IsClosedImmersion
      (tripleCompleteIntersectionChartJacobianImageProjectiveSystem p q hp hq j) := by
  unfold tripleCompleteIntersectionChartJacobianImageProjectiveSystem
  infer_instance

/-- The canonical Jacobian-image parameter system is proper over the
coefficient field.  In particular it is a legitimate projective parameter
space for the closed bad-incidence locus, without a separately supplied
finite frame. -/
instance tripleCompleteIntersectionChartJacobianImageProjectiveSystem_isProper
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3) (j : Fin 4) :
    IsProper
      (tripleCompleteIntersectionChartJacobianImageProjectiveSystem p q hp hq j ≫
        projectiveParametersToBase K (Fin 4) 6) := by
  infer_instance

/- The singular-member locus for a cubic linear system is a *paired*
   incidence condition.  On the intermediate projective curve, the selected
   cubic and its degree-six Jacobian determinant must vanish at the same
   point.  The following carrier-level construction keeps the two equations
   over one parameter and projects their common incidence to the parameter
   scheme. -/
noncomputable def projectiveCubicSexticCommonZeroBadLocus
    {C T : Scheme.{u}}
    (cBase : C ⟶ Spec (.of K)) (tBase : T ⟶ Spec (.of K))
    (a : C ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (s₃ : T ⟶ projectiveParameters K (Fin 4) 3)
    (s₆ : T ⟶ projectiveParameters K (Fin 4) 6) : Set T :=
  let B := pullback cBase tBase
  let π : B ⟶ T := pullback.snd cBase tBase
  let b₃ : B ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K) ⨯
      projectiveParameters K (Fin 4) 3 :=
    Limits.prod.lift (pullback.fst cBase tBase ≫ a) (pullback.snd cBase tBase ≫ s₃)
  let b₆ : B ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K) ⨯
      projectiveParameters K (Fin 4) 6 :=
    Limits.prod.lift (pullback.fst cBase tBase ≫ a) (pullback.snd cBase tBase ≫ s₆)
  π '' (b₃ ⁻¹' Set.range (projectiveUniversalIncidence K (Fin 4) 3) ∩
    b₆ ⁻¹' Set.range (projectiveUniversalIncidence K (Fin 4) 6))

/- Properness of the intermediate curve makes the simultaneous cubic--sextic
   bad locus closed in the third-cubic parameter scheme.  Thus the remaining
   Bertini task is to prove that this closed set is proper, rather than to
   establish any further projection or closed-image assertion. -/
theorem isClosed_projectiveCubicSexticCommonZeroBadLocus
    {C T : Scheme.{u}}
    (cBase : C ⟶ Spec (.of K)) [IsProper cBase]
    (tBase : T ⟶ Spec (.of K))
    (a : C ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (s₃ : T ⟶ projectiveParameters K (Fin 4) 3)
    (s₆ : T ⟶ projectiveParameters K (Fin 4) 6) :
    IsClosed (projectiveCubicSexticCommonZeroBadLocus cBase tBase a s₃ s₆) := by
  let B := pullback cBase tBase
  let π : B ⟶ T := pullback.snd cBase tBase
  let b₃ : B ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K) ⨯
      projectiveParameters K (Fin 4) 3 :=
    Limits.prod.lift (pullback.fst cBase tBase ≫ a) (pullback.snd cBase tBase ≫ s₃)
  let b₆ : B ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K) ⨯
      projectiveParameters K (Fin 4) 6 :=
    Limits.prod.lift (pullback.fst cBase tBase ≫ a) (pullback.snd cBase tBase ≫ s₆)
  letI : IsProper π := by
    dsimp [π]
    infer_instance
  change IsClosed (π '' (b₃ ⁻¹' Set.range
    (projectiveUniversalIncidence K (Fin 4) 3) ∩ b₆ ⁻¹' Set.range
      (projectiveUniversalIncidence K (Fin 4) 6)))
  apply π.isClosedMap
  exact ((isClosed_range_projectiveUniversalIncidence K (Fin 4) 3).preimage
    b₃.continuous).inter
    ((isClosed_range_projectiveUniversalIncidence K (Fin 4) 6).preimage
      b₆.continuous)

/- The actual singular-member condition uses all four maximal Jacobian
   minors at the same point.  This carrier-level locus records a cubic and
   four sextics over one parameter space, and asks for a common projective
   zero on the intermediate curve.  It is the closed incidence locus needed
   for the global Jacobian criterion; the one-sextic construction above is
   its individual-chart building block. -/
noncomputable def projectiveCubicAllSexticCommonZeroBadLocus
    {C T : Scheme.{u}}
    (cBase : C ⟶ Spec (.of K)) (tBase : T ⟶ Spec (.of K))
    (a : C ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (s₃ : T ⟶ projectiveParameters K (Fin 4) 3)
    (s₆ : ∀ j : Fin 4, T ⟶ projectiveParameters K (Fin 4) 6) : Set T :=
  let B := pullback cBase tBase
  let π : B ⟶ T := pullback.snd cBase tBase
  let b₃ : B ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K) ⨯
      projectiveParameters K (Fin 4) 3 :=
    Limits.prod.lift (pullback.fst cBase tBase ≫ a) (pullback.snd cBase tBase ≫ s₃)
  let b₆ : ∀ j : Fin 4,
      B ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K) ⨯
        projectiveParameters K (Fin 4) 6 := fun j =>
    Limits.prod.lift (pullback.fst cBase tBase ≫ a)
      (pullback.snd cBase tBase ≫ s₆ j)
  π '' (b₃ ⁻¹' Set.range (projectiveUniversalIncidence K (Fin 4) 3) ∩
    ⋂ j : Fin 4,
      b₆ j ⁻¹' Set.range (projectiveUniversalIncidence K (Fin 4) 6))

/- Membership in the simultaneous bad locus is exactly a point of the
   curve--parameter pullback at which the cubic and all four sextic equations
   lie in their universal incidence loci. -/
theorem mem_projectiveCubicAllSexticCommonZeroBadLocus_iff
    {C T : Scheme.{u}}
    (cBase : C ⟶ Spec (.of K)) (tBase : T ⟶ Spec (.of K))
    (a : C ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (s₃ : T ⟶ projectiveParameters K (Fin 4) 3)
    (s₆ : Fin 4 → (T ⟶ projectiveParameters K (Fin 4) 6))
    (t : T) :
    t ∈ projectiveCubicAllSexticCommonZeroBadLocus cBase tBase a s₃ s₆ ↔
      ∃ z : (CategoryTheory.Limits.pullback cBase tBase : Scheme.{u}),
        pullback.snd cBase tBase z = t ∧
        Limits.prod.lift (pullback.fst cBase tBase ≫ a)
            (pullback.snd cBase tBase ≫ s₃) z ∈
          Set.range (projectiveUniversalIncidence K (Fin 4) 3) ∧
        ∀ j : Fin 4,
          Limits.prod.lift (pullback.fst cBase tBase ≫ a)
              (pullback.snd cBase tBase ≫ s₆ j) z ∈
            Set.range (projectiveUniversalIncidence K (Fin 4) 6) := by
  simp only [projectiveCubicAllSexticCommonZeroBadLocus, Set.mem_image,
    Set.mem_inter_iff, Set.mem_preimage, Set.mem_iInter]
  constructor
  · rintro ⟨z, ⟨h₃, h₆⟩, rfl⟩
    exact ⟨z, rfl, h₃, h₆⟩
  · rintro ⟨z, rfl, h₃, h₆⟩
    exact ⟨z, ⟨h₃, h₆⟩, rfl⟩

/- A curve point and a parameter point over the same field determine the
   required pullback witness once the five incidence conditions are known. -/
theorem mem_projectiveCubicAllSexticCommonZeroBadLocus_of_fieldPoint
    {C T : Scheme.{u}} {L : Type u} [Field L]
    (cBase : C ⟶ Spec (.of K)) (tBase : T ⟶ Spec (.of K))
    (a : C ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (s₃ : T ⟶ projectiveParameters K (Fin 4) 3)
    (s₆ : Fin 4 → (T ⟶ projectiveParameters K (Fin 4) 6))
    (b : K →+* L) (c : Spec (.of L) ⟶ C) (t : Spec (.of L) ⟶ T)
    (hc : c ≫ cBase = Spec.map (CommRingCat.ofHom b))
    (ht : t ≫ tBase = Spec.map (CommRingCat.ofHom b))
    (h₃ : Limits.prod.lift (c ≫ a) (t ≫ s₃) (IsLocalRing.closedPoint L) ∈
      Set.range (projectiveUniversalIncidence K (Fin 4) 3))
    (h₆ : ∀ j : Fin 4,
      Limits.prod.lift (c ≫ a) (t ≫ s₆ j) (IsLocalRing.closedPoint L) ∈
        Set.range (projectiveUniversalIncidence K (Fin 4) 6)) :
    t (IsLocalRing.closedPoint L) ∈
      projectiveCubicAllSexticCommonZeroBadLocus cBase tBase a s₃ s₆ := by
  let zmap : Spec (.of L) ⟶ CategoryTheory.Limits.pullback cBase tBase :=
    pullback.lift c t (hc.trans ht.symm)
  have hzfst : zmap ≫ pullback.fst cBase tBase = c := by
    dsimp [zmap]
    exact pullback.lift_fst _ _ _
  have hzsnd : zmap ≫ pullback.snd cBase tBase = t := by
    dsimp [zmap]
    exact pullback.lift_snd _ _ _
  apply (mem_projectiveCubicAllSexticCommonZeroBadLocus_iff
    cBase tBase a s₃ s₆ _).mpr
  refine ⟨zmap (IsLocalRing.closedPoint L), ?_, ?_, ?_⟩
  · exact congrArg (fun f : Spec (.of L) ⟶ T => f (IsLocalRing.closedPoint L)) hzsnd
  · let b₃ := Limits.prod.lift (pullback.fst cBase tBase ≫ a)
      (pullback.snd cBase tBase ≫ s₃)
    have hpair : zmap ≫ b₃ = Limits.prod.lift (c ≫ a) (t ≫ s₃) := by
      apply Limits.prod.hom_ext
      · dsimp [b₃]
        rw [Category.assoc, Limits.prod.lift_fst, ← Category.assoc, hzfst]
        exact (Limits.prod.lift_fst _ _).symm
      · dsimp [b₃]
        rw [Category.assoc, Limits.prod.lift_snd, ← Category.assoc, hzsnd]
        exact (Limits.prod.lift_snd _ _).symm
    change (zmap ≫ b₃) (IsLocalRing.closedPoint L) ∈ _
    rw [hpair]
    exact h₃
  · intro j
    let b₆ := Limits.prod.lift (pullback.fst cBase tBase ≫ a)
      (pullback.snd cBase tBase ≫ s₆ j)
    have hpair : zmap ≫ b₆ = Limits.prod.lift (c ≫ a) (t ≫ s₆ j) := by
      apply Limits.prod.hom_ext
      · dsimp [b₆]
        rw [Category.assoc, Limits.prod.lift_fst, ← Category.assoc, hzfst]
        exact (Limits.prod.lift_fst _ _).symm
      · dsimp [b₆]
        rw [Category.assoc, Limits.prod.lift_snd, ← Category.assoc, hzsnd]
        exact (Limits.prod.lift_snd _ _).symm
    change (zmap ≫ b₆) (IsLocalRing.closedPoint L) ∈ _
    rw [hpair]
    exact h₆ j

/- An actual point of a field-valued hypersurface yields incidence at any
   ambient and parameter maps identified with its ambient and classifying
   morphisms. -/
theorem projectiveClassifyingIncidence_mem_range_of_fieldPoint
    {L : Type u} [Field L] {d : ℕ}
    (p : MvPolynomial (Fin 4) L) (hp : p.IsHomogeneous d) (hne : p ≠ 0)
    (b : K →+* L) (q : Spec (.of L) ⟶ hypersurface p hp)
    (hqBase : q ≫ hypersurfaceToBase p hp = 𝟙 _)
    (a : Spec (.of L) ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (ha : q ≫ hypersurfaceToAmbient p hp ≫ ambientCoefficientMap b = a)
    (s : Spec (.of L) ⟶ projectiveParameters K (Fin 4) d)
    (hs : s = projectiveClassifyingMap p hp hne b) :
    Limits.prod.lift a s (IsLocalRing.closedPoint L) ∈
      Set.range (projectiveUniversalIncidence K (Fin 4) d) := by
  let v := Limits.prod.lift
    (hypersurfaceToAmbient p hp ≫ ambientCoefficientMap b)
    (hypersurfaceToBase p hp ≫ projectiveClassifyingMap p hp hne b)
  have hv : q ≫ v = Limits.prod.lift a s := by
    apply Limits.prod.hom_ext
    · dsimp [v]
      rw [Category.assoc, Limits.prod.lift_fst]
      rw [Limits.prod.lift_fst]
      exact ha
    · dsimp [v]
      rw [Category.assoc, Limits.prod.lift_snd]
      rw [← Category.assoc, hqBase, Category.id_comp, ← hs]
      exact (Limits.prod.lift_snd _ _).symm
  have hinc := projectiveClassifyingIncidence_mem_range
    (R := K) p hp hne b (q (IsLocalRing.closedPoint L))
  change (q ≫ v) (IsLocalRing.closedPoint L) ∈ _ at hinc
  rw [hv] at hinc
  exact hinc

/- Five nonzero equations, presented by their actual hypersurface points and
   classifying maps over one field-valued curve--parameter pair, give a point
   of the simultaneous cubic--four-sextic bad locus. -/
theorem mem_projectiveCubicAllSexticCommonZeroBadLocus_of_classifyingPoints
    {C T : Scheme.{u}} {L : Type u} [Field L]
    (cBase : C ⟶ Spec (.of K)) (tBase : T ⟶ Spec (.of K))
    (a : C ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (s₃ : T ⟶ projectiveParameters K (Fin 4) 3)
    (s₆ : Fin 4 → (T ⟶ projectiveParameters K (Fin 4) 6))
    (b : K →+* L) (c : Spec (.of L) ⟶ C) (t : Spec (.of L) ⟶ T)
    (hc : c ≫ cBase = Spec.map (CommRingCat.ofHom b))
    (ht : t ≫ tBase = Spec.map (CommRingCat.ofHom b))
    (p₃ : MvPolynomial (Fin 4) L) (hp₃ : p₃.IsHomogeneous 3) (hne₃ : p₃ ≠ 0)
    (q₃ : Spec (.of L) ⟶ hypersurface p₃ hp₃)
    (hq₃Base : q₃ ≫ hypersurfaceToBase p₃ hp₃ = 𝟙 _)
    (hq₃Ambient : q₃ ≫ hypersurfaceToAmbient p₃ hp₃ ≫ ambientCoefficientMap b = c ≫ a)
    (hs₃ : t ≫ s₃ = projectiveClassifyingMap p₃ hp₃ hne₃ b)
    (p₆ : Fin 4 → MvPolynomial (Fin 4) L)
    (hp₆ : ∀ j, (p₆ j).IsHomogeneous 6) (hne₆ : ∀ j, p₆ j ≠ 0)
    (q₆ : ∀ j, Spec (.of L) ⟶ hypersurface (p₆ j) (hp₆ j))
    (hq₆Base : ∀ j, q₆ j ≫ hypersurfaceToBase (p₆ j) (hp₆ j) = 𝟙 _)
    (hq₆Ambient : ∀ j,
      q₆ j ≫ hypersurfaceToAmbient (p₆ j) (hp₆ j) ≫ ambientCoefficientMap b = c ≫ a)
    (hs₆ : ∀ j, t ≫ s₆ j = projectiveClassifyingMap (p₆ j) (hp₆ j) (hne₆ j) b) :
    t (IsLocalRing.closedPoint L) ∈
      projectiveCubicAllSexticCommonZeroBadLocus cBase tBase a s₃ s₆ := by
  apply mem_projectiveCubicAllSexticCommonZeroBadLocus_of_fieldPoint
    cBase tBase a s₃ s₆ b c t hc ht
  · exact projectiveClassifyingIncidence_mem_range_of_fieldPoint
      p₃ hp₃ hne₃ b q₃ hq₃Base (c ≫ a) hq₃Ambient (t ≫ s₃) hs₃
  · intro j
    exact projectiveClassifyingIncidence_mem_range_of_fieldPoint
      (p₆ j) (hp₆ j) (hne₆ j) b (q₆ j) (hq₆Base j)
      (c ≫ a) (hq₆Ambient j) (t ≫ s₆ j) (hs₆ j)

/- Properness of the intermediate curve makes the true simultaneous
   cubic--all-Jacobian-minors incidence closed in the parameter scheme. -/
theorem isClosed_projectiveCubicAllSexticCommonZeroBadLocus
    {C T : Scheme.{u}}
    (cBase : C ⟶ Spec (.of K)) [IsProper cBase]
    (tBase : T ⟶ Spec (.of K))
    (a : C ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (s₃ : T ⟶ projectiveParameters K (Fin 4) 3)
    (s₆ : ∀ j : Fin 4, T ⟶ projectiveParameters K (Fin 4) 6) :
    IsClosed
      (projectiveCubicAllSexticCommonZeroBadLocus cBase tBase a s₃ s₆) := by
  let B := pullback cBase tBase
  let π : B ⟶ T := pullback.snd cBase tBase
  let b₃ : B ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K) ⨯
      projectiveParameters K (Fin 4) 3 :=
    Limits.prod.lift (pullback.fst cBase tBase ≫ a) (pullback.snd cBase tBase ≫ s₃)
  let b₆ : ∀ j : Fin 4,
      B ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K) ⨯
        projectiveParameters K (Fin 4) 6 := fun j =>
    Limits.prod.lift (pullback.fst cBase tBase ≫ a)
      (pullback.snd cBase tBase ≫ s₆ j)
  letI : IsProper π := by
    dsimp [π]
    infer_instance
  change IsClosed (π '' (b₃ ⁻¹' Set.range
    (projectiveUniversalIncidence K (Fin 4) 3) ∩
      ⋂ j : Fin 4,
        b₆ j ⁻¹' Set.range (projectiveUniversalIncidence K (Fin 4) 6)))
  apply π.isClosedMap
  exact ((isClosed_range_projectiveUniversalIncidence K (Fin 4) 3).preimage
    b₃.continuous).inter
    (isClosed_iInter fun j =>
      (isClosed_range_projectiveUniversalIncidence K (Fin 4) 6).preimage
        (b₆ j).continuous)

/- A proper simultaneous singular-member locus is avoided by the generic
   projective parameter. -/
theorem genericFunctionField_closedPoint_avoids_projectiveCubicAllSexticCommonZeroBadLocus
    {C T : Scheme.{u}}
    (cBase : C ⟶ Spec (.of K)) [IsProper cBase]
    (tBase : T ⟶ Spec (.of K)) [IsIntegral T]
    (a : C ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (s₃ : T ⟶ projectiveParameters K (Fin 4) 3)
    (s₆ : ∀ j : Fin 4, T ⟶ projectiveParameters K (Fin 4) 6)
    (hproper : projectiveCubicAllSexticCommonZeroBadLocus
      cBase tBase a s₃ s₆ ≠ Set.univ) :
    T.fromSpecStalk (genericPoint T) (IsLocalRing.closedPoint T.functionField) ∉
      projectiveCubicAllSexticCommonZeroBadLocus cBase tBase a s₃ s₆ := by
  exact genericFunctionField_closedPoint_avoids_proper_closed T
    (isClosed_projectiveCubicAllSexticCommonZeroBadLocus
      cBase tBase a s₃ s₆) hproper

/- One good parameter is an equivalent concrete way to supply properness for
   the simultaneous singular-member locus. -/
theorem
    genericFunctionField_closedPoint_avoids_projectiveCubicAllSexticCommonZeroBadLocus_of_exists
    {C T : Scheme.{u}}
    (cBase : C ⟶ Spec (.of K)) [IsProper cBase]
    (tBase : T ⟶ Spec (.of K)) [IsIntegral T]
    (a : C ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (s₃ : T ⟶ projectiveParameters K (Fin 4) 3)
    (s₆ : ∀ j : Fin 4, T ⟶ projectiveParameters K (Fin 4) 6)
    (hgood : ∃ t : T,
      t ∉ projectiveCubicAllSexticCommonZeroBadLocus cBase tBase a s₃ s₆) :
    T.fromSpecStalk (genericPoint T) (IsLocalRing.closedPoint T.functionField) ∉
      projectiveCubicAllSexticCommonZeroBadLocus cBase tBase a s₃ s₆ := by
  apply genericFunctionField_closedPoint_avoids_projectiveCubicAllSexticCommonZeroBadLocus
    cBase tBase a s₃ s₆
  rintro hbad
  obtain ⟨t, ht⟩ := hgood
  exact ht (by rw [hbad]; exact Set.mem_univ t)

/- Once one good parameter proves that the paired bad locus is proper, the
   generic parameter avoids it.  This is the exact generic-point conclusion
   used by the selected-cubic Bertini branch. -/
theorem genericFunctionField_closedPoint_avoids_projectiveCubicSexticCommonZeroBadLocus
    {C T : Scheme.{u}}
    (cBase : C ⟶ Spec (.of K)) [IsProper cBase]
    (tBase : T ⟶ Spec (.of K)) [IsIntegral T]
    (a : C ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (s₃ : T ⟶ projectiveParameters K (Fin 4) 3)
    (s₆ : T ⟶ projectiveParameters K (Fin 4) 6)
    (hproper : projectiveCubicSexticCommonZeroBadLocus cBase tBase a s₃ s₆ ≠
      Set.univ) :
    T.fromSpecStalk (genericPoint T) (IsLocalRing.closedPoint T.functionField) ∉
      projectiveCubicSexticCommonZeroBadLocus cBase tBase a s₃ s₆ := by
  exact genericFunctionField_closedPoint_avoids_proper_closed T
    (isClosed_projectiveCubicSexticCommonZeroBadLocus cBase tBase a s₃ s₆) hproper

/- A single parameter outside the paired incidence supplies the properness
   premise of the preceding generic avoidance theorem. -/
theorem genericFunctionField_closedPoint_avoids_projectiveCubicSexticCommonZeroBadLocus_of_exists
    {C T : Scheme.{u}}
    (cBase : C ⟶ Spec (.of K)) [IsProper cBase]
    (tBase : T ⟶ Spec (.of K)) [IsIntegral T]
    (a : C ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (s₃ : T ⟶ projectiveParameters K (Fin 4) 3)
    (s₆ : T ⟶ projectiveParameters K (Fin 4) 6)
    (hgood : ∃ t : T,
      t ∉ projectiveCubicSexticCommonZeroBadLocus cBase tBase a s₃ s₆) :
    T.fromSpecStalk (genericPoint T) (IsLocalRing.closedPoint T.functionField) ∉
      projectiveCubicSexticCommonZeroBadLocus cBase tBase a s₃ s₆ := by
  apply genericFunctionField_closedPoint_avoids_projectiveCubicSexticCommonZeroBadLocus
    cBase tBase a s₃ s₆
  rintro hbad
  obtain ⟨t, ht⟩ := hgood
  exact ht (by rw [hbad]; exact Set.mem_univ t)

/- Specialize the paired cubic--Jacobian incidence to an actual finite frame
   in a cubic linear system.  The parameter supplies both the third cubic and
   its degree-six Jacobian determinant on the intermediate curve `(p = q = 0)`.
   Linear independence of the two displayed frames makes both projective
   parameter maps available. -/
noncomputable def tripleCompleteIntersectionChartJacobianFramedCommonZeroBadLocus
    {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3) (j : Fin 4)
    (W : Submodule K (homogeneousSubmodule (Fin 4) K 3))
    (v : Fin n → W)
    (hv₃ : LinearIndependent K
      (fun i ↦ (v i : homogeneousSubmodule (Fin 4) K 3)))
    (hv₆ : LinearIndependent K
      (tripleCompleteIntersectionChartJacobianRestrictedFrame p q hp hq j W v)) :
    Set (projectiveLinearSystemParameters (K := K) (τ := Fin n)) := by
  let hz : (0 : MvPolynomial (Fin 4) K).IsHomogeneous 3 :=
    MvPolynomial.isHomogeneous_zero (Fin 4) K 3
  let I := tripleCompleteIntersectionHomogeneousIdeal p q 0 hp hq hz
  let e₃ : Fin (Fintype.card (Monomials (Fin 4) 3)) ≃ Monomials (Fin 4) 3 :=
    (Fintype.equivFin _).symm
  exact projectiveCubicSexticCommonZeroBadLocus
    (toBase I)
    (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)))
    (quotientProjMap I)
    (homogeneousFrameToParameters 3 e₃
      (fun i ↦ (v i : homogeneousSubmodule (Fin 4) K 3)) hv₃)
    (tripleCompleteIntersectionChartJacobianRestrictedFrameProjectiveSystem
      p q hp hq j W v hv₆)

/- Properness of the intermediate projective complete intersection proves
   that the framed simultaneous bad locus is closed in the third-cubic
   parameter space. -/
theorem isClosed_tripleCompleteIntersectionChartJacobianFramedCommonZeroBadLocus
    {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3) (j : Fin 4)
    (W : Submodule K (homogeneousSubmodule (Fin 4) K 3))
    (v : Fin n → W)
    (hv₃ : LinearIndependent K
      (fun i ↦ (v i : homogeneousSubmodule (Fin 4) K 3)))
    (hv₆ : LinearIndependent K
      (tripleCompleteIntersectionChartJacobianRestrictedFrame p q hp hq j W v)) :
    IsClosed
      (tripleCompleteIntersectionChartJacobianFramedCommonZeroBadLocus
        p q hp hq j W v hv₃ hv₆) := by
  let hz : (0 : MvPolynomial (Fin 4) K).IsHomogeneous 3 :=
    MvPolynomial.isHomogeneous_zero (Fin 4) K 3
  let I := tripleCompleteIntersectionHomogeneousIdeal p q 0 hp hq hz
  let e₃ : Fin (Fintype.card (Monomials (Fin 4) 3)) ≃ Monomials (Fin 4) 3 :=
    (Fintype.equivFin _).symm
  exact isClosed_projectiveCubicSexticCommonZeroBadLocus
    (toBase I)
    (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)))
    (quotientProjMap I)
    (homogeneousFrameToParameters 3 e₃
      (fun i ↦ (v i : homogeneousSubmodule (Fin 4) K 3)) hv₃)
    (tripleCompleteIntersectionChartJacobianRestrictedFrameProjectiveSystem
      p q hp hq j W v hv₆)

/- Bundle compatible cubic lifts of a basis of the Jacobian image restricted
   to `W`.  Unlike an arbitrary frame of `W`, these coordinates discard the
   kernel of the Jacobian map while every lifted cubic still belongs to `W`.
   This is the coordinate system needed when `W` is the kernel of restriction
   to the completed finite datum. -/
theorem exists_tripleCompleteIntersectionChartJacobianRestrictedImageBasis
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3) (j : Fin 4)
    (W : Submodule K (homogeneousSubmodule (Fin 4) K 3)) :
    ∃ n : ℕ, Nonempty (Module.Basis (Fin n) K
      (LinearMap.range
        (tripleCompleteIntersectionChartJacobianHomogeneousLinearMap_restrict
          p q hp hq j W))) := by
  exact @exists_fin_linearMapImageBasis K _ W _ _
    (homogeneousSubmodule (Fin 4) K 6) _ _
    (tripleCompleteIntersectionChartJacobianHomogeneousLinearMap_restrict
      p q hp hq j W) (FiniteDimensional.finiteDimensional_submodule W)

noncomputable def
    tripleCompleteIntersectionChartJacobianRestrictedImagePairedFrame
    {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3) (j : Fin 4)
    (W : Submodule K (homogeneousSubmodule (Fin 4) K 3))
    (b : Module.Basis (Fin n) K
      (LinearMap.range
        (tripleCompleteIntersectionChartJacobianHomogeneousLinearMap_restrict
          p q hp hq j W))) :
    @LinearMapPairedIndependentFrame K _ W _ _
      (homogeneousSubmodule (Fin 4) K 6) _ _
      (tripleCompleteIntersectionChartJacobianHomogeneousLinearMap_restrict
        p q hp hq j W) (Fin n) :=
  @linearMapImagePairedIndependentFrame K _ W _ _
    (homogeneousSubmodule (Fin 4) K 6) _ _
    (tripleCompleteIntersectionChartJacobianHomogeneousLinearMap_restrict
      p q hp hq j W) (Fin n) b

noncomputable def
    tripleCompleteIntersectionChartJacobianRestrictedImageLiftFrame
    {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3) (j : Fin 4)
    (W : Submodule K (homogeneousSubmodule (Fin 4) K 3))
    (b : Module.Basis (Fin n) K
      (LinearMap.range
        (tripleCompleteIntersectionChartJacobianHomogeneousLinearMap_restrict
          p q hp hq j W))) : IndependentFrame K (Fin n) W :=
  (tripleCompleteIntersectionChartJacobianRestrictedImagePairedFrame
    p q hp hq j W b).source

/- The lifted restricted-image basis, viewed as an independent frame of
   ambient cubic equations. -/
noncomputable def
    tripleCompleteIntersectionChartJacobianRestrictedImageCubicFrame
    {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3) (j : Fin 4)
    (W : Submodule K (homogeneousSubmodule (Fin 4) K 3))
    (b : Module.Basis (Fin n) K
      (LinearMap.range
        (tripleCompleteIntersectionChartJacobianHomogeneousLinearMap_restrict
          p q hp hq j W))) :
    IndependentFrame K (Fin n) (homogeneousSubmodule (Fin 4) K 3) :=
  (tripleCompleteIntersectionChartJacobianRestrictedImageLiftFrame
    p q hp hq j W b).submoduleCoe W

/- The same restricted-image basis as an independent frame of Jacobian
   sextics.  It has the same index type as the preceding cubic frame. -/
noncomputable def
    tripleCompleteIntersectionChartJacobianRestrictedImageSexticFrame
    {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3) (j : Fin 4)
    (W : Submodule K (homogeneousSubmodule (Fin 4) K 3))
    (b : Module.Basis (Fin n) K
      (LinearMap.range
        (tripleCompleteIntersectionChartJacobianHomogeneousLinearMap_restrict
          p q hp hq j W))) :
    IndependentFrame K (Fin n) (homogeneousSubmodule (Fin 4) K 6) :=
  (tripleCompleteIntersectionChartJacobianRestrictedImagePairedFrame
    p q hp hq j W b).target

/- Coordinatewise compatibility is part of the paired frame itself. -/
@[simp] theorem
    tripleCompleteIntersectionChartJacobianRestrictedImagePairedFrame_map
    {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3) (j : Fin 4)
    (W : Submodule K (homogeneousSubmodule (Fin 4) K 3))
    (b : Module.Basis (Fin n) K
      (LinearMap.range
        (tripleCompleteIntersectionChartJacobianHomogeneousLinearMap_restrict
          p q hp hq j W))) (i : Fin n) :
    tripleCompleteIntersectionChartJacobianHomogeneousLinearMap_restrict
        p q hp hq j W
        ((tripleCompleteIntersectionChartJacobianRestrictedImagePairedFrame
          p q hp hq j W b).source.toFun i) =
      (tripleCompleteIntersectionChartJacobianRestrictedImagePairedFrame
        p q hp hq j W b).target.toFun i :=
  (tripleCompleteIntersectionChartJacobianRestrictedImagePairedFrame
    p q hp hq j W b).map_toFun i

/- The kernel-safe paired bad locus for a prescribed third-cubic system.
   When `W` is a restriction kernel, every cubic in this family vanishes on
   the completed datum, while quotienting by the Jacobian kernel prevents the
   false injectivity requirement present in a raw basis of `W`. -/
noncomputable def
    tripleCompleteIntersectionChartJacobianRestrictedImageCommonZeroBadLocus
    {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3) (j : Fin 4)
    (W : Submodule K (homogeneousSubmodule (Fin 4) K 3))
    (b : Module.Basis (Fin n) K
      (LinearMap.range
        (tripleCompleteIntersectionChartJacobianHomogeneousLinearMap_restrict
          p q hp hq j W))) :
    Set (projectiveLinearSystemParameters (K := K) (τ := Fin n)) := by
  let c := tripleCompleteIntersectionChartJacobianRestrictedImageCubicFrame
    p q hp hq j W b
  let s := tripleCompleteIntersectionChartJacobianRestrictedImageSexticFrame
    p q hp hq j W b
  let hz : (0 : MvPolynomial (Fin 4) K).IsHomogeneous 3 :=
    MvPolynomial.isHomogeneous_zero (Fin 4) K 3
  let I := tripleCompleteIntersectionHomogeneousIdeal p q 0 hp hq hz
  let e₃ : Fin (Fintype.card (Monomials (Fin 4) 3)) ≃ Monomials (Fin 4) 3 :=
    (Fintype.equivFin _).symm
  let e₆ : Fin (Fintype.card (Monomials (Fin 4) 6)) ≃ Monomials (Fin 4) 6 :=
    (Fintype.equivFin _).symm
  exact projectiveCubicSexticCommonZeroBadLocus
    (toBase I)
    (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)))
    (quotientProjMap I)
    (homogeneousFrameToParameters 3 e₃ c.toFun c.linearIndependent)
    (homogeneousFrameToParameters 6 e₆ s.toFun s.linearIndependent)

/- Properness of the intermediate complete intersection makes the
   restricted-image simultaneous bad locus closed. -/
theorem
    isClosed_tripleCompleteIntersectionChartJacobianRestrictedImageCommonZeroBadLocus
    {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3) (j : Fin 4)
    (W : Submodule K (homogeneousSubmodule (Fin 4) K 3))
    (b : Module.Basis (Fin n) K
      (LinearMap.range
        (tripleCompleteIntersectionChartJacobianHomogeneousLinearMap_restrict
          p q hp hq j W))) :
    IsClosed
      (tripleCompleteIntersectionChartJacobianRestrictedImageCommonZeroBadLocus
        p q hp hq j W b) := by
  let c := tripleCompleteIntersectionChartJacobianRestrictedImageCubicFrame
    p q hp hq j W b
  let s := tripleCompleteIntersectionChartJacobianRestrictedImageSexticFrame
    p q hp hq j W b
  let hz : (0 : MvPolynomial (Fin 4) K).IsHomogeneous 3 :=
    MvPolynomial.isHomogeneous_zero (Fin 4) K 3
  let I := tripleCompleteIntersectionHomogeneousIdeal p q 0 hp hq hz
  let e₃ : Fin (Fintype.card (Monomials (Fin 4) 3)) ≃ Monomials (Fin 4) 3 :=
    (Fintype.equivFin _).symm
  let e₆ : Fin (Fintype.card (Monomials (Fin 4) 6)) ≃ Monomials (Fin 4) 6 :=
    (Fintype.equivFin _).symm
  change IsClosed (projectiveCubicSexticCommonZeroBadLocus
    (toBase I)
    (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)))
    (quotientProjMap I)
    (homogeneousFrameToParameters 3 e₃ c.toFun c.linearIndependent)
    (homogeneousFrameToParameters 6 e₆ s.toFun s.linearIndependent))
  exact isClosed_projectiveCubicSexticCommonZeroBadLocus
    (toBase I)
    (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)))
    (quotientProjMap I)
    (homogeneousFrameToParameters 3 e₃ c.toFun c.linearIndependent)
    (homogeneousFrameToParameters 6 e₆ s.toFun s.linearIndependent)

/- Specialize the kernel-safe image construction to the cubic system that
   vanishes on a finite homogeneous datum represented by the restriction map
   `homogeneousSectionRestriction`. -/
noncomputable def
    tripleCompleteIntersectionChartJacobianRestrictionKernelImageCommonZeroBadLocus
    {B : Type u} [CommRing B] [Algebra K B] {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3) (j : Fin 4)
    (x : Fin 4 → B)
    (b : Module.Basis (Fin n) K
      (LinearMap.range
        (tripleCompleteIntersectionChartJacobianHomogeneousLinearMap_restrict
          p q hp hq j
          (LinearMap.ker (homogeneousSectionRestriction (K := K) x 3))))) :
    Set (projectiveLinearSystemParameters (K := K) (τ := Fin n)) :=
  tripleCompleteIntersectionChartJacobianRestrictedImageCommonZeroBadLocus
    p q hp hq j (LinearMap.ker (homogeneousSectionRestriction (K := K) x 3)) b

theorem
    isClosed_tripleCompleteIntersectionChartJacobianRestrictionKernelImageCommonZeroBadLocus
    {B : Type u} [CommRing B] [Algebra K B] {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3) (j : Fin 4)
    (x : Fin 4 → B)
    (b : Module.Basis (Fin n) K
      (LinearMap.range
        (tripleCompleteIntersectionChartJacobianHomogeneousLinearMap_restrict
          p q hp hq j
          (LinearMap.ker (homogeneousSectionRestriction (K := K) x 3))))) :
    IsClosed
      (tripleCompleteIntersectionChartJacobianRestrictionKernelImageCommonZeroBadLocus
        p q hp hq j x b) := by
  exact
    isClosed_tripleCompleteIntersectionChartJacobianRestrictedImageCommonZeroBadLocus
      p q hp hq j
      (LinearMap.ker (homogeneousSectionRestriction (K := K) x 3)) b

/- One good member of the restriction-kernel image system forces its generic
   projective parameter to avoid the paired cubic--Jacobian bad locus. -/
theorem
    genericFunctionField_closedPoint_avoids_tripleCompleteIntersectionChartJacobianRestrictionKernelImageCommonZeroBadLocus_of_exists
    {B : Type u} [CommRing B] [Algebra K B] {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3) (j : Fin 4)
    (x : Fin 4 → B)
    (b : Module.Basis (Fin n) K
      (LinearMap.range
        (tripleCompleteIntersectionChartJacobianHomogeneousLinearMap_restrict
          p q hp hq j
          (LinearMap.ker (homogeneousSectionRestriction (K := K) x 3)))))
    [IsIntegral (projectiveLinearSystemParameters (K := K) (τ := Fin n))]
    (hgood : ∃ t : projectiveLinearSystemParameters (K := K) (τ := Fin n),
      t ∉
        tripleCompleteIntersectionChartJacobianRestrictionKernelImageCommonZeroBadLocus
          p q hp hq j x b) :
    (projectiveLinearSystemParameters (K := K) (τ := Fin n)).fromSpecStalk
        (genericPoint (projectiveLinearSystemParameters (K := K) (τ := Fin n)))
        (IsLocalRing.closedPoint
          (projectiveLinearSystemParameters (K := K) (τ := Fin n)).functionField) ∉
      tripleCompleteIntersectionChartJacobianRestrictionKernelImageCommonZeroBadLocus
        p q hp hq j x b := by
  apply genericFunctionField_closedPoint_avoids_proper_closed
    (projectiveLinearSystemParameters (K := K) (τ := Fin n))
    (isClosed_tripleCompleteIntersectionChartJacobianRestrictionKernelImageCommonZeroBadLocus
      p q hp hq j x b)
  rintro hbad
  obtain ⟨t, ht⟩ := hgood
  exact ht (by rw [hbad]; exact Set.mem_univ t)

/- Use the canonical basis of the Jacobian image and its cubic lifts to put
   both equations over the same projective parameter space.  This version
   avoids any injectivity hypothesis on the original cubic system. -/
noncomputable def tripleCompleteIntersectionChartJacobianImageCommonZeroBadLocus
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3) (j : Fin 4) :
    Set (projectiveLinearSystemParameters (K := K)
      (τ := Fin (Module.finrank K
        (LinearMap.range (tripleCompleteIntersectionChartJacobianHomogeneousLinearMap
          p q hp hq j))))) := by
  let hz : (0 : MvPolynomial (Fin 4) K).IsHomogeneous 3 :=
    MvPolynomial.isHomogeneous_zero (Fin 4) K 3
  let I := tripleCompleteIntersectionHomogeneousIdeal p q 0 hp hq hz
  let b := tripleCompleteIntersectionChartJacobianImageBasis p q hp hq j
  let e₃ : Fin (Fintype.card (Monomials (Fin 4) 3)) ≃ Monomials (Fin 4) 3 :=
    (Fintype.equivFin _).symm
  exact projectiveCubicSexticCommonZeroBadLocus
    (toBase I)
    (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule
      (Fin (Module.finrank K
        (LinearMap.range (tripleCompleteIntersectionChartJacobianHomogeneousLinearMap
          p q hp hq j)))) K)))
    (quotientProjMap I)
    (homogeneousFrameToParameters 3 e₃
      (tripleCompleteIntersectionChartJacobianImageLiftFrame p q hp hq j b)
      (tripleCompleteIntersectionChartJacobianImageLiftFrame_linearIndependent
        p q hp hq j b))
    (tripleCompleteIntersectionChartJacobianImageProjectiveSystem p q hp hq j)

/- The canonical image-coordinate bad locus is closed.  Its properness is
   now the exact good-member statement still needed for the Bertini step. -/
theorem isClosed_tripleCompleteIntersectionChartJacobianImageCommonZeroBadLocus
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3) (j : Fin 4) :
    IsClosed
      (tripleCompleteIntersectionChartJacobianImageCommonZeroBadLocus
        p q hp hq j) := by
  let hz : (0 : MvPolynomial (Fin 4) K).IsHomogeneous 3 :=
    MvPolynomial.isHomogeneous_zero (Fin 4) K 3
  let I := tripleCompleteIntersectionHomogeneousIdeal p q 0 hp hq hz
  let b := tripleCompleteIntersectionChartJacobianImageBasis p q hp hq j
  let e₃ : Fin (Fintype.card (Monomials (Fin 4) 3)) ≃ Monomials (Fin 4) 3 :=
    (Fintype.equivFin _).symm
  exact isClosed_projectiveCubicSexticCommonZeroBadLocus
    (toBase I)
    (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule
      (Fin (Module.finrank K
        (LinearMap.range (tripleCompleteIntersectionChartJacobianHomogeneousLinearMap
          p q hp hq j)))) K)))
    (quotientProjMap I)
    (homogeneousFrameToParameters 3 e₃
      (tripleCompleteIntersectionChartJacobianImageLiftFrame p q hp hq j b)
      (tripleCompleteIntersectionChartJacobianImageLiftFrame_linearIndependent
        p q hp hq j b))
    (tripleCompleteIntersectionChartJacobianImageProjectiveSystem p q hp hq j)

/- The image-system parameter map can now be paired with any ambient family.
   Its pullback of the universal degree-six incidence is the Jacobian bad
   locus for that family. -/
noncomputable def tripleCompleteIntersectionChartJacobianIncidenceParameterMap
    {B : Scheme.{u}}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3) (j : Fin 4)
    (a : B ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (s : B ⟶ projectiveLinearSystemParameters (K := K)
      (τ := Fin (Module.finrank K
        (LinearMap.range (tripleCompleteIntersectionChartJacobianHomogeneousLinearMap
          p q hp hq j))))) :
    B ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K) ⨯
      projectiveParameters K (Fin 4) 6 :=
  Limits.prod.lift a
    (s ≫ tripleCompleteIntersectionChartJacobianImageProjectiveSystem p q hp hq j)

noncomputable def tripleCompleteIntersectionChartJacobianIncidenceBadLocus
    {B : Scheme.{u}}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3) (j : Fin 4)
    (a : B ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (s : B ⟶ projectiveLinearSystemParameters (K := K)
      (τ := Fin (Module.finrank K
        (LinearMap.range (tripleCompleteIntersectionChartJacobianHomogeneousLinearMap
          p q hp hq j))))) : Set B :=
  (tripleCompleteIntersectionChartJacobianIncidenceParameterMap p q hp hq j a s) ⁻¹'
    Set.range (projectiveUniversalIncidence K (Fin 4) 6)

theorem isClosed_tripleCompleteIntersectionChartJacobianIncidenceBadLocus
    {B : Scheme.{u}}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3) (j : Fin 4)
    (a : B ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (s : B ⟶ projectiveLinearSystemParameters (K := K)
      (τ := Fin (Module.finrank K
        (LinearMap.range (tripleCompleteIntersectionChartJacobianHomogeneousLinearMap
          p q hp hq j))))) :
    IsClosed (tripleCompleteIntersectionChartJacobianIncidenceBadLocus p q hp hq j a s) := by
  exact (isClosed_range_projectiveUniversalIncidence K (Fin 4) 6).preimage
    (tripleCompleteIntersectionChartJacobianIncidenceParameterMap p q hp hq j a s).continuous

theorem tripleCompleteIntersectionChartJacobianIncidenceBadLocus_ne_univ_of_exists
    {B : Scheme.{u}}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3) (j : Fin 4)
    (a : B ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (s : B ⟶ projectiveLinearSystemParameters (K := K)
      (τ := Fin (Module.finrank K
        (LinearMap.range (tripleCompleteIntersectionChartJacobianHomogeneousLinearMap
          p q hp hq j)))))
    (hgood : ∃ b : B,
      b ∉ tripleCompleteIntersectionChartJacobianIncidenceBadLocus p q hp hq j a s) :
    tripleCompleteIntersectionChartJacobianIncidenceBadLocus p q hp hq j a s ≠ Set.univ := by
  rintro hbad
  obtain ⟨b, hb⟩ := hgood
  exact hb (by rw [hbad]; exact Set.mem_univ b)

theorem genericFunctionField_closedPoint_avoids_tripleCompleteIntersectionChartJacobianIncidence
    {B : Scheme.{u}} [IsIntegral B]
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3) (j : Fin 4)
    (a : B ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (s : B ⟶ projectiveLinearSystemParameters (K := K)
      (τ := Fin (Module.finrank K
        (LinearMap.range (tripleCompleteIntersectionChartJacobianHomogeneousLinearMap
          p q hp hq j)))))
    (hgood : ∃ b : B,
      b ∉ tripleCompleteIntersectionChartJacobianIncidenceBadLocus p q hp hq j a s) :
    B.fromSpecStalk (genericPoint B) (IsLocalRing.closedPoint B.functionField) ∉
      tripleCompleteIntersectionChartJacobianIncidenceBadLocus p q hp hq j a s := by
  apply genericFunctionField_closedPoint_avoids_projectiveUniversalIncidence_preimage
    K (Fin 4) 6 (tripleCompleteIntersectionChartJacobianIncidenceParameterMap
      p q hp hq j a s)
  exact tripleCompleteIntersectionChartJacobianIncidenceBadLocus_ne_univ_of_exists
    p q hp hq j a s hgood

/-- The square pre-submersive presentation of a normalized chart. -/
noncomputable def tripleCompleteIntersectionChartPrePresentation
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous a) (hq : q.IsHomogeneous b) (hr : r.IsHomogeneous c)
    (j : Fin 4) :
    Algebra.PreSubmersivePresentation K
      (ChartRing (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr) j)
      (Fin 4) (Fin 4) :=
  (Algebra.PreSubmersivePresentation.naive
      (v := tripleCompleteIntersectionChartRelations p q r j)
      (fun i => i) Function.injective_id).ofAlgEquiv
    (tripleCompleteIntersectionChartRelationsEquiv p q r hp hq hr j)

/-- The normalized chart of a projective three-equation intersection has
relative dimension zero. -/
theorem tripleCompleteIntersectionChartPrePresentation_dimension
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous a) (hq : q.IsHomogeneous b) (hr : r.IsHomogeneous c)
    (j : Fin 4) :
    (tripleCompleteIntersectionChartPrePresentation p q r hp hq hr j).dimension = 0 := by
  change ((Algebra.PreSubmersivePresentation.naive
      (v := tripleCompleteIntersectionChartRelations p q r j)
      (fun i => i) Function.injective_id).ofAlgEquiv
        (tripleCompleteIntersectionChartRelationsEquiv p q r hp hq hr j)).dimension = 0
  simp [Algebra.Presentation.dimension]

/-- The determinant of the four-by-four Jacobian of `p`, `q`, `r`, and
`X j - 1`, evaluated in the normalized `j`-th chart. -/
noncomputable def tripleCompleteIntersectionChartJacobian
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous a) (hq : q.IsHomogeneous b) (hr : r.IsHomogeneous c)
    (j : Fin 4) :
    ChartRing (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr) j :=
  (tripleCompleteIntersectionChartJacobianPolynomial p q r j).eval₂
    (chartBaseMap (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr) j)
    (chartCoordinate (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr) j)

/- Passage from a fixed surface chart to a three-cubic quotient chart commutes
   with evaluation of the Jacobian polynomial.  This is the chart-level link
   between the linear bad locus in the ambient cubic system and the actual
   moving complete intersection. -/
theorem tripleCompleteIntersectionChartJacobianPolynomial_eval_chartQuotientMap
    {I J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)}
    (hIJ : I.toIdeal ≤ J.toIdeal)
    (p q r : MvPolynomial (Fin 4) K) (j : Fin 4) :
    chartQuotientMap I J hIJ j
      ((tripleCompleteIntersectionChartJacobianPolynomial p q r j).eval₂
        (chartBaseMap I j) (chartCoordinate I j)) =
      (tripleCompleteIntersectionChartJacobianPolynomial p q r j).eval₂
        (chartBaseMap J j) (chartCoordinate J j) := by
  exact chartQuotientMap_eval₂ I J hIJ j
    (tripleCompleteIntersectionChartJacobianPolynomial p q r j)

/- The surface chart used for the linear system is obtained by taking the
   third equation to be zero.  Its homogeneous ideal is canonically contained
   in the ideal obtained after adjoining any third cubic. -/
theorem tripleCompleteIntersectionHomogeneousIdeal_zero_le
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3)
    (hr : r.IsHomogeneous 3)
    (hz : (0 : MvPolynomial (Fin 4) K).IsHomogeneous 3) :
    (tripleCompleteIntersectionHomogeneousIdeal p q 0 hp hq hz).toIdeal ≤
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr).toIdeal := by
  rw [tripleCompleteIntersectionHomogeneousIdeal_toIdeal,
    tripleCompleteIntersectionHomogeneousIdeal_toIdeal]
  apply Ideal.span_le.mpr
  intro s hs
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  rcases hs with rfl | rfl | rfl
  · exact Ideal.subset_span (by simp)
  · exact Ideal.subset_span (by simp)
  · simpa using (Ideal.zero_mem _)

/- For the surface chart cut out by `p` and `q`, the Jacobian failure locus
   pulls back from every three-cubic quotient chart.  This is the precise
   ideal-membership form needed to apply the linear bad-submodule API at an
   actual point of the moving intersection. -/
theorem mem_tripleCompleteIntersectionChartJacobianBadSubmodule_comap_iff
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3)
    (hr : r.IsHomogeneous 3)
    (hz : (0 : MvPolynomial (Fin 4) K).IsHomogeneous 3)
    (hIJ : (tripleCompleteIntersectionHomogeneousIdeal p q 0 hp hq hz).toIdeal ≤
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr).toIdeal)
    (j : Fin 4)
    (Q : Ideal (ChartRing
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr) j)) :
    let I := tripleCompleteIntersectionHomogeneousIdeal p q 0 hp hq hz
    let J := tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr
    let φ := chartQuotientMap I J hIJ j
    let e : MvPolynomial (Fin 4) K →ₐ[K] ChartRing I j :=
      MvPolynomial.eval₂AlgHom K (chartCoordinate I j)
    ∀ v : homogeneousSubmodule (Fin 4) K 3,
      v ∈ tripleCompleteIntersectionChartJacobianBadSubmodule p q j e
          (Q.comap φ) ↔
        (tripleCompleteIntersectionChartJacobianPolynomial p q v.1 j).eval₂
            (chartBaseMap J j) (chartCoordinate J j) ∈ Q := by
  dsimp
  intro v
  rw [mem_tripleCompleteIntersectionChartJacobianBadSubmodule_iff,
    Ideal.mem_comap]
  change (chartQuotientMap
      (tripleCompleteIntersectionHomogeneousIdeal p q 0 hp hq hz)
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr) hIJ j)
      ((tripleCompleteIntersectionChartJacobianPolynomial p q v.1 j).eval₂
        (chartBaseMap (tripleCompleteIntersectionHomogeneousIdeal p q 0 hp hq hz) j)
        (chartCoordinate (tripleCompleteIntersectionHomogeneousIdeal p q 0 hp hq hz) j)) ∈ Q ↔ _
  rw [tripleCompleteIntersectionChartJacobianPolynomial_eval_chartQuotientMap]

/- A convenience form with the canonical surface-to-triple ideal inclusion.
   This is the form used by callers selecting a third cubic from the fixed
   `(p,q)` surface chart. -/
theorem mem_tripleCompleteIntersectionChartJacobianBadSubmodule_zero_comap_iff
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3)
    (hr : r.IsHomogeneous 3)
    (hz : (0 : MvPolynomial (Fin 4) K).IsHomogeneous 3)
    (j : Fin 4)
    (Q : Ideal (ChartRing
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr) j)) :
    let I := tripleCompleteIntersectionHomogeneousIdeal p q 0 hp hq hz
    let J := tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr
    let hIJ := tripleCompleteIntersectionHomogeneousIdeal_zero_le p q r hp hq hr hz
    let φ := chartQuotientMap I J hIJ j
    let e : MvPolynomial (Fin 4) K →ₐ[K] ChartRing I j :=
      MvPolynomial.eval₂AlgHom K (chartCoordinate I j)
    ∀ v : homogeneousSubmodule (Fin 4) K 3,
      v ∈ tripleCompleteIntersectionChartJacobianBadSubmodule p q j e
          (Q.comap φ) ↔
        (tripleCompleteIntersectionChartJacobianPolynomial p q v.1 j).eval₂
            (chartBaseMap J j) (chartCoordinate J j) ∈ Q := by
  dsimp
  apply mem_tripleCompleteIntersectionChartJacobianBadSubmodule_comap_iff

/- Properness can likewise be stated directly on the moving chart: the
   pullback bad submodule on the fixed surface chart is proper exactly when
   some degree-three cubic has nonzero Jacobian at the selected target point. -/
theorem tripleCompleteIntersectionChartJacobianBadSubmodule_zero_comap_ne_top_iff
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3)
    (hr : r.IsHomogeneous 3)
    (hz : (0 : MvPolynomial (Fin 4) K).IsHomogeneous 3)
    (j : Fin 4)
    (Q : Ideal (ChartRing
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr) j)) :
    let I := tripleCompleteIntersectionHomogeneousIdeal p q 0 hp hq hz
    let J := tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr
    let hIJ := tripleCompleteIntersectionHomogeneousIdeal_zero_le p q r hp hq hr hz
    let φ := chartQuotientMap I J hIJ j
    let e : MvPolynomial (Fin 4) K →ₐ[K] ChartRing I j :=
      MvPolynomial.eval₂AlgHom K (chartCoordinate I j)
    tripleCompleteIntersectionChartJacobianBadSubmodule p q j e
          (Q.comap φ) ≠ ⊤ ↔
      ∃ v : homogeneousSubmodule (Fin 4) K 3,
        (tripleCompleteIntersectionChartJacobianPolynomial p q v.1 j).eval₂
            (chartBaseMap J j) (chartCoordinate J j) ∉ Q := by
  dsimp only
  rw [tripleCompleteIntersectionChartJacobianBadSubmodule_ne_top_iff]
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨v, ?_⟩
    intro hmem
    apply hv
    rw [Ideal.mem_comap]
    change (chartQuotientMap
      (tripleCompleteIntersectionHomogeneousIdeal p q 0 hp hq hz)
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr) _ j)
      ((tripleCompleteIntersectionChartJacobianPolynomial p q v.1 j).eval₂
        (chartBaseMap (tripleCompleteIntersectionHomogeneousIdeal p q 0 hp hq hz) j)
        (chartCoordinate (tripleCompleteIntersectionHomogeneousIdeal p q 0 hp hq hz) j)) ∈ Q
    rw [tripleCompleteIntersectionChartJacobianPolynomial_eval_chartQuotientMap]
    exact hmem
  · rintro ⟨v, hv⟩
    refine ⟨v, ?_⟩
    intro hmem
    rw [Ideal.mem_comap] at hmem
    change (chartQuotientMap
      (tripleCompleteIntersectionHomogeneousIdeal p q 0 hp hq hz)
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr) _ j)
      ((tripleCompleteIntersectionChartJacobianPolynomial p q v.1 j).eval₂
        (chartBaseMap (tripleCompleteIntersectionHomogeneousIdeal p q 0 hp hq hz) j)
        (chartCoordinate (tripleCompleteIntersectionHomogeneousIdeal p q 0 hp hq hz) j)) ∈ Q at hmem
    rw [tripleCompleteIntersectionChartJacobianPolynomial_eval_chartQuotientMap] at hmem
    exact hv hmem

theorem tripleCompleteIntersectionChartJacobian_eq_signed_minor
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous a) (hq : q.IsHomogeneous b) (hr : r.IsHomogeneous c)
    (j : Fin 4) :
    tripleCompleteIntersectionChartJacobian p q r hp hq hr j =
      (-1 : ChartRing (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr) j) ^
          ((j : ℕ) + 3) *
        (((tripleCompleteIntersectionChartJacobiMatrix p q r j).submatrix
          j.succAbove (3 : Fin 4).succAbove).det).eval₂
          (chartBaseMap (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr) j)
          (chartCoordinate (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr) j) := by
  unfold tripleCompleteIntersectionChartJacobian
  rw [tripleCompleteIntersectionChartJacobianPolynomial_eq_signed_minor]
  rw [eval₂_mul, eval₂_pow]
  have hneg :
      eval₂ (chartBaseMap (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr) j)
          (chartCoordinate (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr) j)
          (-1 : MvPolynomial (Fin 4) K) =
        (-1 : ChartRing (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr) j) := by
    change (MvPolynomial.eval₂Hom
      (chartBaseMap (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr) j)
      (chartCoordinate (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr) j))
        (-1 : MvPolynomial (Fin 4) K) = _
    rw [map_neg, map_one]
  rw [hneg]

theorem tripleCompleteIntersectionChartJacobian_isUnit_iff_minor_eval_isUnit
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous a) (hq : q.IsHomogeneous b) (hr : r.IsHomogeneous c)
    (j : Fin 4) :
    IsUnit (tripleCompleteIntersectionChartJacobian p q r hp hq hr j) ↔
      IsUnit
        ((((tripleCompleteIntersectionChartJacobiMatrix p q r j).submatrix
          j.succAbove (3 : Fin 4).succAbove).det).eval₂
          (chartBaseMap (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr) j)
      (chartCoordinate (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr) j)) := by
  rw [tripleCompleteIntersectionChartJacobian_eq_signed_minor]
  have hneg : IsUnit
      (-1 : ChartRing (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr) j) :=
    IsUnit.neg (isUnit_one : IsUnit
      (1 : ChartRing (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr) j))
  have hpow : IsUnit
      ((-1 : ChartRing (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr) j) ^
        ((j : ℕ) + 3)) := hneg.pow _
  rw [IsUnit.mul_iff]
  exact and_iff_right hpow

/- The actual chart element, rather than only its polynomial numerator, also
   commutes with coefficient change. -/
theorem tripleCompleteIntersectionChartJacobian_map
    {K L : Type u} [Field K] [Field L]
    (f : K →+* L)
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous a) (hq : q.IsHomogeneous b) (hr : r.IsHomogeneous c)
    (j : Fin 4) :
    let I := tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr
    let J := tripleCompleteIntersectionHomogeneousIdeal (p.map f) (q.map f) (r.map f)
      (hp.map f) (hq.map f) (hr.map f)
    let h : I.toIdeal.map (MvPolynomial.map f) = J.toIdeal := by
      rw [tripleCompleteIntersectionHomogeneousIdeal_toIdeal,
        tripleCompleteIntersectionHomogeneousIdeal_toIdeal]
      exact tripleCompleteIntersectionIdeal_map f p q r
    let cm := chartCoefficientMap f I J h j
    cm (tripleCompleteIntersectionChartJacobian p q r hp hq hr j) =
      tripleCompleteIntersectionChartJacobian (p.map f) (q.map f) (r.map f)
        (hp.map f) (hq.map f) (hr.map f) j := by
  dsimp
  let I := tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr
  let J := tripleCompleteIntersectionHomogeneousIdeal (p.map f) (q.map f) (r.map f)
      (hp.map f) (hq.map f) (hr.map f)
  let h : I.toIdeal.map (MvPolynomial.map f) = J.toIdeal := by
    rw [tripleCompleteIntersectionHomogeneousIdeal_toIdeal,
      tripleCompleteIntersectionHomogeneousIdeal_toIdeal]
    exact tripleCompleteIntersectionIdeal_map f p q r
  let cm := chartCoefficientMap f I J h j
  unfold tripleCompleteIntersectionChartJacobian
  rw [← tripleCompleteIntersectionChartJacobianPolynomial_map f p q r hp hq hr j]
  exact chartCoefficientMap_eval f I J h j _

/- A Jacobian-unit certificate transports along any coefficient map.  This is
   the form consumed by the generic cubic residual after passing to its
   function field. -/
theorem tripleCompleteIntersectionChartJacobian_isUnit_map
    {K L : Type u} [Field K] [Field L]
    (f : K →+* L)
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous a) (hq : q.IsHomogeneous b) (hr : r.IsHomogeneous c)
    (j : Fin 4)
    (hunit : IsUnit (tripleCompleteIntersectionChartJacobian p q r hp hq hr j)) :
    IsUnit (tripleCompleteIntersectionChartJacobian (p.map f) (q.map f) (r.map f)
      (hp.map f) (hq.map f) (hr.map f) j) := by
  let I := tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr
  let J := tripleCompleteIntersectionHomogeneousIdeal (p.map f) (q.map f) (r.map f)
      (hp.map f) (hq.map f) (hr.map f)
  let h : I.toIdeal.map (MvPolynomial.map f) = J.toIdeal := by
    rw [tripleCompleteIntersectionHomogeneousIdeal_toIdeal,
      tripleCompleteIntersectionHomogeneousIdeal_toIdeal]
    exact tripleCompleteIntersectionIdeal_map f p q r
  let cm := chartCoefficientMap f I J h j
  rw [← tripleCompleteIntersectionChartJacobian_map f p q r hp hq hr j]
  exact hunit.map cm

/-- The explicit Jacobian determinant is the Jacobian attached to the square
pre-submersive presentation of the normalized chart. -/
theorem tripleCompleteIntersectionChartPrePresentation_jacobian
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous a) (hq : q.IsHomogeneous b) (hr : r.IsHomogeneous c)
    (j : Fin 4) :
    (tripleCompleteIntersectionChartPrePresentation p q r hp hq hr j).jacobian =
      tripleCompleteIntersectionChartJacobian p q r hp hq hr j := by
  classical
  let P₀ := Algebra.PreSubmersivePresentation.naive
    (v := tripleCompleteIntersectionChartRelations p q r j)
    (fun i => i) Function.injective_id
  have hP₀ : P₀.jacobian = Ideal.Quotient.mk _
      (tripleCompleteIntersectionChartJacobianPolynomial p q r j) := by
    rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
    change Ideal.Quotient.mk _ P₀.jacobiMatrix.det =
      Ideal.Quotient.mk _ (tripleCompleteIntersectionChartJacobiMatrix p q r j).det
    have hmatrix : P₀.jacobiMatrix = tripleCompleteIntersectionChartJacobiMatrix p q r j := by
      ext i l
      simp only [P₀, Algebra.PreSubmersivePresentation.jacobiMatrix_naive,
        tripleCompleteIntersectionChartJacobiMatrix]
    rw [hmatrix]
  change (P₀.ofAlgEquiv
    (tripleCompleteIntersectionChartRelationsEquiv p q r hp hq hr j)).jacobian = _
  calc
    _ = tripleCompleteIntersectionChartRelationsEquiv p q r hp hq hr j P₀.jacobian :=
      Algebra.PreSubmersivePresentation.jacobian_ofAlgEquiv P₀
        (tripleCompleteIntersectionChartRelationsEquiv p q r hp hq hr j)
    _ = tripleCompleteIntersectionChartRelationsEquiv p q r hp hq hr j
        (Ideal.Quotient.mk _ (tripleCompleteIntersectionChartJacobianPolynomial p q r j)) :=
      congrArg _ hP₀
    _ = _ := tripleCompleteIntersectionChartRelationsEquiv_mk p q r hp hq hr j _

/-- An invertible chart Jacobian makes the normalized chart étale. -/
theorem tripleCompleteIntersection_chart_etale_of_jacobian_isUnit
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous a) (hq : q.IsHomogeneous b) (hr : r.IsHomogeneous c)
    (j : Fin 4)
    (hjac : IsUnit (tripleCompleteIntersectionChartJacobian p q r hp hq hr j)) :
    Algebra.Etale K
      (ChartRing (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr) j) := by
  let P := tripleCompleteIntersectionChartPrePresentation p q r hp hq hr j
  let Q : Algebra.SubmersivePresentation K
      (ChartRing (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr) j)
      (Fin 4) (Fin 4) :=
    { P with
      jacobian_isUnit := by
        rw [tripleCompleteIntersectionChartPrePresentation_jacobian]
        exact hjac }
  letI : Algebra.IsStandardSmoothOfRelativeDimension 0 K
      (ChartRing (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr) j) :=
    Q.isStandardSmoothOfRelativeDimension
      (tripleCompleteIntersectionChartPrePresentation_dimension p q r hp hq hr j)
  infer_instance

/- The same Jacobian calculation is useful pointwise.  A chart Jacobian need
   only be a unit after localizing at the chosen prime; the corresponding
   local ring is then formally etale over the coefficient field.  This is the
   local transversality form consumed by maximal-point arguments. -/
theorem tripleCompleteIntersection_chart_isEtaleAt_of_jacobian_not_mem
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous a) (hq : q.IsHomogeneous b) (hr : r.IsHomogeneous c)
    (j : Fin 4) (Q : Ideal (ChartRing
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr) j))
    [Q.IsPrime]
    (hQ : tripleCompleteIntersectionChartJacobian p q r hp hq hr j ∉ Q) :
    Algebra.IsEtaleAt K Q := by
  let S := ChartRing (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr) j
  let P := tripleCompleteIntersectionChartPrePresentation p q r hp hq hr j
  have hdim : P.dimension = 0 :=
    tripleCompleteIntersectionChartPrePresentation_dimension p q r hp hq hr j
  have hbasic : (PrimeSpectrum.basicOpen P.jacobian : Set (PrimeSpectrum S)) ⊆
      Algebra.etaleLocus K S := by
    letI : Algebra.Etale K (Localization.Away P.jacobian) :=
      AllCharacteristics.etale_jacobianLocalization_of_dimension_zero P hdim
    exact Algebra.basicOpen_subset_etaleLocus_iff.mpr
      (by infer_instance)
  have hmem : (⟨Q, inferInstance⟩ : PrimeSpectrum S) ∈
      PrimeSpectrum.basicOpen P.jacobian := by
    change P.jacobian ∉ Q
    rw [tripleCompleteIntersectionChartPrePresentation_jacobian]
    exact hQ
  have hEtale : (⟨Q, inferInstance⟩ : PrimeSpectrum S) ∈
      Algebra.etaleLocus K S := hbasic hmem
  exact hEtale

/-- If the explicit square Jacobian is invertible on every normalized chart,
the projective three-equation intersection is étale over its coefficient
field. -/
theorem etale_tripleCompleteIntersection_toBase_of_chartJacobian_isUnit
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous a) (hq : q.IsHomogeneous b) (hr : r.IsHomogeneous c)
    (hjac : ∀ j : Fin 4,
      IsUnit (tripleCompleteIntersectionChartJacobian p q r hp hq hr j)) :
    Etale (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) := by
  letI : IsZariskiLocalAtSource (@Etale.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Etale)
  apply (IsZariskiLocalAtSource.iff_of_openCover (P := @Etale.{u})
    (coordinateOpenCover (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)).openCover).mpr
  intro j
  change Fin 4 at j
  change Etale (chartι (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr) j ≫
    toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))
  rw [chartι_toBase]
  exact (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
    (tripleCompleteIntersection_chart_etale_of_jacobian_isUnit p q r hp hq hr j (hjac j))

/-- Checking that the chart Jacobian does not vanish at any closed point
is enough to make the projective three-equation intersection étale. -/
theorem etale_tripleCompleteIntersection_toBase_of_chartJacobian_not_mem_maximal
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous a) (hq : q.IsHomogeneous b) (hr : r.IsHomogeneous c)
    (hjac : ∀ j : Fin 4,
      ∀ Q : Ideal (ChartRing
        (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr) j),
      [Q.IsMaximal] →
        tripleCompleteIntersectionChartJacobian p q r hp hq hr j ∉ Q) :
    Etale (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) := by
  apply etale_tripleCompleteIntersection_toBase_of_chartJacobian_isUnit
    p q r hp hq hr
  intro j
  let d := tripleCompleteIntersectionChartJacobian p q r hp hq hr j
  by_contra hd
  have hproper : Ideal.span ({d} : Set (ChartRing
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr) j)) ≠ ⊤ := by
    intro ht
    exact hd (Ideal.span_singleton_eq_top.mp ht)
  obtain ⟨Q, hQ, hle⟩ := Ideal.exists_le_maximal _ hproper
  letI : Q.IsMaximal := hQ
  have hdQ : d ∈ Q := hle (Ideal.subset_span (Set.mem_singleton d))
  exact (hjac j Q) hdQ

end

end PfaffianDescent
