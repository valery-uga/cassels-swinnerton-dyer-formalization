import PfaffianDescent.VoisinQuadraticJacobianSelector

/-!
# The singular scheme of a cubic--quadric--quadric intersection

The original universal singular-family API was specialized to three cubics.
Voisin's final degree-eight residual uses one cubic and two quadrics.  This
file supplies the mixed-degree projective Jacobian package: its four maximal
minors have degree four, their simultaneous zero scheme detects every bad
affine chart, and emptiness of that scheme implies that the complete
intersection is étale.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics HomogeneousProjective

universe u

variable {K : Type u} [Field K]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- For a cubic and two quadrics, every projective maximal Jacobian minor is
homogeneous of degree four. -/
theorem cubicTwoQuadricChartJacobianPolynomial_isHomogeneous
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hr : r.IsHomogeneous 2) (j : Fin 4) :
    (tripleCompleteIntersectionChartJacobianPolynomial p q r j).IsHomogeneous 4 := by
  let M := tripleCompleteIntersectionChartJacobianMinorMatrix p q r j
  have h0 (i : Fin 3) : (M i 0).IsHomogeneous 2 := by
    simpa [M, tripleCompleteIntersectionChartJacobianMinorMatrix] using hp.pderiv
  have h1 (i : Fin 3) : (M i 1).IsHomogeneous 1 := by
    simpa [M, tripleCompleteIntersectionChartJacobianMinorMatrix] using hq.pderiv
  have h2 (i : Fin 3) : (M i 2).IsHomogeneous 1 := by
    simpa [M, tripleCompleteIntersectionChartJacobianMinorMatrix] using hr.pderiv
  have h000 : (M 0 0 * M 1 1 * M 2 2).IsHomogeneous 4 := by
    simpa using (h0 0 |>.mul (h1 1) |>.mul (h2 2))
  have h001 : (M 0 0 * M 1 2 * M 2 1).IsHomogeneous 4 := by
    simpa [Nat.add_comm] using (h0 0 |>.mul (h2 1) |>.mul (h1 2))
  have h010 : (M 0 1 * M 1 0 * M 2 2).IsHomogeneous 4 := by
    simpa [Nat.add_comm, Nat.add_left_comm] using
      (h1 0 |>.mul (h0 1) |>.mul (h2 2))
  have h011 : (M 0 1 * M 1 2 * M 2 0).IsHomogeneous 4 := by
    simpa [Nat.add_comm, Nat.add_left_comm] using
      (h1 0 |>.mul (h2 1) |>.mul (h0 2))
  have h100 : (M 0 2 * M 1 0 * M 2 1).IsHomogeneous 4 := by
    simpa [Nat.add_comm, Nat.add_left_comm] using
      (h2 0 |>.mul (h0 1) |>.mul (h1 2))
  have h101 : (M 0 2 * M 1 1 * M 2 0).IsHomogeneous 4 := by
    simpa [Nat.add_comm, Nat.add_left_comm] using
      (h2 0 |>.mul (h1 1) |>.mul (h0 2))
  have hdet : M.det.IsHomogeneous 4 := by
    rw [Matrix.det_fin_three]
    exact (((((h000.sub h001).sub h010).add h011).add h100).sub h101)
  rw [tripleCompleteIntersectionChartJacobianPolynomial_eq_signed_minorMatrix]
  have hsign : ((-1 : MvPolynomial (Fin 4) K) ^ ((j : ℕ) + 3)).IsHomogeneous 0 := by
    simpa only [map_neg, map_one, Nat.zero_mul] using
      (MvPolynomial.isHomogeneous_C (Fin 4) (-1 : K)).pow ((j : ℕ) + 3)
  simpa only [zero_add] using hsign.mul hdet

/-- Euler's identity puts the projective coordinate vector in the kernel of
the full derivative matrix at a common zero of a cubic and two quadrics. -/
theorem cubicTwoQuadricFullJacobianEvaluationMatrix_mulVec_eq_zero
    (p q r : MvPolynomial (Fin 4) K) (x : Fin 4 → K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hr : r.IsHomogeneous 2)
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

/-- At a common projective zero, vanishing of the normalized Jacobian in one
chart containing the point forces all four projective maximal minors to
vanish. -/
theorem all_cubicTwoQuadricChartJacobianPolynomial_eval_eq_zero_of_one
    (p q r : MvPolynomial (Fin 4) K) (x : Fin 4 → K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hr : r.IsHomogeneous 2)
    (hpx : p.eval x = 0) (hqx : q.eval x = 0) (hrx : r.eval x = 0)
    (j : Fin 4) (hxj : x j ≠ 0)
    (hj : (tripleCompleteIntersectionChartJacobianPolynomial p q r j).eval x = 0) :
    ∀ k : Fin 4,
      (tripleCompleteIntersectionChartJacobianPolynomial p q r k).eval x = 0 := by
  let A := tripleCompleteIntersectionFullJacobianEvaluationMatrix p q r x
  have hAx : A.mulVec x = 0 :=
    cubicTwoQuadricFullJacobianEvaluationMatrix_mulVec_eq_zero
      p q r x hp hq hr hpx hqx hrx
  have hminorj : (A.submatrix id j.succAbove).det = 0 :=
    (tripleCompleteIntersectionChartJacobianPolynomial_eval_eq_zero_iff_fullMinor
      p q r x j).mp hj
  have hall := all_maximalMinors_zero_of_mulVec_eq_zero A x j hxj hAx hminorj
  intro k
  exact (tripleCompleteIntersectionChartJacobianPolynomial_eval_eq_zero_iff_fullMinor
    p q r x k).mpr (hall k)

/-- The equations cutting out the projective singular locus of a
cubic--quadric--quadric intersection. -/
noncomputable def cubicTwoQuadricSingularEquationSet
    (p q r : MvPolynomial (Fin 4) K) : Set (MvPolynomial (Fin 4) K) :=
  {p, q, r} ∪ Set.range (fun j : Fin 4 =>
    tripleCompleteIntersectionChartJacobianPolynomial p q r j)

noncomputable def cubicTwoQuadricSingularIdeal
    (p q r : MvPolynomial (Fin 4) K) : Ideal (MvPolynomial (Fin 4) K) :=
  Ideal.span (cubicTwoQuadricSingularEquationSet p q r)

theorem cubicTwoQuadricSingularEquationSet_homogeneous
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hr : r.IsHomogeneous 2) :
    ∀ s ∈ cubicTwoQuadricSingularEquationSet p q r,
      ∃ d, s.IsHomogeneous d := by
  intro s hs
  rcases hs with hs | hs
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl
    · exact ⟨3, hp⟩
    · exact ⟨2, hq⟩
    · exact ⟨2, hr⟩
  · obtain ⟨j, rfl⟩ := hs
    exact ⟨4, cubicTwoQuadricChartJacobianPolynomial_isHomogeneous
      p q r hp hq hr j⟩

/-- The homogeneous ideal of the mixed-degree singular scheme. -/
noncomputable def cubicTwoQuadricSingularHomogeneousIdeal
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hr : r.IsHomogeneous 2) :
    HomogeneousIdeal (homogeneousSubmodule (Fin 4) K) :=
  ⟨cubicTwoQuadricSingularIdeal p q r,
    Ideal.homogeneous_span _ _
      (cubicTwoQuadricSingularEquationSet_homogeneous p q r hp hq hr)⟩

@[simp] theorem cubicTwoQuadricSingularHomogeneousIdeal_toIdeal
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hr : r.IsHomogeneous 2) :
    (cubicTwoQuadricSingularHomogeneousIdeal p q r hp hq hr).toIdeal =
      cubicTwoQuadricSingularIdeal p q r := rfl

/-- If the mixed-degree projective singular scheme is empty, every normalized
chart Jacobian is invertible. -/
theorem cubicTwoQuadricChartJacobian_isUnit_of_isEmpty_singularScheme
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hr : r.IsHomogeneous 2)
    (hempty : IsEmpty (scheme
      (cubicTwoQuadricSingularHomogeneousIdeal p q r hp hq hr))) :
    ∀ j : Fin 4,
      IsUnit (tripleCompleteIntersectionChartJacobian p q r hp hq hr j) := by
  intro j
  by_contra hunit
  let J := tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr
  let A := ChartRing J j
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal
    (Ideal.span ({tripleCompleteIntersectionChartJacobian
      p q r hp hq hr j} : Set A))
    (Ideal.span_singleton_ne_top hunit)
  let Q : MaximalSpectrum A := ⟨M, hM⟩
  letI : Algebra K A := (chartBaseMap J j).toAlgebra
  let e : MvPolynomial (Fin 4) K →ₐ[K] A :=
    MvPolynomial.eval₂AlgHom K (chartCoordinate J j)
  let L := Q.asIdeal.ResidueField
  let x : Fin 4 → L := tripleCompleteIntersectionResidueEvaluation e Q
  have hxj : x j ≠ 0 := by
    simpa only [x, e] using
      tripleCompleteIntersectionResidueEvaluation_chartCoordinate_ne_zero J j Q
  have hpJ : p ∈ J.toIdeal := by
    dsimp [J]
    rw [tripleCompleteIntersectionHomogeneousIdeal_toIdeal]
    exact Ideal.subset_span (by simp)
  have hqJ : q ∈ J.toIdeal := by
    dsimp [J]
    rw [tripleCompleteIntersectionHomogeneousIdeal_toIdeal]
    exact Ideal.subset_span (by simp)
  have hrJ : r ∈ J.toIdeal := by
    dsimp [J]
    rw [tripleCompleteIntersectionHomogeneousIdeal_toIdeal]
    exact Ideal.subset_span (by simp)
  have hep : e p = 0 := by
    change p.eval₂ (chartBaseMap J j) (chartCoordinate J j) = 0
    exact eval₂_chartCoordinate_eq_zero_of_mem J j p hpJ
  have heq : e q = 0 := by
    change q.eval₂ (chartBaseMap J j) (chartCoordinate J j) = 0
    exact eval₂_chartCoordinate_eq_zero_of_mem J j q hqJ
  have her : e r = 0 := by
    change r.eval₂ (chartBaseMap J j) (chartCoordinate J j) = 0
    exact eval₂_chartCoordinate_eq_zero_of_mem J j r hrJ
  have hpx : (p.map (algebraMap K L)).eval x = 0 := by
    change (MvPolynomial.eval₂Hom (RingHom.id Q.asIdeal.ResidueField) x)
      (p.map (algebraMap K Q.asIdeal.ResidueField)) = 0
    rw [← tripleCompleteIntersectionResidueEvaluation_map_eval e Q p,
      hep, map_zero]
  have hqx : (q.map (algebraMap K L)).eval x = 0 := by
    change (MvPolynomial.eval₂Hom (RingHom.id Q.asIdeal.ResidueField) x)
      (q.map (algebraMap K Q.asIdeal.ResidueField)) = 0
    rw [← tripleCompleteIntersectionResidueEvaluation_map_eval e Q q,
      heq, map_zero]
  have hrx : (r.map (algebraMap K L)).eval x = 0 := by
    change (MvPolynomial.eval₂Hom (RingHom.id Q.asIdeal.ResidueField) x)
      (r.map (algebraMap K Q.asIdeal.ResidueField)) = 0
    rw [← tripleCompleteIntersectionResidueEvaluation_map_eval e Q r,
      her, map_zero]
  have hjacM : tripleCompleteIntersectionChartJacobian
      p q r hp hq hr j ∈ M :=
    hle (Ideal.subset_span (Set.mem_singleton _))
  have hjacZero : algebraMap A L
      (tripleCompleteIntersectionChartJacobian p q r hp hq hr j) = 0 :=
    Ideal.algebraMap_residueField_eq_zero.mpr hjacM
  have hjMapped :
      ((tripleCompleteIntersectionChartJacobianPolynomial p q r j).map
        (algebraMap K L)).eval x = 0 := by
    calc
      _ = algebraMap A L
          (e (tripleCompleteIntersectionChartJacobianPolynomial p q r j)) :=
        (tripleCompleteIntersectionResidueEvaluation_map_eval e Q
          (tripleCompleteIntersectionChartJacobianPolynomial p q r j)).symm
      _ = algebraMap A L
          (tripleCompleteIntersectionChartJacobian p q r hp hq hr j) := by
        rfl
      _ = 0 := hjacZero
  have hj :
      (tripleCompleteIntersectionChartJacobianPolynomial
        (p.map (algebraMap K L)) (q.map (algebraMap K L))
        (r.map (algebraMap K L)) j).eval x = 0 := by
    rw [← tripleCompleteIntersectionChartJacobianPolynomial_map
      (algebraMap K L) p q r hp hq hr j]
    exact hjMapped
  have hall :=
    all_cubicTwoQuadricChartJacobianPolynomial_eval_eq_zero_of_one
      (p.map (algebraMap K L)) (q.map (algebraMap K L))
      (r.map (algebraMap K L)) x
      (hp.map (algebraMap K L)) (hq.map (algebraMap K L))
      (hr.map (algebraMap K L)) hpx hqx hrx j hxj hj
  let I := cubicTwoQuadricSingularHomogeneousIdeal p q r hp hq hr
  have heval : ∀ s : MvPolynomial (Fin 4) K,
      s ∈ I.toIdeal → s.eval₂ (algebraMap K L) x = 0 := by
    intro s hs
    have hker : I.toIdeal ≤
        RingHom.ker (MvPolynomial.eval₂Hom (algebraMap K L) x) := by
      dsimp [I]
      rw [cubicTwoQuadricSingularIdeal]
      apply Ideal.span_le.mpr
      intro a ha
      rcases ha with ha | ha
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
        rcases ha with rfl | rfl | rfl
        · simpa [MvPolynomial.eval₂_map] using hpx
        · simpa [MvPolynomial.eval₂_map] using hqx
        · simpa [MvPolynomial.eval₂_map] using hrx
      · obtain ⟨k, rfl⟩ := ha
        change MvPolynomial.eval₂ (algebraMap K L) x
          (tripleCompleteIntersectionChartJacobianPolynomial p q r k) = 0
        rw [MvPolynomial.eval₂_eq_eval_map,
          tripleCompleteIntersectionChartJacobianPolynomial_map
            (algebraMap K L) p q r hp hq hr k]
        exact hall k
    exact hker hs
  have hx : x ≠ 0 := by
    intro hzero
    exact hxj (congrFun hzero j)
  obtain ⟨t, _⟩ := point_of_coordinates I (algebraMap K L) x hx heval
  exact hempty.false (t (IsLocalRing.closedPoint L))

/-- Empty mixed-degree singular scheme gives exactly the étaleness condition
needed for Voisin's cubic--quadric--quadric residual. -/
theorem etale_cubicTwoQuadric_toBase_of_isEmpty_singularScheme
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hr : r.IsHomogeneous 2)
    (hempty : IsEmpty (scheme
      (cubicTwoQuadricSingularHomogeneousIdeal p q r hp hq hr))) :
    Etale (toBase
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) :=
  etale_tripleCompleteIntersection_toBase_of_chartJacobian_isUnit
    p q r hp hq hr
      (cubicTwoQuadricChartJacobian_isUnit_of_isEmpty_singularScheme
        p q r hp hq hr hempty)

end PfaffianDescent
