import AllCharacteristics.CubicPolynomialCoordinates
import AllCharacteristics.CubicMultiplicity
import AllCharacteristics.HomogeneousSpecialization
import PfaffianDescent.HyperplaneParametrization
import PfaffianDescent.TopHomogeneousProduct
import PfaffianDescent.CorayPlaneHomogeneousCommonZero

/-! A line in a singular plane cubic that avoids the
singular point forces another contained line through that point. The proof
constructs a second double point by intersecting the line and residual conic,
then uses the explicit binary cubic restriction. -/

noncomputable section
namespace PfaffianDescent
open MvPolynomial

theorem mem_span_homogeneousLinearForm_of_hyperplane_restriction_eq_zero_any_dimension
    {K : Type*} [Field K] {n : ℕ}
    (c : Fin (n + 1) → K) (k : Fin (n + 1)) (hk : c k ≠ 0)
    (q : MvPolynomial (Fin (n + 1)) K)
    (hq : rectangularSubstitution (hyperplaneInclusion c k) q = 0) :
    q ∈ Ideal.span ({homogeneousLinearForm c} : Set (MvPolynomial (Fin (n + 1)) K)) := by
  let M := hyperplaneInclusion c k
  let N := coordinateOmission (K := K) k
  let J := Ideal.span ({homogeneousLinearForm c} : Set (MvPolynomial (Fin (n + 1)) K))
  let e : MvPolynomial (Fin (n + 1)) K →ₐ[K] MvPolynomial (Fin (n + 1)) K ⧸ J :=
    Ideal.Quotient.mkₐ K J
  let t := e.comp (rectangularSubstitution N)
  have ht : t.comp (rectangularSubstitution M) = e := by
    apply MvPolynomial.algHom_ext
    intro i
    change e (rectangularSubstitution N (rectangularSubstitution M (X i))) = e (X i)
    have hrel : e (linearSectionRelation M N i) = 0 := by
      change Ideal.Quotient.mk J (linearSectionRelation M N i) = 0
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      by_cases hi : i = k
      · subst i
        rw [show M = hyperplaneInclusion c k by rfl,
          show N = coordinateOmission k by rfl,
          hyperplaneInclusion_pivot_relation c k hk]
        exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_singleton _))
      · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hi
        rw [show M = hyperplaneInclusion c k by rfl,
          show N = coordinateOmission k by rfl,
          hyperplaneInclusion_other_relation]
        exact Ideal.zero_mem _
    change e (X i - rectangularSubstitution N (rectangularLinearCoordinate M i)) = 0 at hrel
    rw [_root_.map_sub, sub_eq_zero] at hrel
    rw [rectangularSubstitution_X]
    exact hrel.symm
  have heq := AlgHom.congr_fun ht q
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change e q = 0
  change t (rectangularSubstitution M q) = e q at heq
  rw [show rectangularSubstitution M q = 0 from hq] at heq
  simpa [t] using heq.symm

/-- A line factor avoiding a singular point of a plane cubic yields an
actual contained line through that point. The second double point is the
constructed intersection of the line factor with its residual conic. -/
theorem exists_contained_line_through_singular_of_linear_factor
    {K : Type*} [Field K] [IsAlgClosed K]
    (F ℓ : MvPolynomial (Fin 3) K)
    (hF : F.IsHomogeneous 3) (hF0 : F ≠ 0) (hℓ : ℓ.IsHomogeneous 1)
    (p : Fin 3 → K) (hp : MvPolynomial.eval p F = 0)
    (hgradient : ∀ i : Fin 3, MvPolynomial.eval p (pderiv i F) = 0)
    (hℓp : MvPolynomial.eval p ℓ ≠ 0) (hdiv : ℓ ∣ F) :
    ∃ d : Fin 3 → K, LinearIndependent K ![p, d] ∧
      ∀ s t : K, MvPolynomial.eval (s • p + t • d) F = 0 := by
  classical
  obtain ⟨Q, hfactor⟩ := hdiv
  have hℓ0 : ℓ ≠ 0 := by
    intro hzero
    exact hℓp (by rw [hzero, _root_.map_zero])
  have hQ0 : Q ≠ 0 := by
    intro hzero
    apply hF0
    rw [hfactor, hzero, mul_zero]
  have hQhom : Q.IsHomogeneous 2 := by
    have hprod : (ℓ * Q).IsHomogeneous 3 := hfactor ▸ hF
    have hhom := (homogeneous_factor_of_homogeneous_product hℓ0 hQ0 hprod).2
    have hdegF : F.totalDegree = 3 := hF.totalDegree hF0
    have hdegℓ : ℓ.totalDegree = 1 := hℓ.totalDegree hℓ0
    have hdeg : Q.totalDegree = 2 := by
      have heq : F.totalDegree = ℓ.totalDegree + Q.totalDegree := by
        rw [hfactor, totalDegree_mul_of_isDomain hℓ0 hQ0]
      omega
    simpa only [hdeg] using hhom
  obtain ⟨d, hd0, hQd, hℓd⟩ :=
    Coray.plane_exists_nonzero_common_zero_of_homogeneous_pos Q ℓ hQhom hℓ
      (by norm_num) (by norm_num)
  have hQd' : MvPolynomial.eval d Q = 0 := by
    simpa only [aeval_def, Algebra.algebraMap_self, MvPolynomial.eval₂_id] using hQd
  have hℓd' : MvPolynomial.eval d ℓ = 0 := by
    simpa only [aeval_def, Algebra.algebraMap_self, MvPolynomial.eval₂_id] using hℓd
  have hdF : MvPolynomial.eval d F = 0 := by
    rw [hfactor, _root_.map_mul, hQd', mul_zero]
  have hdgrad : ∀ i : Fin 3, MvPolynomial.eval d (pderiv i F) = 0 := by
    intro i
    rw [hfactor, pderiv_mul, _root_.map_add, _root_.map_mul, _root_.map_mul,
      hQd', hℓd']
    ring
  have hind : LinearIndependent K ![p, d] := by
    rw [linearIndependent_fin2]
    refine ⟨hd0, ?_⟩
    intro a ha
    change a • d = p at ha
    apply hℓp
    rw [← ha]
    change MvPolynomial.eval₂ (RingHom.id K) (a • d) ℓ = 0
    rw [AllCharacteristics.eval₂_homogeneous_smul ℓ hℓ,
      MvPolynomial.eval₂_id, hℓd', mul_zero]
  obtain ⟨c, hc⟩ := AllCharacteristics.homogeneous_cubic_has_tensor_any_characteristic F hF
  have heval (x : Fin 3 → K) : MvPolynomial.eval x F = c.eval x := by
    rw [← hc]
    simpa only [MvPolynomial.eval₂_id,
      show c.map (RingHom.id K) = c by funext i; rfl] using
        Cubic.eval_toMvPolynomial (RingHom.id K) c x
  have hcp : c.eval p = 0 := by
    exact (heval p).symm.trans hp
  have hcd : c.eval d = 0 := by
    exact (heval d).symm.trans hdF
  have hmp : c.mixed p d = 0 := by
    rw [AllCharacteristics.Cubic.mixed_eq_sum_pderiv_eval, hc]
    simp only [hgradient, mul_zero, Finset.sum_const_zero]
  have hmd : c.mixed d p = 0 := by
    rw [AllCharacteristics.Cubic.mixed_eq_sum_pderiv_eval, hc]
    simp only [hdgrad, mul_zero, Finset.sum_const_zero]
  refine ⟨d, hind, ?_⟩
  intro s t
  rw [heval, Cubic.eval_line, hcp, hcd, hmp, hmd]
  ring

/-- A plane cubic having no contained line through its singular point has
nonzero restriction to every line avoiding that point. -/
theorem plane_cubic_line_restriction_ne_zero_of_no_contained_line_through
    {K : Type*} [Field K] [IsAlgClosed K]
    (F : MvPolynomial (Fin 3) K) (hF : F.IsHomogeneous 3) (hF0 : F ≠ 0)
    (p : Fin 3 → K) (hp : MvPolynomial.eval p F = 0)
    (hgradient : ∀ i : Fin 3, MvPolynomial.eval p (pderiv i F) = 0)
    (hnoLine : ∀ d : Fin 3 → K, LinearIndependent K ![p, d] →
      ∃ s t : K, MvPolynomial.eval (s • p + t • d) F ≠ 0)
    (a : Fin 3 → K) (k : Fin 3) (hk : a k ≠ 0)
    (hap : MvPolynomial.eval p (homogeneousLinearForm a) ≠ 0) :
    rectangularSubstitution (hyperplaneInclusion a k) F ≠ 0 := by
  intro hzero
  have hdiv : homogeneousLinearForm a ∣ F := Ideal.mem_span_singleton.mp
    (mem_span_homogeneousLinearForm_of_hyperplane_restriction_eq_zero_any_dimension
      a k hk F hzero)
  have hhom : (homogeneousLinearForm a).IsHomogeneous 1 := by
    apply IsHomogeneous.sum
    intro i _
    exact isHomogeneous_C_mul_X _ _
  obtain ⟨d, hind, hline⟩ :=
    exists_contained_line_through_singular_of_linear_factor F (homogeneousLinearForm a)
      hF hF0 hhom p hp hgradient hap hdiv
  obtain ⟨s, t, hst⟩ := hnoLine d hind
  exact hst (hline s t)

end PfaffianDescent
