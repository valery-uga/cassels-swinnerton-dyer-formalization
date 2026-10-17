import PfaffianDescent.CorayProjectiveEvaluationLinearForm
import PfaffianDescent.HomogeneousChartPrime
import AllCharacteristics.NormalizedChartGeneration

noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

/-- The actual closed support of the original-coefficient linear equation. -/
def basisProjectiveHyperplaneSupport {K : Type u} [CommRing K]
    {σ : Type} [Fintype σ] (c : σ → K) :
    Set (scheme (⊥ : HomogeneousIdeal (homogeneousSubmodule σ K))) :=
  ProjectiveSpectrum.zeroLocus (grading (⊥ : HomogeneousIdeal (homogeneousSubmodule σ K)))
    ({Ideal.Quotient.mk (⊥ : Ideal (MvPolynomial σ K))
      (∑ i, C (c i) * X i)} : Set (CoordinateRing (⊥ : HomogeneousIdeal (homogeneousSubmodule σ K))))

theorem basisProjectiveHyperplaneSupport_isClosed001 {K : Type u} [CommRing K]
    {σ : Type} [Fintype σ] (c : σ → K) :
    IsClosed (basisProjectiveHyperplaneSupport c) :=
  ProjectiveSpectrum.isClosed_zeroLocus _ _

/-- The literal homogeneous linear equation at an actual field chart point
is zero precisely when the existing normalized chart linear form is zero. -/
theorem basisProjectiveHyperplaneSupport_chartPoint_mem_iff001
    {K F : Type u} [CommRing K] [Field F] {σ : Type} [Fintype σ]
    (a : σ)
    (g : ChartRing (⊥ : HomogeneousIdeal (homogeneousSubmodule σ K)) a →+* F)
    (c : σ → K) :
    (chartι (⊥ : HomogeneousIdeal (homogeneousSubmodule σ K)) a
      (Spec.map (CommRingCat.ofHom g) (IsLocalRing.closedPoint F))) ∈
        basisProjectiveHyperplaneSupport c ↔ g (projectiveChartLinearForm a c) = 0 := by
  classical
  let I : HomogeneousIdeal (homogeneousSubmodule σ K) := ⊥
  let l : MvPolynomial σ K := ∑ i, C (c i) * X i
  have hl : l.IsHomogeneous 1 :=
    IsHomogeneous.sum _ _ _ (fun i _ => isHomogeneous_C_mul_X (c i) i)
  have hForm : Away.mk (grading I) (coordinate_mem I a) 1
      (Ideal.Quotient.mk I.toIdeal l) (by simpa using polynomial_class_mem_grading I l hl) =
        projectiveChartLinearForm a c := by
    rw [← eval₂_chartCoordinate_eq_fraction I a l hl]
    simp only [l, I, projectiveChartLinearForm, eval₂_sum, eval₂_mul, eval₂_C, eval₂_X]
  have hmem := PfaffianDescent.homogeneousChart_prime_membership
    (grading I) (coordinate I a) (coordinate_mem I a)
    (Spec.map (CommRingCat.ofHom g) (IsLocalRing.closedPoint F)) 1
    (Ideal.Quotient.mk I.toIdeal l) (polynomial_class_mem_grading I l hl)
  rw [hForm] at hmem
  change Ideal.Quotient.mk I.toIdeal l ∈
      (chartι I a (Spec.map (CommRingCat.ofHom g) (IsLocalRing.closedPoint F))).asHomogeneousIdeal ↔
        g (projectiveChartLinearForm a c) ∈ IsLocalRing.maximalIdeal F at hmem
  change ({Ideal.Quotient.mk I.toIdeal l} : Set (CoordinateRing I)) ⊆
      (chartι I a (Spec.map (CommRingCat.ofHom g) (IsLocalRing.closedPoint F))).asHomogeneousIdeal ↔
        g (projectiveChartLinearForm a c) = 0
  rw [Set.singleton_subset_iff]
  constructor
  · intro h
    have hZero := hmem.mp h
    rw [IsLocalRing.maximalIdeal_eq_bot] at hZero
    exact Ideal.mem_bot.mp hZero
  · intro hZero
    apply hmem.mpr
    rw [hZero]
    exact Ideal.zero_mem _

end PfaffianDescent.Coray
