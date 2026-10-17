import PfaffianDescent.CorayAiProjectiveHyperplaneSupport
import PfaffianDescent.CorayNativeLocalizedProjectiveHyperplanePullback
import Mathlib.AlgebraicGeometry.Limits

noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial HomogeneousLocalization
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

/-- Literal linear-equation membership for every native chart prime,
without requiring a residue-field presentation or closed source point. -/
theorem basisProjectiveHyperplaneSupport_chartPrime_mem_iff001
    {K : Type u} [CommRing K] {σ : Type} [Fintype σ]
    (a : σ)
    (q : Spec (.of (ChartRing (⊥ : HomogeneousIdeal (homogeneousSubmodule σ K)) a)))
    (c : σ → K) :
    chartι (⊥ : HomogeneousIdeal (homogeneousSubmodule σ K)) a q ∈
      basisProjectiveHyperplaneSupport c ↔ projectiveChartLinearForm a c ∈ q.asIdeal := by
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
    (grading I) (coordinate I a) (coordinate_mem I a) q 1
    (Ideal.Quotient.mk I.toIdeal l) (polynomial_class_mem_grading I l hl)
  rw [hForm] at hmem
  change ({Ideal.Quotient.mk I.toIdeal l} : Set (CoordinateRing I)) ⊆
      (chartι I a q).asHomogeneousIdeal ↔ projectiveChartLinearForm a c ∈ q.asIdeal
  rw [Set.singleton_subset_iff]
  exact hmem

/-- Every point of the WHOLE affine hyperplane quotient lies in the literal
original projective hyperplane support. No reduced-support replacement. -/
theorem basisProjectiveHyperplaneSupport_quotientChartPoint_mem001
    {K : Type u} [CommRing K] {σ : Type} [Fintype σ]
    (a : σ) (c : σ → K)
    (q : Spec (.of ((ChartRing (⊥ : HomogeneousIdeal (homogeneousSubmodule σ K)) a) ⧸
      Ideal.span ({projectiveChartLinearForm a c} : Set
        (ChartRing (⊥ : HomogeneousIdeal (homogeneousSubmodule σ K)) a))))) :
    chartι (⊥ : HomogeneousIdeal (homogeneousSubmodule σ K)) a
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        (Ideal.span ({projectiveChartLinearForm a c} : Set
          (ChartRing (⊥ : HomogeneousIdeal (homogeneousSubmodule σ K)) a))))) q) ∈
        basisProjectiveHyperplaneSupport c := by
  let A := ChartRing (⊥ : HomogeneousIdeal (homogeneousSubmodule σ K)) a
  let H := Ideal.span ({projectiveChartLinearForm a c} : Set A)
  apply (basisProjectiveHyperplaneSupport_chartPrime_mem_iff001 a _ c).mpr
  change Ideal.Quotient.mk H (projectiveChartLinearForm a c) ∈ q.asIdeal
  have hZero : Ideal.Quotient.mk H (projectiveChartLinearForm a c) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  rw [hZero]
  exact Ideal.zero_mem _

/-- ALL native hyperplane pullback points satisfy the actual original
projective equation. The pullback is the full quotient, preserving the
scheme used by the pending SAME whole p/q-curve restriction isomorphism. -/
theorem nativeLocalizedProjectiveHyperplanePullback_images_mem_support001
    {K R : Type u} [CommRing K] [CommRing R] {σ : Type} [Fintype σ]
    (f : K →+* R) (x : σ → R) (a : σ) (c : σ → K) :
    let A := ChartRing (⊥ : HomogeneousIdeal (homogeneousSubmodule σ K)) a
    let H := Ideal.span ({projectiveChartLinearForm a c} : Set A)
    let v := Spec.map (CommRingCat.ofHom (nativeLocalizedProjectiveChartMap f x a))
    let h := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk H))
    ∀ z : (pullback v h : Scheme),
      nativeLocalizedProjectiveChartPoint f x a (pullback.fst v h z) ∈
        basisProjectiveHyperplaneSupport c := by
  let A := ChartRing (⊥ : HomogeneousIdeal (homogeneousSubmodule σ K)) a
  let H := Ideal.span ({projectiveChartLinearForm a c} : Set A)
  let v := Spec.map (CommRingCat.ofHom (nativeLocalizedProjectiveChartMap f x a))
  let h := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk H))
  change ∀ z : (pullback v h : Scheme),
    nativeLocalizedProjectiveChartPoint f x a (pullback.fst v h z) ∈
      basisProjectiveHyperplaneSupport c
  intro z
  have hComm := congrArg (fun k : pullback v h ⟶ Spec (.of A) => k z)
    (pullback.condition (f := v) (g := h))
  change v (pullback.fst v h z) = h (pullback.snd v h z) at hComm
  change chartι (⊥ : HomogeneousIdeal (homogeneousSubmodule σ K)) a
    (v (pullback.fst v h z)) ∈ basisProjectiveHyperplaneSupport c
  rw [hComm]
  exact basisProjectiveHyperplaneSupport_quotientChartPoint_mem001 a c (pullback.snd v h z)

end PfaffianDescent.Coray
