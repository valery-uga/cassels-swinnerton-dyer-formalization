import PfaffianDescent.VoisinQuadraticSingularFiberEtale
import PfaffianDescent.VoisinProjectiveLinearSystem

/-!
# The universal Jacobian family for the full restriction kernel

This file chooses a basis of the actual space of quadratic equations vanishing
on a finite homogeneous datum and specializes the common-source universal
Jacobian family to that complete linear system.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics HomogeneousProjective

universe u

section

variable {K A : Type u} [Field K] [CommRing A] [Algebra K A]
  [FiniteDimensional K A]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A basis of the full kernel of quadratic restriction to a finite homogeneous
datum. -/
noncomputable def quadraticRestrictionKernelBasis (x : Fin 4 → A) :
    Basis
      (Fin (finrank K
        (LinearMap.ker (homogeneousSectionRestriction (K := K) x 2)))) K
      (LinearMap.ker (homogeneousSectionRestriction (K := K) x 2)) := by
  letI : Module.Free K
      (LinearMap.ker (homogeneousSectionRestriction (K := K) x 2)) :=
    Module.Free.of_divisionRing K
      (LinearMap.ker (homogeneousSectionRestriction (K := K) x 2))
  exact Module.finBasis K
    (LinearMap.ker (homogeneousSectionRestriction (K := K) x 2))

/-- The full restriction-kernel basis, viewed as quadratic homogeneous
polynomials. -/
noncomputable def quadraticRestrictionKernelFrame (x : Fin 4 → A) :
    Fin (finrank K
      (LinearMap.ker (homogeneousSectionRestriction (K := K) x 2))) →
      homogeneousSubmodule (Fin 4) K 2 :=
  fun i => (quadraticRestrictionKernelBasis (K := K) x i).1

theorem quadraticRestrictionKernelFrame_linearIndependent (x : Fin 4 → A) :
    LinearIndependent K (quadraticRestrictionKernelFrame (K := K) x) := by
  exact linearIndependent_submodule_coe
    (LinearMap.ker (homogeneousSectionRestriction (K := K) x 2))
    (quadraticRestrictionKernelBasis (K := K) x)
    (quadraticRestrictionKernelBasis (K := K) x).linearIndependent

/-- Every member of the chosen frame vanishes on the finite homogeneous
datum. -/
theorem quadraticRestrictionKernelFrame_vanishes
    (x : Fin 4 → A)
    (i : Fin (finrank K
      (LinearMap.ker (homogeneousSectionRestriction (K := K) x 2)))) :
    (quadraticRestrictionKernelFrame (K := K) x i).1.eval₂
      (algebraMap K A) x = 0 := by
  exact LinearMap.mem_ker.mp
    (quadraticRestrictionKernelBasis (K := K) x i).property

/-- The universal quadric formed from the complete restriction-kernel basis
vanishes identically on the original finite homogeneous datum.  Its value is
the zero polynomial in the universal parameter coordinates. -/
theorem cubicTwoQuadricUniversalQuadric_restrictionKernel_eval_eq_zero
    (x : Fin 4 → A) :
    (cubicTwoQuadricUniversalQuadric
      (quadraticRestrictionKernelFrame (K := K) x)).eval₂
        (MvPolynomial.map (algebraMap K A)) (fun k => C (x k)) = 0 := by
  classical
  rw [cubicTwoQuadricUniversalQuadric]
  simp only [eval₂_sum, eval₂_mul, eval₂_C, map_X,
    MvPolynomial.eval₂_map]
  apply Finset.sum_eq_zero
  intro i hi
  let ι := Fin (finrank K
    (LinearMap.ker (homogeneousSectionRestriction (K := K) x 2)))
  have hvalue :
      MvPolynomial.eval₂
        ((MvPolynomial.map (σ := ι) (algebraMap K A)).comp
          (MvPolynomial.C : K →+* MvPolynomial ι K))
        (fun k => MvPolynomial.C (x k) : Fin 4 → MvPolynomial ι A)
        (quadraticRestrictionKernelFrame (K := K) x i).1 = 0 := by
    calc
      _ = MvPolynomial.eval₂
          ((MvPolynomial.C : A →+* MvPolynomial ι A).comp (algebraMap K A))
          (fun k => MvPolynomial.C (x k))
          (quadraticRestrictionKernelFrame (K := K) x i).1 := by
        rw [show
          (MvPolynomial.map (σ := ι) (algebraMap K A)).comp
              (MvPolynomial.C : K →+* MvPolynomial ι K) =
            (MvPolynomial.C : A →+* MvPolynomial ι A).comp
              (algebraMap K A) by
          ext a
          simp]
      _ = MvPolynomial.C ((quadraticRestrictionKernelFrame (K := K) x i).1.eval₂
          (algebraMap K A) x) :=
        (MvPolynomial.hom_eval₂
          (quadraticRestrictionKernelFrame (K := K) x i).1
          (algebraMap K A) (MvPolynomial.C : A →+* MvPolynomial ι A) x).symm
      _ = 0 := by
        rw [quadraticRestrictionKernelFrame_vanishes (K := K) x i, map_zero]
  rw [hvalue, mul_zero]

/-- The chosen vectors span the full restriction kernel, rather than a
proper subsystem. -/
theorem quadraticRestrictionKernelBasis_span_eq_top (x : Fin 4 → A) :
    Submodule.span K
      (Set.range (quadraticRestrictionKernelBasis (K := K) x)) = ⊤ :=
  (quadraticRestrictionKernelBasis (K := K) x).span_eq

/-- The polynomial span of the chosen quadratic frame is the complete
restriction kernel.  This exposes the intrinsic linear system in the ambient
space of homogeneous quadrics, rather than only in its kernel subtype. -/
theorem quadraticRestrictionKernelFrame_span_eq_ker (x : Fin 4 → A) :
    Submodule.span K (Set.range (quadraticRestrictionKernelFrame (K := K) x)) =
      LinearMap.ker (homogeneousSectionRestriction (K := K) x 2) := by
  apply le_antisymm
  · apply Submodule.span_le.2
    rintro y ⟨i, rfl⟩
    exact (quadraticRestrictionKernelBasis (K := K) x i).property
  · intro y hy
    let W := LinearMap.ker (homogeneousSectionRestriction (K := K) x 2)
    let y' : W := ⟨y, hy⟩
    have hy' : y' ∈ Submodule.span K
        (Set.range (quadraticRestrictionKernelBasis (K := K) x)) := by
      rw [quadraticRestrictionKernelBasis_span_eq_top]
      exact Submodule.mem_top
    have hmap : W.subtype '' Set.range (quadraticRestrictionKernelBasis (K := K) x) =
        Set.range (quadraticRestrictionKernelFrame (K := K) x) := by
      ext z
      constructor
      · rintro ⟨i, ⟨j, rfl⟩, rfl⟩
        exact ⟨j, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨quadraticRestrictionKernelBasis (K := K) x i, ⟨i, rfl⟩, rfl⟩
    have hspan : Submodule.map W.subtype
        (Submodule.span K (Set.range (quadraticRestrictionKernelBasis (K := K) x))) =
        Submodule.span K (Set.range (quadraticRestrictionKernelFrame (K := K) x)) := by
      rw [Submodule.map_span, hmap]
    rw [← hspan]
    exact ⟨y', hy', rfl⟩

/-- The simultaneous singular-member locus for the complete quadratic linear
system through the finite homogeneous datum. -/
noncomputable def
    cubicTwoQuadricRestrictionKernelSingularParameterLocus
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (x : Fin 4 → A) :
    Set (projectiveLinearSystemParameters (K := K)
      (τ := Fin (finrank K
        (LinearMap.ker (homogeneousSectionRestriction (K := K) x 2))))) :=
  cubicTwoQuadricUniversalSingularParameterLocus
    p q hp hq (quadraticRestrictionKernelFrame (K := K) x)

theorem
    isClosed_cubicTwoQuadricRestrictionKernelSingularParameterLocus
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (x : Fin 4 → A) :
    IsClosed
      (cubicTwoQuadricRestrictionKernelSingularParameterLocus
        p q hp hq x) :=
  isClosed_cubicTwoQuadricUniversalSingularParameterLocus
    p q hp hq (quadraticRestrictionKernelFrame (K := K) x)

/-- Once geometric input proves the full restriction-kernel bad locus
proper, its generic function-field member is nonsingular. -/
theorem
    genericFunctionField_closedPoint_avoids_cubicTwoQuadricRestrictionKernelSingularParameterLocus
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (x : Fin 4 → A)
    [IsIntegral (projectiveLinearSystemParameters (K := K)
      (τ := Fin (finrank K
        (LinearMap.ker (homogeneousSectionRestriction (K := K) x 2)))))]
    (hproper :
      cubicTwoQuadricRestrictionKernelSingularParameterLocus
        p q hp hq x ≠ Set.univ) :
    (projectiveLinearSystemParameters (K := K)
      (τ := Fin (finrank K
        (LinearMap.ker
          (homogeneousSectionRestriction (K := K) x 2))))).fromSpecStalk
        (genericPoint
          (projectiveLinearSystemParameters (K := K)
            (τ := Fin (finrank K
              (LinearMap.ker
                (homogeneousSectionRestriction (K := K) x 2))))))
        (IsLocalRing.closedPoint
          (projectiveLinearSystemParameters (K := K)
            (τ := Fin (finrank K
              (LinearMap.ker
                (homogeneousSectionRestriction (K := K) x 2))))).functionField) ∉
      cubicTwoQuadricRestrictionKernelSingularParameterLocus
        p q hp hq x := by
  exact
    genericFunctionField_closedPoint_avoids_cubicTwoQuadricUniversalSingularParameterLocus
      p q hp hq (quadraticRestrictionKernelFrame (K := K) x) hproper

/-- One explicit nonsingular member of the full restriction kernel is enough
to obtain the generic nonsingular member. -/
theorem
    genericFunctionField_closedPoint_avoids_cubicTwoQuadricRestrictionKernelSingularParameterLocus_of_exists
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (x : Fin 4 → A)
    [IsIntegral (projectiveLinearSystemParameters (K := K)
      (τ := Fin (finrank K
        (LinearMap.ker (homogeneousSectionRestriction (K := K) x 2)))))]
    (hgood : ∃ t : projectiveLinearSystemParameters (K := K)
        (τ := Fin (finrank K
          (LinearMap.ker (homogeneousSectionRestriction (K := K) x 2)))),
      t ∉ cubicTwoQuadricRestrictionKernelSingularParameterLocus
        p q hp hq x) :
    (projectiveLinearSystemParameters (K := K)
      (τ := Fin (finrank K
        (LinearMap.ker
          (homogeneousSectionRestriction (K := K) x 2))))).fromSpecStalk
        (genericPoint
          (projectiveLinearSystemParameters (K := K)
            (τ := Fin (finrank K
              (LinearMap.ker
                (homogeneousSectionRestriction (K := K) x 2))))))
        (IsLocalRing.closedPoint
          (projectiveLinearSystemParameters (K := K)
            (τ := Fin (finrank K
              (LinearMap.ker
                (homogeneousSectionRestriction (K := K) x 2))))).functionField) ∉
      cubicTwoQuadricRestrictionKernelSingularParameterLocus
        p q hp hq x := by
  exact
    genericFunctionField_closedPoint_avoids_cubicTwoQuadricUniversalSingularParameterLocus_of_exists
      p q hp hq (quadraticRestrictionKernelFrame (K := K) x) hgood

/-- A normalized ground-field specialization of a quadratic frame still
vanishes at any coordinate tuple on which every frame member vanishes. -/
theorem cubicTwoQuadricUniversalQuadric_parameterChart_map_eval_eq_zero
    [Infinite K] {n : ℕ}
    (v : Fin n → homogeneousSubmodule (Fin 4) K 2)
    (x : Fin 4 → A)
    (hvan : ∀ k, (v k).1.eval₂ (algebraMap K A) x = 0)
    (i : Fin n)
    (g : ChartRing
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i →+* K)
    (hgbase : g.comp (chartBaseMap
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i) =
        RingHom.id K) :
    (((cubicTwoQuadricUniversalQuadric v).map
      (cubicTwoQuadricParameterChartCoefficientMap (K := K) i)).map g).eval₂
        (algebraMap K A) x = 0 := by
  let c : Fin n → K := fun k => g (chartCoordinate
    (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i k)
  rw [MvPolynomial.map_map, cubicTwoQuadricParameterChartCoefficientMap_comp]
  rw [cubicTwoQuadricUniversalQuadric_map]
  simp only [hgbase, MvPolynomial.map_id, eval₂_sum, eval₂_mul, eval₂_C]
  apply Finset.sum_eq_zero
  intro k hk
  rw [hvan k, mul_zero]

/-- Properness of the mixed singular-member locus of an independent
quadratic frame produces an actual ground-field member which retains any
common finite base datum and cuts the fixed cubic--quadric curve étale. -/
theorem exists_vanishing_quadric_etale_of_singularParameterLocus_ne_univ
    [Infinite K] {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 2)
    (hv : LinearIndependent K v)
    (x : Fin 4 → A)
    (hvan : ∀ k, (v k).1.eval₂ (algebraMap K A) x = 0)
    (hproper : cubicTwoQuadricUniversalSingularParameterLocus
      p q hp hq v ≠ Set.univ) :
    ∃ (r : MvPolynomial (Fin 4) K) (hr : r.IsHomogeneous 2),
      r.eval₂ (algebraMap K A) x = 0 ∧ r ≠ 0 ∧
      Etale (toBase
        (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) := by
  obtain ⟨i, g, hgbase, hetale⟩ :=
    exists_groundField_cubicTwoQuadric_parameterChartHom_etale_of_singularParameterLocus_ne_univ
      p q hp hq v hproper
  let r : MvPolynomial (Fin 4) K :=
    ((cubicTwoQuadricUniversalQuadric v).map
      (cubicTwoQuadricParameterChartCoefficientMap (K := K) i)).map g
  have hr : r.IsHomogeneous 2 := by
    exact ((cubicTwoQuadricUniversalQuadric_isHomogeneous v).map _).map g
  have hrne : r ≠ 0 := by
    exact cubicTwoQuadricUniversalQuadric_parameterChart_map_ne_zero
      v hv i g
  have hrvan : r.eval₂ (algebraMap K A) x = 0 := by
    exact cubicTwoQuadricUniversalQuadric_parameterChart_map_eval_eq_zero
      v x hvan i g hgbase
  refine ⟨r, hr, hrvan, hrne, ?_⟩
  change Etale (toBase (tripleCompleteIntersectionHomogeneousIdeal p q
    (((cubicTwoQuadricUniversalQuadric v).map
      (cubicTwoQuadricParameterChartCoefficientMap (K := K) i)).map g)
    hp hq _))
  rw [hgbase] at hetale
  have hpmap : p.map (RingHom.id K) = p := by
    ext d
    rfl
  have hqmap : q.map (RingHom.id K) = q := by
    ext d
    rfl
  have hIdeal :
      tripleCompleteIntersectionHomogeneousIdeal
          (p.map (RingHom.id K)) (q.map (RingHom.id K))
          (((cubicTwoQuadricUniversalQuadric v).map
            (cubicTwoQuadricParameterChartCoefficientMap (K := K) i)).map g)
          (hp.map _) (hq.map _)
          ((cubicTwoQuadricUniversalQuadric_isHomogeneous v).map _ |>.map g) =
        tripleCompleteIntersectionHomogeneousIdeal p q
          (((cubicTwoQuadricUniversalQuadric v).map
            (cubicTwoQuadricParameterChartCoefficientMap (K := K) i)).map g)
          hp hq hr := by
    apply HomogeneousIdeal.ext
    simp only [tripleCompleteIntersectionHomogeneousIdeal_toIdeal,
      hpmap, hqmap]
  rw [hIdeal] at hetale
  exact hetale

/-- For the complete quadratic restriction kernel, properness of its
singular-member locus produces a nonzero quadric through the prescribed
finite datum whose intersection with the fixed cubic and quadric is étale. -/
theorem
    exists_restrictionKernel_quadric_etale_of_singularParameterLocus_ne_univ
    [Infinite K]
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (x : Fin 4 → A)
    (hproper : cubicTwoQuadricRestrictionKernelSingularParameterLocus
      p q hp hq x ≠ Set.univ) :
    ∃ (r : MvPolynomial (Fin 4) K) (hr : r.IsHomogeneous 2),
      r.eval₂ (algebraMap K A) x = 0 ∧ r ≠ 0 ∧
      Etale (toBase
        (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) := by
  exact exists_vanishing_quadric_etale_of_singularParameterLocus_ne_univ
    p q hp hq (quadraticRestrictionKernelFrame (K := K) x)
    (quadraticRestrictionKernelFrame_linearIndependent (K := K) x)
    x (quadraticRestrictionKernelFrame_vanishes (K := K) x) hproper

end

end PfaffianDescent
