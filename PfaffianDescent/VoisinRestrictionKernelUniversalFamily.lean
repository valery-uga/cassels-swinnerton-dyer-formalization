import PfaffianDescent.VoisinJacobianUniversalFamily
import PfaffianDescent.VoisinProjectiveLinearSystem

/-!
# The universal Jacobian family for the full restriction kernel

This file chooses a basis of the actual space of cubic equations vanishing
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

/-- A basis of the full kernel of cubic restriction to a finite homogeneous
datum. -/
noncomputable def cubicRestrictionKernelBasis (x : Fin 4 → A) :
    Basis
      (Fin (finrank K
        (LinearMap.ker (homogeneousSectionRestriction (K := K) x 3)))) K
      (LinearMap.ker (homogeneousSectionRestriction (K := K) x 3)) := by
  letI : Module.Free K
      (LinearMap.ker (homogeneousSectionRestriction (K := K) x 3)) :=
    Module.Free.of_divisionRing K
      (LinearMap.ker (homogeneousSectionRestriction (K := K) x 3))
  exact Module.finBasis K
    (LinearMap.ker (homogeneousSectionRestriction (K := K) x 3))

/-- The full restriction-kernel basis, viewed as cubic homogeneous
polynomials. -/
noncomputable def cubicRestrictionKernelFrame (x : Fin 4 → A) :
    Fin (finrank K
      (LinearMap.ker (homogeneousSectionRestriction (K := K) x 3))) →
      homogeneousSubmodule (Fin 4) K 3 :=
  fun i => (cubicRestrictionKernelBasis (K := K) x i).1

theorem cubicRestrictionKernelFrame_linearIndependent (x : Fin 4 → A) :
    LinearIndependent K (cubicRestrictionKernelFrame (K := K) x) := by
  exact linearIndependent_submodule_coe
    (LinearMap.ker (homogeneousSectionRestriction (K := K) x 3))
    (cubicRestrictionKernelBasis (K := K) x)
    (cubicRestrictionKernelBasis (K := K) x).linearIndependent

/-- Every member of the chosen frame vanishes on the finite homogeneous
datum. -/
theorem cubicRestrictionKernelFrame_vanishes
    (x : Fin 4 → A)
    (i : Fin (finrank K
      (LinearMap.ker (homogeneousSectionRestriction (K := K) x 3)))) :
    (cubicRestrictionKernelFrame (K := K) x i).1.eval₂
      (algebraMap K A) x = 0 := by
  exact LinearMap.mem_ker.mp
    (cubicRestrictionKernelBasis (K := K) x i).property

/-- The universal cubic formed from the complete restriction-kernel basis
vanishes identically on the original finite homogeneous datum.  Its value is
the zero polynomial in the universal parameter coordinates. -/
theorem tripleCompleteIntersectionUniversalCubic_restrictionKernel_eval_eq_zero
    (x : Fin 4 → A) :
    (tripleCompleteIntersectionUniversalCubic
      (cubicRestrictionKernelFrame (K := K) x)).eval₂
        (MvPolynomial.map (algebraMap K A)) (fun k => C (x k)) = 0 := by
  classical
  rw [tripleCompleteIntersectionUniversalCubic]
  simp only [eval₂_sum, eval₂_mul, eval₂_C, map_X,
    MvPolynomial.eval₂_map]
  apply Finset.sum_eq_zero
  intro i hi
  let ι := Fin (finrank K
    (LinearMap.ker (homogeneousSectionRestriction (K := K) x 3)))
  have hvalue :
      MvPolynomial.eval₂
        ((MvPolynomial.map (σ := ι) (algebraMap K A)).comp
          (MvPolynomial.C : K →+* MvPolynomial ι K))
        (fun k => MvPolynomial.C (x k) : Fin 4 → MvPolynomial ι A)
        (cubicRestrictionKernelFrame (K := K) x i).1 = 0 := by
    calc
      _ = MvPolynomial.eval₂
          ((MvPolynomial.C : A →+* MvPolynomial ι A).comp (algebraMap K A))
          (fun k => MvPolynomial.C (x k))
          (cubicRestrictionKernelFrame (K := K) x i).1 := by
        rw [show
          (MvPolynomial.map (σ := ι) (algebraMap K A)).comp
              (MvPolynomial.C : K →+* MvPolynomial ι K) =
            (MvPolynomial.C : A →+* MvPolynomial ι A).comp
              (algebraMap K A) by
          ext a
          simp]
      _ = MvPolynomial.C ((cubicRestrictionKernelFrame (K := K) x i).1.eval₂
          (algebraMap K A) x) :=
        (MvPolynomial.hom_eval₂
          (cubicRestrictionKernelFrame (K := K) x i).1
          (algebraMap K A) (MvPolynomial.C : A →+* MvPolynomial ι A) x).symm
      _ = 0 := by
        rw [cubicRestrictionKernelFrame_vanishes (K := K) x i, map_zero]
  rw [hvalue, mul_zero]

/-- The chosen vectors span the full restriction kernel, rather than a
proper subsystem. -/
theorem cubicRestrictionKernelBasis_span_eq_top (x : Fin 4 → A) :
    Submodule.span K
      (Set.range (cubicRestrictionKernelBasis (K := K) x)) = ⊤ :=
  (cubicRestrictionKernelBasis (K := K) x).span_eq

/-- The simultaneous singular-member locus for the complete cubic linear
system through the finite homogeneous datum. -/
noncomputable def
    tripleCompleteIntersectionRestrictionKernelSingularParameterLocus
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3)
    (x : Fin 4 → A) :
    Set (projectiveLinearSystemParameters (K := K)
      (τ := Fin (finrank K
        (LinearMap.ker (homogeneousSectionRestriction (K := K) x 3))))) :=
  tripleCompleteIntersectionUniversalSingularParameterLocus
    p q hp hq (cubicRestrictionKernelFrame (K := K) x)

theorem
    isClosed_tripleCompleteIntersectionRestrictionKernelSingularParameterLocus
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3)
    (x : Fin 4 → A) :
    IsClosed
      (tripleCompleteIntersectionRestrictionKernelSingularParameterLocus
        p q hp hq x) :=
  isClosed_tripleCompleteIntersectionUniversalSingularParameterLocus
    p q hp hq (cubicRestrictionKernelFrame (K := K) x)

/-- Once geometric input proves the full restriction-kernel bad locus
proper, its generic function-field member is nonsingular. -/
theorem
    genericFunctionField_closedPoint_avoids_tripleCompleteIntersectionRestrictionKernelSingularParameterLocus
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3)
    (x : Fin 4 → A)
    [IsIntegral (projectiveLinearSystemParameters (K := K)
      (τ := Fin (finrank K
        (LinearMap.ker (homogeneousSectionRestriction (K := K) x 3)))))]
    (hproper :
      tripleCompleteIntersectionRestrictionKernelSingularParameterLocus
        p q hp hq x ≠ Set.univ) :
    (projectiveLinearSystemParameters (K := K)
      (τ := Fin (finrank K
        (LinearMap.ker
          (homogeneousSectionRestriction (K := K) x 3))))).fromSpecStalk
        (genericPoint
          (projectiveLinearSystemParameters (K := K)
            (τ := Fin (finrank K
              (LinearMap.ker
                (homogeneousSectionRestriction (K := K) x 3))))))
        (IsLocalRing.closedPoint
          (projectiveLinearSystemParameters (K := K)
            (τ := Fin (finrank K
              (LinearMap.ker
                (homogeneousSectionRestriction (K := K) x 3))))).functionField) ∉
      tripleCompleteIntersectionRestrictionKernelSingularParameterLocus
        p q hp hq x := by
  exact
    genericFunctionField_closedPoint_avoids_tripleCompleteIntersectionUniversalSingularParameterLocus
      p q hp hq (cubicRestrictionKernelFrame (K := K) x) hproper

/-- One explicit nonsingular member of the full restriction kernel is enough
to obtain the generic nonsingular member. -/
theorem
    genericFunctionField_closedPoint_avoids_tripleCompleteIntersectionRestrictionKernelSingularParameterLocus_of_exists
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3)
    (x : Fin 4 → A)
    [IsIntegral (projectiveLinearSystemParameters (K := K)
      (τ := Fin (finrank K
        (LinearMap.ker (homogeneousSectionRestriction (K := K) x 3)))))]
    (hgood : ∃ t : projectiveLinearSystemParameters (K := K)
        (τ := Fin (finrank K
          (LinearMap.ker (homogeneousSectionRestriction (K := K) x 3)))),
      t ∉ tripleCompleteIntersectionRestrictionKernelSingularParameterLocus
        p q hp hq x) :
    (projectiveLinearSystemParameters (K := K)
      (τ := Fin (finrank K
        (LinearMap.ker
          (homogeneousSectionRestriction (K := K) x 3))))).fromSpecStalk
        (genericPoint
          (projectiveLinearSystemParameters (K := K)
            (τ := Fin (finrank K
              (LinearMap.ker
                (homogeneousSectionRestriction (K := K) x 3))))))
        (IsLocalRing.closedPoint
          (projectiveLinearSystemParameters (K := K)
            (τ := Fin (finrank K
              (LinearMap.ker
                (homogeneousSectionRestriction (K := K) x 3))))).functionField) ∉
      tripleCompleteIntersectionRestrictionKernelSingularParameterLocus
        p q hp hq x := by
  exact
    genericFunctionField_closedPoint_avoids_tripleCompleteIntersectionUniversalSingularParameterLocus_of_exists
      p q hp hq (cubicRestrictionKernelFrame (K := K) x) hgood

end

end PfaffianDescent
