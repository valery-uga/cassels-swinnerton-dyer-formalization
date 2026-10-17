import PfaffianDescent.CorayHomogeneousIdealLinearKernelProjection
import PfaffianDescent.CorayWholeSurfaceToPlaneCutCoordinateIdealRestriction
import AllCharacteristics.HomogeneousProjectiveAmbient

/-! Homogeneous preimages for the SAME whole ideal restriction kernel.
Only native quotient grading/decomposition is used. No graded-piece/H0
comparison, supplied graded witness, or dimension conclusion is input. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The genuine whole original surface ideal is homogeneous in the actual
quotient grading, by native homogeneous-ideal map of the original whole ideal. -/
theorem wholeOriginalSurfaceCoordinateIdeal_isHomogeneous
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) :
    (wholeOriginalSurfaceCoordinateIdeal C p hp).IsHomogeneous
      (grading (equationIdeal
        (p.map (algebraMap K (GenericHyperplaneField K))) (hp.map _))) := by
  let I := equationIdeal
    (p.map (algebraMap K (GenericHyperplaneField K))) (hp.map _)
  change ((wholeGenericCurveIdeal C).map (quotientGradedRingHom I)).toIdeal.IsHomogeneous
    (grading I)
  exact ((wholeGenericCurveIdeal C).map (quotientGradedRingHom I)).isHomogeneous

/-- The actual generic H class has degree one in the SAME original surface quotient. -/
theorem wholeOriginalSurfaceHyperplaneCoordinate_mem_degree_one
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) :
    Ideal.Quotient.mk (equationIdeal
      (p.map (algebraMap K (GenericHyperplaneField K))) (hp.map _)).toIdeal
        (genericHyperplaneEquation (K := K)) ∈
      grading (equationIdeal
        (p.map (algebraMap K (GenericHyperplaneField K))) (hp.map _)) 1 :=
  ⟨genericHyperplaneEquation (K := K), genericHyperplaneEquation_isHomogeneous, rfl⟩

/-- ORIGINAL p/q/minimal C produce a degree(d-1) kernel preimage under the
SAME actual H-multiplication, in the SAME actual whole surface ideal.
For d=0 the kernel element is zero and the chosen preimage is zero.
All coefficient actions and the actual ideal-to-ideal restriction are retained. -/
theorem selectedOriginalWholeCurve_wholeSurfaceToPlaneCutIdealRestriction_homogeneous_kernel_preimage
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hCmin : C.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes)
    (d : ℕ)
    (y : (wholeOriginalSurfaceCoordinateIdeal C p hp).restrictScalars (GenericHyperplaneField K))
    (hy : y.val ∈ grading (equationIdeal
      (p.map (algebraMap K (GenericHyperplaneField K))) (hp.map _)) d)
    (hzero : wholeOriginalSurfaceToPlaneCutCoordinateIdealRestriction C p hp y = 0) :
    ∃ z : (wholeOriginalSurfaceCoordinateIdeal C p hp).restrictScalars (GenericHyperplaneField K),
      z.val ∈ grading (equationIdeal
        (p.map (algebraMap K (GenericHyperplaneField K))) (hp.map _)) (d - 1) ∧
      wholeOriginalSurfaceCoordinateIdealHyperplaneMultiplication C p hp z = y := by
  classical
  let F := GenericHyperplaneField K
  let I := equationIdeal (p.map (algebraMap K F)) (hp.map _)
  let H := Ideal.Quotient.mk I.toIdeal (genericHyperplaneEquation (K := K))
  have hH : H ∈ grading I 1 := wholeOriginalSurfaceHyperplaneCoordinate_mem_degree_one p hp
  have hhom : (wholeOriginalSurfaceCoordinateIdeal C p hp).IsHomogeneous (grading I) :=
    wholeOriginalSurfaceCoordinateIdeal_isHomogeneous C p hp
  have hkernel := selectedOriginalWholeCurve_wholeSurfaceToPlaneCutIdealRestriction_ker_eq_hyperplane_range
    p q hp hp0 n hq hnot C hCmin
  have hyrange : y ∈ LinearMap.range
      (wholeOriginalSurfaceCoordinateIdealHyperplaneMultiplication C p hp) := by
    rw [← hkernel]
    exact LinearMap.mem_ker.mpr hzero
  obtain ⟨z, hzy⟩ := LinearMap.mem_range.mp hyrange
  have hzyval : H * z.val = y.val := congrArg Subtype.val hzy
  by_cases hd0 : d = 0
  · subst d
    have hyzero : y.val = 0 := homogeneous_linearFactor_degreeZero_eq_zero
      (grading I) H hH y.val hy z.val hzyval
    refine ⟨0, (grading I (0 - 1)).zero_mem, ?_⟩
    apply Subtype.ext
    change H * 0 = y.val
    rw [mul_zero, hyzero]
  · have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr hd0
    obtain ⟨w, hwJ, hwd, hwy⟩ :=
      homogeneousIdeal_linearFactor_exists_complementaryDegree
        (grading I) (wholeOriginalSurfaceCoordinateIdeal C p hp) hhom
        H hH d hd y.val hy z.val z.property hzyval
    refine ⟨⟨w, hwJ⟩, hwd, ?_⟩
    apply Subtype.ext
    exact hwy

end PfaffianDescent.Coray
