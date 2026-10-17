import PfaffianDescent.CorayWholeSurfacePlaneIdealRestrictionKernel
import PfaffianDescent.CorayActualWholeCutPlaneIdealTransport

/-! The restriction actually lands in the ENTIRE literal plane-cut ideal
modulo its cubic equation. This supplies the whole ideal-to-ideal map and
its original-input kernel, with the same coefficient field action. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- ENTIRE same plane cut, viewed as an ideal in the same plane cubic quotient. -/
def wholeOriginalPlaneCutCoordinateIdeal
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) :
    Ideal (CoordinateRing (equationIdeal
      (planeHyperplaneRestrictionHom (genericHyperplaneCoefficient (K := K))
        (p.map (algebraMap K (GenericHyperplaneField K))))
      (planeHyperplaneRestrictionHom_homogeneous (genericHyperplaneCoefficient (K := K))
        _ (hp.map _)))) :=
  (wholeGenericCutPlaneIdeal C).toIdeal.map
    (Ideal.Quotient.mk (equationIdeal
      (planeHyperplaneRestrictionHom (genericHyperplaneCoefficient (K := K))
        (p.map (algebraMap K (GenericHyperplaneField K))))
      (planeHyperplaneRestrictionHom_homogeneous (genericHyperplaneCoefficient (K := K))
        _ (hp.map _))).toIdeal)

/-- Every original ideal class restricts into the same whole plane-cut ideal. -/
theorem wholeOriginalSurfaceCoordinateIdealRestriction_mem_planeCut
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (y : (wholeOriginalSurfaceCoordinateIdeal C p hp).restrictScalars (GenericHyperplaneField K)) :
    wholeOriginalSurfaceCoordinateIdealRestriction C p hp y ∈
      wholeOriginalPlaneCutCoordinateIdeal C p hp := by
  let F := GenericHyperplaneField K
  let f := p.map (algebraMap K F)
  let hf := hp.map (algebraMap K F)
  let mk := Ideal.Quotient.mk (equationIdeal f hf).toIdeal
  have hymem : y.val ∈ (wholeGenericCurveIdeal C).toIdeal.map mk := y.property
  obtain ⟨q, hqJ, hqy⟩ :=
    (Ideal.mem_map_iff_of_surjective mk (Ideal.Quotient.mk_surjective)).mp hymem
  have hqCut : q ∈ (wholeGenericCutIdeal C).toIdeal :=
    (show (wholeGenericCurveIdeal C).toIdeal ≤ (wholeGenericCutIdeal C).toIdeal from le_sup_left) hqJ
  have hqPlane : planeHyperplaneRestrictionHom (genericHyperplaneCoefficient (K := K)) q ∈
      (wholeGenericCutPlaneIdeal C).toIdeal := by
    rw [wholeGenericCutPlaneIdeal_toIdeal]
    exact Ideal.mem_map_of_mem _ hqCut
  change surfacePlaneCoordinateRestriction (genericHyperplaneCoefficient (K := K))
    f hf y.val ∈ (wholeOriginalPlaneCutCoordinateIdeal C p hp)
  rw [← hqy, surfacePlaneCoordinateRestriction_mk]
  exact Ideal.mem_map_of_mem _ hqPlane

/-- The actual whole ideal-to-whole ideal restriction, with genuine landing proof. -/
def wholeOriginalSurfaceToPlaneCutCoordinateIdealRestriction
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) :
    (wholeOriginalSurfaceCoordinateIdeal C p hp).restrictScalars (GenericHyperplaneField K) →ₗ[GenericHyperplaneField K]
      (wholeOriginalPlaneCutCoordinateIdeal C p hp).restrictScalars (GenericHyperplaneField K) :=
  LinearMap.codRestrict
    ((wholeOriginalPlaneCutCoordinateIdeal C p hp).restrictScalars (GenericHyperplaneField K))
    (wholeOriginalSurfaceCoordinateIdealRestriction C p hp)
    (wholeOriginalSurfaceCoordinateIdealRestriction_mem_planeCut C p hp)

/-- ORIGINAL p/q/minimal C construct the ideal-to-ideal restriction kernel.
All objects are the literal whole originals; no supplied restriction,
regularity, finite rank or dimension estimate is a premise. -/
theorem selectedOriginalWholeCurve_wholeSurfaceToPlaneCutIdealRestriction_ker_eq_hyperplane_range
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hCmin : C.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes) :
    LinearMap.ker (wholeOriginalSurfaceToPlaneCutCoordinateIdealRestriction C p hp) =
      LinearMap.range (wholeOriginalSurfaceCoordinateIdealHyperplaneMultiplication C p hp) := by
  calc
    LinearMap.ker (wholeOriginalSurfaceToPlaneCutCoordinateIdealRestriction C p hp) =
        LinearMap.ker (wholeOriginalSurfaceCoordinateIdealRestriction C p hp) := by
      apply Submodule.ext
      intro y
      change wholeOriginalSurfaceToPlaneCutCoordinateIdealRestriction C p hp y = 0 ↔
        wholeOriginalSurfaceCoordinateIdealRestriction C p hp y = 0
      constructor
      · intro hy
        exact congrArg Subtype.val hy
      · intro hy
        apply Subtype.ext
        exact hy
    _ = _ := selectedOriginalWholeCurve_surfacePlaneIdealRestriction_ker_eq_hyperplane_range
      p q hp hp0 n hq hnot C hCmin

end PfaffianDescent.Coray
