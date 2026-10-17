import PfaffianDescent.CorayActualGenericPlaneCubicIntegral
import PfaffianDescent.CorayActualGenericPlaneSectionImmersion

/-! SOURCE ONLY / UNVERIFIED150. Transport native integrality through the
proved literal plane-equation comparison. The actual closed-immersion source
into the SAME extended original cubic is geometrically integral; no abstract
replacement E or geometric component is selected. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u

/-- Equal plane equations define identical native integral schemes,
independently of the homogeneity proof. -/
theorem planeCubic_isIntegral_congr
    {K : Type u} [Field K]
    (q r : MvPolynomial (Fin 3) K) (hq : q.IsHomogeneous 3) (hr : r.IsHomogeneous 3)
    (h : q = r) : IsIntegral (hypersurface q hq) ↔ IsIntegral (hypersurface r hr) := by
  subst r
  rfl

/-- Equal plane equations have identical native geometric-integrality
statements, with their SAME structure maps. -/
theorem planeCubic_geometricallyIntegral_congr
    {K : Type u} [Field K]
    (q r : MvPolynomial (Fin 3) K) (hq : q.IsHomogeneous 3) (hr : r.IsHomogeneous 3)
    (h : q = r) : GeometricallyIntegral (hypersurfaceToBase q hq) ↔
      GeometricallyIntegral (hypersurfaceToBase r hr) := by
  subst r
  rfl

/-- The actual source of149's generic-plane closed immersion is native
integral, internally constructed from original cubic smoothness. -/
theorem smoothCubic_actualLinearGenericPlaneSection_isIntegral
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] :
    IsIntegral (PfaffianDescent.linearHypersurfaceSection
      (genericPlaneInclusionMatrix (K := K))
      (p.map (algebraMap K (GenericHyperplaneField K))) (hp.map _)) := by
  apply (planeCubic_isIntegral_congr _ _ _ _
    (genericPlaneInclusionMatrix_restrictedEquation p)).mpr
  exact smoothCubic_actualGenericPlaneCubic_isIntegral p hp hp0

/-- The SAME source of the literal generic-plane closed immersion is native
geometrically integral. It is not a newly chosen abstract curve. -/
theorem smoothCubic_actualLinearGenericPlaneSection_geometricallyIntegral
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] :
    GeometricallyIntegral (hypersurfaceToBase
      (PfaffianDescent.rectangularSubstitution (genericPlaneInclusionMatrix (K := K))
        (p.map (algebraMap K (GenericHyperplaneField K))))
      (PfaffianDescent.rectangularSubstitution_homogeneous
        (genericPlaneInclusionMatrix (K := K)) (hp.map _))) := by
  apply (planeCubic_geometricallyIntegral_congr _ _ _ _
    (genericPlaneInclusionMatrix_restrictedEquation p)).mpr
  exact smoothCubic_actualGenericPlaneCubic_geometricallyIntegral p hp hp0

end PfaffianDescent.Coray

