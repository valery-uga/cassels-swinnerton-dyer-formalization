import PfaffianDescent.CorayActualGenericPlaneCubicSmooth
import PfaffianDescent.HyperplaneParametrization
import PfaffianDescent.LinearHypersurfaceSection
import AllCharacteristics.ProjectiveFiberSmoothness

/-! SOURCE ONLY / UNVERIFIED149. Identify the literal generic plane equation
with the existing rectangular linear-section construction. Its actual closed
immersion into the SAME coefficient-extended original cubic carries native
smoothness, not a separately selected abstract curve. No own curve component
is replaced here. The ideal-(p,H) same-Proj comparison remains separate. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
open scoped BigOperators
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The literal normal of the same generic plane is (1,t0,t1,t2). -/
def genericPlaneNormal {K : Type u} [Field K] : Fin 4 → GenericHyperplaneField K :=
  Fin.cases 1 (genericHyperplaneCoefficient (K := K))

/-- Existing native split linear inclusion of the SAME generic plane. -/
def genericPlaneInclusionMatrix {K : Type u} [Field K] :
    Matrix (Fin 4) (Fin 3) (GenericHyperplaneField K) :=
  PfaffianDescent.hyperplaneInclusion (genericPlaneNormal (K := K)) 0

theorem genericPlaneInclusionMatrix_leftInverse {K : Type u} [Field K] :
    PfaffianDescent.coordinateOmission (K := GenericHyperplaneField K) (n := 3) 0 *
      genericPlaneInclusionMatrix (K := K) = (1 : Matrix (Fin 3) (Fin 3) (GenericHyperplaneField K)) :=
  PfaffianDescent.hyperplaneInclusion_leftInverse _ _

/-- The existing rectangular restriction IS the literal substitution used
in the independently constructed generic-smoothness proof, on every polynomial. -/
theorem genericPlaneInclusionMatrix_substitution {K : Type u} [Field K] :
    PfaffianDescent.rectangularSubstitution (genericPlaneInclusionMatrix (K := K)) =
      planeHyperplaneRestrictionHom (genericHyperplaneCoefficient (K := K)) := by
  apply MvPolynomial.algHom_ext
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [PfaffianDescent.rectangularSubstitution_X,
      planeHyperplaneRestrictionHom_X_zero]
    change PfaffianDescent.rectangularLinearCoordinate
      (PfaffianDescent.hyperplaneInclusion (genericPlaneNormal (K := K)) 0) 0 = _
    rw [PfaffianDescent.hyperplaneInclusion_pivot_coordinate]
    simp [genericPlaneNormal, Fin.succAbove_zero]
  · rw [PfaffianDescent.rectangularSubstitution_X,
      planeHyperplaneRestrictionHom_X_succ]
    simpa only [genericPlaneInclusionMatrix, Fin.succAbove_zero] using
      PfaffianDescent.hyperplaneInclusion_other_coordinate (genericPlaneNormal (K := K)) 0 j

/-- The linear-section equation is the SAME actual generic cubic. -/
theorem genericPlaneInclusionMatrix_restrictedEquation
    {K : Type u} [Field K] (p : MvPolynomial (Fin 4) K) :
    PfaffianDescent.rectangularSubstitution (genericPlaneInclusionMatrix (K := K))
      (p.map (algebraMap K (GenericHyperplaneField K))) = genericPlaneCubic p := by
  rw [genericPlaneInclusionMatrix_substitution]
  rfl

/-- The actual native plane-section scheme is smooth, by the proved literal
equation comparison. Its source is the existing actual linear section. -/
theorem smoothCubic_actualLinearGenericPlaneSection_smooth
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] :
    Smooth (hypersurfaceToBase
      (PfaffianDescent.rectangularSubstitution (genericPlaneInclusionMatrix (K := K))
        (p.map (algebraMap K (GenericHyperplaneField K))))
      (PfaffianDescent.rectangularSubstitution_homogeneous
        (genericPlaneInclusionMatrix (K := K)) (hp.map _))) := by
  apply (smooth_hypersurfaceToBase_congr _ _ _ _
    (genericPlaneInclusionMatrix_restrictedEquation p)).mpr
  exact smoothCubic_actualGenericPlaneCubic_smooth p hp hp0

/-- The literal actual generic plane-section closed immersion into the SAME
original cubic after the parameter-field coefficient extension. -/
def actualGenericPlaneSectionImmersion
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) :
    PfaffianDescent.linearHypersurfaceSection (genericPlaneInclusionMatrix (K := K))
      (p.map (algebraMap K (GenericHyperplaneField K))) (hp.map _) ⟶
      hypersurface (p.map (algebraMap K (GenericHyperplaneField K))) (hp.map _) :=
  PfaffianDescent.linearHypersurfaceSectionι
    (genericPlaneInclusionMatrix (K := K))
    (PfaffianDescent.coordinateOmission (K := GenericHyperplaneField K) (n := 3) 0)
    genericPlaneInclusionMatrix_leftInverse _ _

instance actualGenericPlaneSectionImmersion_isClosedImmersion
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) :
    IsClosedImmersion (actualGenericPlaneSectionImmersion p hp) := by
  unfold actualGenericPlaneSectionImmersion
  infer_instance

/-- The actual generic plane-section immersion preserves the original
coefficient-extended structure morphism. -/
theorem actualGenericPlaneSectionImmersion_toBase
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) :
    actualGenericPlaneSectionImmersion p hp ≫
      hypersurfaceToBase (p.map (algebraMap K (GenericHyperplaneField K))) (hp.map _) =
      hypersurfaceToBase
        (PfaffianDescent.rectangularSubstitution (genericPlaneInclusionMatrix (K := K))
          (p.map (algebraMap K (GenericHyperplaneField K))))
        (PfaffianDescent.rectangularSubstitution_homogeneous
          (genericPlaneInclusionMatrix (K := K)) (hp.map _)) :=
  PfaffianDescent.linearHypersurfaceSectionι_toBase _ _ _ _ _

end PfaffianDescent.Coray
