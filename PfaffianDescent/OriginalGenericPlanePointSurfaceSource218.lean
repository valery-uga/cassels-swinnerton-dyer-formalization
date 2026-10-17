import PfaffianDescent.OriginalCurvePointSurfaceSourceFactory218
import PfaffianDescent.OriginalCurvePointSurfaceFactory210

/-! SOURCE ONLY218. The original smooth cubic alone supplies the required
integral/noetherian/DVR curve geometry. No Omega or residue certificate. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Every whole-quotient/source-coordinate witness is internally constructed
on the SAME original generic-plane curve from the original smooth cubic. -/
theorem originalGenericPlanePoint_exists_surfaceSourceUnitMatch218
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (P : closedPoints (hypersurface (genericPlaneCubic p) (genericPlaneCubic_isHomogeneous p hp)))
    (j : Fin 4)
    (hx : cubicSecondEquationCurveImmersion (p.map (algebraMap K (GenericHyperplaneField K)))
      (genericHyperplaneEquation (K := K)) (hp.map _) 1
      genericHyperplaneEquation_isHomogeneous ((genericPlaneCubicPairSchemeIso p hp).hom P.1) ∈
        quotientCoordinateOpen (equationIdeal (p.map (algebraMap K (GenericHyperplaneField K)))
          (hp.map _)) j) :
    let X := hypersurface (genericPlaneCubic p) (genericPlaneCubic_isHomogeneous p hp)
    let pL := p.map (algebraMap K (GenericHyperplaneField K))
    let hpL := hp.map (algebraMap K (GenericHyperplaneField K))
    let hpL0 := originalCubicCoefficientExtension_ne_zero210 p hp0
    letI : Smooth (hypersurfaceToBase pL hpL) :=
      smooth_hypersurfaceToBase_map (algebraMap K (GenericHyperplaneField K)) p hp
    originalCurvePointSurfaceSourceData218 pL (genericHyperplaneEquation (K := K)) hpL hpL0
      genericHyperplaneEquation_isHomogeneous genericHyperplaneEquation_ne_zero
      X (genericPlaneCubicPairSchemeIso p hp) P j hx := by
  dsimp only
  let X := hypersurface (genericPlaneCubic p) (genericPlaneCubic_isHomogeneous p hp)
  letI : Smooth (hypersurfaceToBase (p.map (algebraMap K (GenericHyperplaneField K))) (hp.map _)) :=
    smooth_hypersurfaceToBase_map (algebraMap K (GenericHyperplaneField K)) p hp
  letI : Smooth (hypersurfaceToBase (genericPlaneCubic p) (genericPlaneCubic_isHomogeneous p hp)) :=
    smoothCubic_actualGenericPlaneCubic_smooth p hp hp0
  letI : IsIntegral X := smoothCubic_actualGenericPlaneCubic_isIntegral p hp hp0
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian
    (hypersurfaceToBase (genericPlaneCubic p) (genericPlaneCubic_isHomogeneous p hp))
  letI : IsDiscreteValuationRing (X.presheaf.stalk P.1) :=
    smoothCubic_actualGenericPlaneCubic_closedPoint_stalk_isDVR200 p hp hp0 P
  exact originalCurvePoint_exists_surfaceSourceUnitMatch218 _ _ _
    (originalCubicCoefficientExtension_ne_zero210 p hp0)
    genericHyperplaneEquation_isHomogeneous genericHyperplaneEquation_ne_zero
    X (genericPlaneCubicPairSchemeIso p hp) P j hx

end PfaffianDescent.Coray
