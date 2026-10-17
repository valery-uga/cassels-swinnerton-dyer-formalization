import PfaffianDescent.OriginalCurvePointGlobalBoundaryNonzero224
import PfaffianDescent.OriginalCurvePointSurfaceFactory210

/-! SOURCE ONLY224. Original cubic hypotheses derive the integral,
Noetherian and DVR geometry, and the required chart is chosen internally.
No differential normalization or nonvanishing certificate is assumed. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian MvPolynomial
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
variable {K : Type u} [Field K] [CharZero K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

/-- On the SAME actual generic-plane section of the ORIGINAL smooth cubic,
the literal global point connecting map is nonzero. Every geometric input,
including the original chart, is constructed internally; only native Ext
dictionaries on the actual schemes/rings are quantified in the result. -/
theorem originalGenericPlanePoint_exists_globalBoundaryNonzero224
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (P : closedPoints (hypersurface (genericPlaneCubic p) (genericPlaneCubic_isHomogeneous p hp))) :
    let X := hypersurface (genericPlaneCubic p) (genericPlaneCubic_isHomogeneous p hp)
    let pL := p.map (algebraMap K (GenericHyperplaneField K))
    let hpL := hp.map (algebraMap K (GenericHyperplaneField K))
    let hpL0 := originalCubicCoefficientExtension_ne_zero210 p hp0
    letI : Smooth (hypersurfaceToBase pL hpL) :=
      smooth_hypersurfaceToBase_map (algebraMap K (GenericHyperplaneField K)) p hp
    ∀ (hExtX : HasExt.{u} X.Modules)
      (hExtSurface : HasExt.{u} (hypersurface pL hpL).Modules)
      (hExtPoint : HasExt.{u + 1} (ModuleCat.{u} (X.presheaf.stalk P.1))),
    letI := hExtX
    letI := hExtSurface
    letI := hExtPoint
    ∃ (j : Fin 4)
      (hx : cubicSecondEquationCurveImmersion pL (genericHyperplaneEquation (K := K)) hpL 1
        genericHyperplaneEquation_isHomogeneous ((genericPlaneCubicPairSchemeIso p hp).hom P.1) ∈
          quotientCoordinateOpen (equationIdeal pL hpL) j),
      originalCurvePointBoundaryNonzeroData224 pL (genericHyperplaneEquation (K := K)) hpL hpL0
        genericHyperplaneEquation_isHomogeneous genericHyperplaneEquation_ne_zero
        X (genericPlaneCubicPairSchemeIso p hp) P j hx := by
  classical
  dsimp only
  letI : Smooth (hypersurfaceToBase (p.map (algebraMap K (GenericHyperplaneField K))) (hp.map _)) :=
    smooth_hypersurfaceToBase_map (algebraMap K (GenericHyperplaneField K)) p hp
  intro hExtX hExtSurface hExtPoint
  letI := hExtX
  letI := hExtSurface
  letI := hExtPoint
  let X := hypersurface (genericPlaneCubic p) (genericPlaneCubic_isHomogeneous p hp)
  letI : Smooth (hypersurfaceToBase (genericPlaneCubic p) (genericPlaneCubic_isHomogeneous p hp)) :=
    smoothCubic_actualGenericPlaneCubic_smooth p hp hp0
  letI : IsIntegral X := smoothCubic_actualGenericPlaneCubic_isIntegral p hp hp0
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian
    (hypersurfaceToBase (genericPlaneCubic p) (genericPlaneCubic_isHomogeneous p hp))
  letI : IsDiscreteValuationRing (X.presheaf.stalk P.1) :=
    smoothCubic_actualGenericPlaneCubic_closedPoint_stalk_isDVR200 p hp hp0 P
  let pL := p.map (algebraMap K (GenericHyperplaneField K))
  let hpL := hp.map (algebraMap K (GenericHyperplaneField K))
  let y := cubicSecondEquationCurveImmersion pL (genericHyperplaneEquation (K := K)) hpL 1
    genericHyperplaneEquation_isHomogeneous ((genericPlaneCubicPairSchemeIso p hp).hom P.1)
  have hcover : y ∈ ⨆ j : Fin 4, quotientCoordinateOpen (equationIdeal pL hpL) j := by
    rw [quotientCoordinateOpen_iSup]
    trivial
  obtain ⟨j, hx⟩ := TopologicalSpace.Opens.mem_iSup.mp hcover
  refine ⟨j, hx, ?_⟩
  exact originalCurvePoint_exists_globalBoundaryNonzero224 pL (genericHyperplaneEquation (K := K))
    hpL (originalCubicCoefficientExtension_ne_zero210 p hp0)
    genericHyperplaneEquation_isHomogeneous genericHyperplaneEquation_ne_zero
    X (genericPlaneCubicPairSchemeIso p hp) P j hx

end PfaffianDescent.Coray
