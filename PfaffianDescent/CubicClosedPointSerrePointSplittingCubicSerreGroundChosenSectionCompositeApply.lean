import PfaffianDescent.CubicClosedPointSerrePointSplittingCubicSerreGroundChosenSectionCompositeMap
import PfaffianDescent.CubicClosedPointSerrePointSplittingCubicSerreGroundChosenSectionCompositeIso

noncomputable section
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
open scoped TensorProduct
namespace PfaffianDescent
open ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

/-- Exact actual section formula for the second field pullback followed by
literal PBComp, including its field scalar. -/
theorem pointSplittingCubicSerreGroundChosenSection_compositeTensorMap_tmul
    {K F E : Type u} [Field K] [Field F] [Field E]
    [Algebra K F] [Algebra F E]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    {N : (hypersurface p hp).Modules} (e : SerreExtensionData (hypersurface p hp) N)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E)]
    (c : E)
    (σ : SchemeModuleGlobalSectionsOver
      (hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F)))
      ((Scheme.Modules.pullback
        (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)).obj e.E)) :
    pointSplittingCubicSerreGroundChosenSection_compositeTensorMap (F := F) (E := E) p hp e C
      (c ⊗ₜ[F] σ) =
    c • (serreActualPulledGlobalSection
      (hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F)))
      (hypersurfaceToBase ((p.map (algebraMap K F)).map (algebraMap F E))
        ((hp.map (algebraMap K F)).map (algebraMap F E)))
      (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap F E)
        (p.map (algebraMap K F)) (hp.map (algebraMap K F)))
      ((Scheme.Modules.pullback
        (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)).obj e.E) σ ≫
      (pointSplittingCubicSerreGroundChosenSection_compositeModuleIso (F := F) (E := E) p hp e.E).hom) := by
  let s := serreIncidenceCubicCoefficientPulledSerre (algebraMap K F) p hp e C
  let Cs := serreIncidenceCubicCoefficientPulledCover (algebraMap K F) p hp e C
  letI : FiniteDimensional F (SchemeModuleGlobalSectionsOver
      (hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F))) s.E) :=
    serreIncidenceCubicCoefficientGlobalSections_finiteDimensional (F := F) p hp e C
  change cubicClosedPointSerreDegreeThreeEvaluationModuleIsoLinearEquiv (K := E) _
    (pointSplittingCubicSerreGroundChosenSection_compositeModuleIso (F := F) (E := E) p hp e.E)
    (pointSplittingCubicSerreGroundKernel_coefficientFrame (F := E)
      (p.map (algebraMap K F)) (hp.map (algebraMap K F)) s Cs (c ⊗ₜ[F] σ)) = _
  rw [pointSplittingCubicSerreGroundChosenSection_coefficientFrame_tmul, map_smul,
    pointSplittingGroundKernel_moduleIso_apply]

end PfaffianDescent
