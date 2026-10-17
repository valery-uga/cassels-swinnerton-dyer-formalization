import PfaffianDescent.VoisinDegreeElevenSerreIncidenceGroundTensorFrameCoordinates
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceCubicCoefficientGlobalFrame
import PfaffianDescent.CubicClosedPointSerrePointSplittingCubicSerreGroundKernelOriginalSectionsTensor

/-! # Native original-section tensor comparison preserves the transported Fin9 coordinates -/
noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped TensorProduct
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
open Module
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem serreIncidenceCubicGroundTensor_coordinates
    {K F E : Type u} [Field K] [Field F] [Field E]
    [Algebra K F] [Algebra F E] [Algebra K E] [IsScalarTower K F E]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    {N : (hypersurface p hp).Modules} (e : SerreExtensionData (hypersurface p hp) N)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E)]
    (h9 : finrank K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E) = 9)
    (t : E ⊗[F] SchemeModuleGlobalSectionsOver
      (hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F)))
      ((Scheme.Modules.pullback
        (ProjectiveNegativeTwist.cubicPointTraceFieldBaseChangeCubicCoefficientMap
          (algebraMap K F) p hp)).obj e.E)) :
    ((finBasisOfFinrankEq K _ h9).baseChange E).equivFun
      (pointSplittingCubicSerreGroundKernel_originalSectionsTensorEquiv (F := F) (E := E) p hp e C t) =
    ((serreIncidenceCubicCoefficientGlobalBasis (F := F) p hp e C h9).baseChange E).equivFun t := by
  have hq : pointSplittingCubicSerreGroundKernel_originalSectionsTensorEquiv
      (F := F) (E := E) p hp e C =
      serreIncidenceGroundTensorFrame (E := E)
        (serreIncidenceCubicCoefficientGlobalFrame (F := F) p hp e C) := rfl
  rw [hq]
  simpa only [serreIncidenceCubicCoefficientGlobalBasis] using
    serreIncidenceGroundTensorFrame_coordinates
      (serreIncidenceCubicCoefficientGlobalFrame (F := F) p hp e C)
      (finBasisOfFinrankEq K _ h9) t

end PfaffianDescent
