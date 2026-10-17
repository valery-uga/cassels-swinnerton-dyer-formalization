import PfaffianDescent.VoisinDegreeElevenSerreIncidenceCubicCoefficientGlobalFrame
import PfaffianDescent.CubicClosedPointSerrePointSplittingCubicSerreGroundKernelOriginalSectionsTensor
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceGroundTensorFrameCoordinates

/-! Optional generic bridges between the two literal coefficient section frames.
These compare the literal pulled module before specialising to the native
function field or viewing it as the middle module of the pulled Serre data. -/
noncomputable section
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
open scoped TensorProduct
namespace PfaffianDescent
open ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

variable {K F E : Type u} [Field K] [Field F] [Field E]
variable [Algebra K F] [Algebra F E] [Algebra K E] [IsScalarTower K F E]
variable (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
variable {N : (hypersurface p hp).Modules}
variable (e : SerreExtensionData (hypersurface p hp) N)
variable (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
variable [FiniteDimensional K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E)]

/-- The two coefficient-frame names denote the same actual comparison. -/
theorem serreActualCoefficientGlobalFrame_eq_originalCoefficientFrame :
    serreIncidenceCubicCoefficientGlobalFrame (F := F) p hp e C =
      pointSplittingCubicSerreGroundKernel_coefficientFrame (F := F) p hp e C := by
  dsimp only [serreIncidenceCubicCoefficientGlobalFrame,
    pointSplittingCubicSerreGroundKernel_coefficientFrame]

/-- Expose the global basis formula at the literal pulled-module endpoint,
before viewing this basis as a basis of a pulled Serre middle module. -/
theorem serreActualCoefficientGlobalBasis_eq_mappedGlobalFrame
    (h9 : Module.finrank K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E) = 9) :
    serreIncidenceCubicCoefficientGlobalBasis (F := F) p hp e C h9 =
      ((Module.finBasisOfFinrankEq K
        (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E) h9).baseChange F).map
        (serreIncidenceCubicCoefficientGlobalFrame (F := F) p hp e C) := by
  rfl

/-- Transport basis equality by the small frame equality, keeping Basis.map
and the actual module endpoint intact. -/
theorem serreActualCoefficientGlobalBasis_eq_originalCoefficientFrame
    (h9 : Module.finrank K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E) = 9) :
    serreIncidenceCubicCoefficientGlobalBasis (F := F) p hp e C h9 =
      ((Module.finBasisOfFinrankEq K
        (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E) h9).baseChange F).map
        (pointSplittingCubicSerreGroundKernel_coefficientFrame (F := F) p hp e C) := by
  dsimp only [serreIncidenceCubicCoefficientGlobalBasis]
  exact congrArg
    (fun z => ((Module.finBasisOfFinrankEq K
      (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E) h9).baseChange F).map z)
    (serreActualCoefficientGlobalFrame_eq_originalCoefficientFrame (F := F) p hp e C)

/-- The actual original-section tensor comparison is the generic tensor frame
formed from the same coefficient global frame. -/
theorem serreActualOriginalSectionsTensorEquiv_eq_coefficientGlobalFrame :
    pointSplittingCubicSerreGroundKernel_originalSectionsTensorEquiv (F := F) (E := E) p hp e C =
      serreIncidenceGroundTensorFrame (E := E)
        (serreIncidenceCubicCoefficientGlobalFrame (F := F) p hp e C) := by
  exact congrArg (fun z => serreIncidenceGroundTensorFrame (E := E) z)
    (serreActualCoefficientGlobalFrame_eq_originalCoefficientFrame (F := F) p hp e C).symm

end PfaffianDescent
