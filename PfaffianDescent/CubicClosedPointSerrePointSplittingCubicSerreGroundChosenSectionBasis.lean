import PfaffianDescent.CubicClosedPointSerrePointSplittingCubicSerreGroundChosenSectionCompositeIso
import PfaffianDescent.CubicClosedPointSerrePointSplittingCubicSerreGroundChosenSectionPullbackComp
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceCubicCoefficientGlobalFrame

noncomputable section
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
open scoped TensorProduct
namespace PfaffianDescent
open ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

/-- The SAME coefficient frame basis consists of the literal original section pullbacks. -/
theorem pointSplittingCubicSerreGroundChosenSection_coefficientBasis_apply
    {K F : Type u} [Field K] [Field F] [Algebra K F]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    {N : (hypersurface p hp).Modules} (e : SerreExtensionData (hypersurface p hp) N)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E)]
    (h9 : Module.finrank K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E) = 9)
    (j : Fin 9) :
    serreIncidenceCubicCoefficientGlobalBasis (F := F) p hp e C h9 j =
    serreActualPulledGlobalSection (hypersurfaceToBase p hp)
      (hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F)))
      (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp) e.E
      (Module.finBasisOfFinrankEq K
        (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E) h9 j) := by
  rw [serreIncidenceCubicCoefficientGlobalBasis, Module.Basis.map_apply,
    Module.Basis.baseChange_apply]
  simp only [serreIncidenceCubicCoefficientGlobalFrame, LinearEquiv.trans_apply]
  rw [pointSplittingCubicSerreGroundChosenSection_fieldFrame_tmul, one_smul]
  exact pointSplittingCubicSerreGroundKernel_coefficientIso_pulled p hp e.E _

/-- Actual section equality on the SAME twice coefficient cubic for each
canonical transported basis section, through the actual PBComp module iso. -/
theorem pointSplittingCubicSerreGroundChosenSection_coefficientBasis_pulled
    {K F E : Type u} [Field K] [Field F] [Field E] [Algebra K F] [Algebra F E]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    {N : (hypersurface p hp).Modules} (e : SerreExtensionData (hypersurface p hp) N)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E)]
    (h9 : Module.finrank K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E) = 9)
    (j : Fin 9) :
    serreActualPulledGlobalSection
      (hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F)))
      (hypersurfaceToBase ((p.map (algebraMap K F)).map (algebraMap F E))
        ((hp.map (algebraMap K F)).map (algebraMap F E)))
      (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap F E)
        (p.map (algebraMap K F)) (hp.map (algebraMap K F)))
      ((Scheme.Modules.pullback
        (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)).obj e.E)
      (serreIncidenceCubicCoefficientGlobalBasis (F := F) p hp e C h9 j) ≫
      (pointSplittingCubicSerreGroundChosenSection_compositeModuleIso (F := F) (E := E) p hp e.E).hom =
    serreActualPulledGlobalSection (hypersurfaceToBase p hp)
      (hypersurfaceToBase ((p.map (algebraMap K F)).map (algebraMap F E))
        ((hp.map (algebraMap K F)).map (algebraMap F E)))
      (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap F E)
        (p.map (algebraMap K F)) (hp.map (algebraMap K F)) ≫
        cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp) e.E
      (Module.finBasisOfFinrankEq K
        (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E) h9 j) := by
  rw [pointSplittingCubicSerreGroundChosenSection_coefficientBasis_apply]
  exact pointSplittingCubicSerreGroundChosenSection_pulledSection_comp _ _ _ _ _ _ rfl e.E _

end PfaffianDescent
