import PfaffianDescent.CubicClosedPointSerrePointSplittingCubicSerreGroundChosenSectionSquare

noncomputable section
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
open scoped TensorProduct
namespace PfaffianDescent
open ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

/-- Equality of actual sections on the same twice-coefficient cubic, for ANY
actual coefficient-cubic global section, not merely its fibre evaluations. -/
theorem pointSplittingCubicSerreGroundChosenSection_section_eq_combination
    {K F E : Type u} [Field K] [Field F] [Field E]
    [Algebra K F] [Algebra F E] [Algebra K E] [IsScalarTower K F E]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    {N : (hypersurface p hp).Modules} (e : SerreExtensionData (hypersurface p hp) N)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E)]
    (h9 : Module.finrank K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E) = 9)
    (σ : SchemeModuleGlobalSectionsOver
      (hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F)))
      ((Scheme.Modules.pullback
        (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)).obj e.E)) :
    serreActualPulledGlobalSection
      (hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F)))
      (hypersurfaceToBase ((p.map (algebraMap K F)).map (algebraMap F E))
        ((hp.map (algebraMap K F)).map (algebraMap F E)))
      (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap F E)
        (p.map (algebraMap K F)) (hp.map (algebraMap K F)))
      ((Scheme.Modules.pullback
        (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)).obj e.E) σ ≫
      (pointSplittingCubicSerreGroundChosenSection_compositeModuleIso (F := F) (E := E) p hp e.E).hom =
    pointSplittingCubicSerreGroundChosenSection_originalCombinationMap (F := F) (E := E) p hp e h9
      (pointSplittingCubicSerreGroundKernel_originalSectionsTensorEquiv
        (F := F) (E := E) p hp e C (1 ⊗ₜ[F] σ)) := by
  have h := LinearMap.congr_fun
    (pointSplittingCubicSerreGroundChosenSection_tensor_square (F := F) (E := E) p hp e C h9)
    (pointSplittingCubicSerreGroundKernel_originalSectionsTensorEquiv
      (F := F) (E := E) p hp e C (1 ⊗ₜ[F] σ))
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearEquiv.symm_apply_apply,
    pointSplittingCubicSerreGroundChosenSection_compositeTensorMap_tmul, one_smul] using h

end PfaffianDescent
