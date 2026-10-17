import PfaffianDescent.CubicClosedPointSerrePointSplittingCubicSerreGroundChosenSectionFrame
import PfaffianDescent.CubicClosedPointSerrePointSplittingCubicSerreGroundKernelOriginalSectionsTensor

noncomputable section
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
open scoped TensorProduct
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

/-- Pure tensors under the inverse tower comparison, before inserting any geometry. -/
theorem pointSplittingCubicSerreGroundChosenSection_cancel_symm_tmul
    {K F E V W : Type u} [Field K] [Field F] [Field E]
    [Algebra K F] [Algebra F E] [Algebra K E] [IsScalarTower K F E]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module F W]
    (z : (F ⊗[K] V) ≃ₗ[F] W) (c : E) (s : V) :
    ((z.symm.baseChange F E).trans
      (TensorProduct.AlgebraTensorModule.cancelBaseChange K F E E V)).symm (c ⊗ₜ[K] s) =
      c ⊗ₜ[F] z (1 ⊗ₜ[K] s) := by
  simp only [LinearEquiv.trans_symm, LinearEquiv.trans_apply,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
    LinearEquiv.baseChange_symm, LinearEquiv.symm_symm, LinearEquiv.baseChange_tmul]

/-- The inverse native section-tensor comparison on ANY actual original
section is exactly its coefficient-map pullback tensor. -/
theorem pointSplittingCubicSerreGroundChosenSection_originalTensor_symm_tmul
    {K F E : Type u} [Field K] [Field F] [Field E]
    [Algebra K F] [Algebra F E] [Algebra K E] [IsScalarTower K F E]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    {N : (hypersurface p hp).Modules} (e : SerreExtensionData (hypersurface p hp) N)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E)]
    (c : E) (s : SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E) :
    (pointSplittingCubicSerreGroundKernel_originalSectionsTensorEquiv (F := F) (E := E) p hp e C).symm
      (c ⊗ₜ[K] s) =
    c ⊗ₜ[F] serreActualPulledGlobalSection (hypersurfaceToBase p hp)
      (hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F)))
      (ProjectiveNegativeTwist.cubicPointTraceFieldBaseChangeCubicCoefficientMap
        (algebraMap K F) p hp) e.E s := by
  have h := pointSplittingCubicSerreGroundChosenSection_cancel_symm_tmul
    (pointSplittingCubicSerreGroundKernel_coefficientFrame (F := F) p hp e C) c s
  have hs := pointSplittingCubicSerreGroundChosenSection_coefficientFrame_tmul
    (F := F) p hp e C (1 : F) s
  simp only [one_smul] at hs
  exact h.trans (congrArg (fun z => c ⊗ₜ[F] z) hs)

end PfaffianDescent
