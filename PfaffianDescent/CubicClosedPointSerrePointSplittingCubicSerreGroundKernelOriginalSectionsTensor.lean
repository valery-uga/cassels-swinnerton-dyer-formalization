import PfaffianDescent.CubicClosedPointSerrePointSplittingCubicSerreGroundKernelOriginalSectionsFrame
import Mathlib.LinearAlgebra.TensorProduct.Tower

noncomputable section
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
open scoped TensorProduct
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

/-- Native coefficient section comparison and tensor associativity, preserving
actual original global sections. -/
def pointSplittingCubicSerreGroundKernel_originalSectionsTensorEquiv
    {K F E : Type u} [Field K] [Field F] [Field E]
    [Algebra K F] [Algebra F E] [Algebra K E] [IsScalarTower K F E]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    {N : (hypersurface p hp).Modules} (e : SerreExtensionData (hypersurface p hp) N)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E)] :=
  ((pointSplittingCubicSerreGroundKernel_coefficientFrame (F := F) p hp e C).symm.baseChange F E).trans
    (TensorProduct.AlgebraTensorModule.cancelBaseChange K F E E
      (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E))

/-- The inverse tensor comparison on the original basis is the literal pulled
section tensor. -/
theorem pointSplittingCubicSerreGroundKernel_originalSectionsTensorEquiv_symm_basis
    {K F E : Type u} [Field K] [Field F] [Field E]
    [Algebra K F] [Algebra F E] [Algebra K E] [IsScalarTower K F E]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    {N : (hypersurface p hp).Modules} (e : SerreExtensionData (hypersurface p hp) N)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E)]
    (i : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E))) :
    (pointSplittingCubicSerreGroundKernel_originalSectionsTensorEquiv (F := F) (E := E) p hp e C).symm
      (1 ⊗ₜ[K] Module.finBasis K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E) i) =
    1 ⊗ₜ[F] serreActualPulledGlobalSection (hypersurfaceToBase p hp)
      (hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F)))
      (ProjectiveNegativeTwist.cubicPointTraceFieldBaseChangeCubicCoefficientMap
        (algebraMap K F) p hp) e.E
      (Module.finBasis K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E) i) := by
  simp only [pointSplittingCubicSerreGroundKernel_originalSectionsTensorEquiv,
    LinearEquiv.trans_symm, LinearEquiv.trans_apply,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
    LinearEquiv.baseChange_symm, LinearEquiv.symm_symm,
    LinearEquiv.baseChange_tmul,
    pointSplittingCubicSerreGroundKernel_coefficientFrame_one_tmul_basis]

end PfaffianDescent
