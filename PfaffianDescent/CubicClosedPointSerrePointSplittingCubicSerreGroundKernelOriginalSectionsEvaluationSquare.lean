import PfaffianDescent.CubicClosedPointSerrePointSplittingCubicSerreGroundKernelOriginalSectionsTensor

noncomputable section
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
open scoped TensorProduct
namespace PfaffianDescent
open ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

/-- The actual coefficient Gamma/tensor comparison commutes with literal
three-point evaluation and the native pulled-point Gamma isomorphism. -/
theorem pointSplittingCubicSerreGroundKernel_originalSections_evaluation_square
    {K F E : Type u} [Field K] [Field F] [Field E]
    [Algebra K F] [Algebra F E] [Algebra K E] [IsScalarTower K F E]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    {N : (hypersurface p hp).Modules} (e : SerreExtensionData (hypersurface p hp) N)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E)]
    (r : Fin 3 → (Spec (.of E) ⟶ hypersurface (p.map (algebraMap K F)) (hp.map (algebraMap K F))))
    (q : Fin 3 → (Spec (.of E) ⟶ hypersurface p hp))
    (hq : ∀ i, r i ≫ cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp = q i)
    (hr : ∀ i, r i ≫ hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F)) =
      Spec.map (CommRingCat.ofHom (algebraMap F E)))
    (hqb : ∀ i, q i ≫ hypersurfaceToBase p hp =
      Spec.map (CommRingCat.ofHom (algebraMap K E))) :
    (serreActualThreePointPulledGammaEquiv
      (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp) r q hq e.E).toLinearMap.comp
      ((cubicClosedPointSerreSurfaceJetCotangent_threePointSectionEvaluationTensor
        (hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F))) r hr
        ((Scheme.Modules.pullback
          (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)).obj e.E)).comp
        (pointSplittingCubicSerreGroundKernel_originalSectionsTensorEquiv (F := F) (E := E) p hp e C).symm.toLinearMap) =
    cubicClosedPointSerreSurfaceJetCotangent_threePointSectionEvaluationTensor
      (hypersurfaceToBase p hp) q hqb e.E := by
  apply (Module.finBasis K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E)).baseChange E |>.ext
  intro i
  simp only [LinearMap.comp_apply, Module.Basis.baseChange_apply,
    LinearEquiv.coe_toLinearMap]
  rw [pointSplittingCubicSerreGroundKernel_originalSectionsTensorEquiv_symm_basis]
  exact serreActualThreePointPulledGammaEquiv_one_tmul
    (hypersurfaceToBase p hp)
    (hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F)))
    (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)
    r q hq hr hqb e.E _

end PfaffianDescent
