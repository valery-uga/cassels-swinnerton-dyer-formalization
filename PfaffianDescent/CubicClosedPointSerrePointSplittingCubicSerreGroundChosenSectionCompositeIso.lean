import PfaffianDescent.CubicClosedPointSerrePointSplittingCubicSerreGroundChosenSectionFrame

noncomputable section
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
open scoped TensorProduct
namespace PfaffianDescent
open ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

/-- The literal module composition isomorphism on the twice coefficient cubic. -/
def pointSplittingCubicSerreGroundChosenSection_compositeModuleIso
    {K F E : Type u} [Field K] [Field F] [Field E]
    [Algebra K F] [Algebra F E]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (M : (hypersurface p hp).Modules) :=
  (Scheme.Modules.pullbackComp
    (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap F E)
      (p.map (algebraMap K F)) (hp.map (algebraMap K F)))
    (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)).app M ≪≫
    (Scheme.Modules.pullbackCongr rfl).app M

end PfaffianDescent
