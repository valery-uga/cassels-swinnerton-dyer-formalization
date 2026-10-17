import PfaffianDescent.CubicClosedPointSerrePointSplittingCubicSerreGroundChosenSectionTensor
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceCubicCoefficientGlobalDimension

noncomputable section
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
open scoped TensorProduct
namespace PfaffianDescent
open ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

/-- Actual global-section tensor map on the SAME twice coefficient cubic,
transported through the literal pullback composition module isomorphism. -/
def pointSplittingCubicSerreGroundChosenSection_compositeTensorMap
    {K F E : Type u} [Field K] [Field F] [Field E]
    [Algebra K F] [Algebra F E]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    {N : (hypersurface p hp).Modules} (e : SerreExtensionData (hypersurface p hp) N)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E)] := by
  let a := algebraMap K F
  let β := algebraMap F E
  let f := cubicPointTraceFieldBaseChangeCubicCoefficientMap a p hp
  let g := cubicPointTraceFieldBaseChangeCubicCoefficientMap β (p.map a) (hp.map a)
  let s := serreIncidenceCubicCoefficientPulledSerre a p hp e C
  let Cs := serreIncidenceCubicCoefficientPulledCover a p hp e C
  letI : FiniteDimensional F (SchemeModuleGlobalSectionsOver
      (hypersurfaceToBase (p.map a) (hp.map a)) s.E) :=
    serreIncidenceCubicCoefficientGlobalSections_finiteDimensional (F := F) p hp e C
  let z := pointSplittingCubicSerreGroundKernel_coefficientFrame (F := E)
    (p.map a) (hp.map a) s Cs
  let em := (Scheme.Modules.pullbackComp g f).app e.E ≪≫
    (Scheme.Modules.pullbackCongr (rfl : g ≫ f = g ≫ f)).app e.E
  let base := hypersurfaceToBase ((p.map a).map β) ((hp.map a).map β)
  let t := cubicClosedPointSerreDegreeThreeEvaluationModuleIsoLinearEquiv (K := E) base em
  exact t.toLinearMap.comp z.toLinearMap

end PfaffianDescent
