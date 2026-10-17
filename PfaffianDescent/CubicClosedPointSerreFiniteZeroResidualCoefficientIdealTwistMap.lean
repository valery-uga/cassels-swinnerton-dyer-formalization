import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualCoefficientPositiveTwistIso
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualPullbackTensorNaturality
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent.ProjectiveNegativeTwist
universe u
set_option backward.isDefEq.respectTransparency false
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K L : Type u} [Field K] [Field L] (g : K →+* L)
  (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
  {D : Scheme.{u}} (i : D ⟶ hypersurface p hp) [IsClosedImmersion i]

/-- The literal comparison for the actual pulled ideal and native positive twist. -/
def cubicClosedPointSerreFiniteZeroResidual_coefficientIdealTwistMap (m : ℕ) :
    (Scheme.Modules.pullback (cubicPointTraceFieldBaseChangeCubicCoefficientMap g p hp)).obj
      (closedImmersionIdealTwist i
        (positiveSheafOfModules (grading (equationIdeal p hp)) m)) ⟶
    closedImmersionIdealTwist
      (pullback.fst (cubicPointTraceFieldBaseChangeCubicCoefficientMap g p hp) i)
      (positiveSheafOfModules (grading (equationIdeal (p.map g) (hp.map g))) m) :=
  cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap
    (cubicPointTraceFieldBaseChangeCubicCoefficientMap g p hp)
    (IdealSheafDataModule.closedImmersionModule i)
    (positiveSheafOfModules (grading (equationIdeal p hp)) m) ≫
  schemeModuleTensorMap
    (cubicClosedPointSerreFiniteZeroResidual_coefficientIdealIso g p hp i).hom
    (cubicClosedPointSerreFiniteZeroResidual_coefficientPositiveTwistIso g p hp m).hom

/-- The middle-object comparison uses the same tensor adjunct and twist map. -/
def cubicClosedPointSerreFiniteZeroResidual_coefficientTwistedUnitMap (m : ℕ) :
    (Scheme.Modules.pullback (cubicPointTraceFieldBaseChangeCubicCoefficientMap g p hp)).obj
      (schemeModuleTensor (SheafOfModules.unit (hypersurface p hp).ringCatSheaf)
        (positiveSheafOfModules (grading (equationIdeal p hp)) m)) ⟶
    schemeModuleTensor
      (SheafOfModules.unit (hypersurface (p.map g) (hp.map g)).ringCatSheaf)
      (positiveSheafOfModules (grading (equationIdeal (p.map g) (hp.map g))) m) :=
  cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap
    (cubicPointTraceFieldBaseChangeCubicCoefficientMap g p hp)
    (SheafOfModules.unit (hypersurface p hp).ringCatSheaf)
    (positiveSheafOfModules (grading (equationIdeal p hp)) m) ≫
  schemeModuleTensorMap
    (BundleSectionZeroLocus.pullbackUnitComparison
      (cubicPointTraceFieldBaseChangeCubicCoefficientMap g p hp))
    (cubicClosedPointSerreFiniteZeroResidual_coefficientPositiveTwistIso g p hp m).hom

 theorem cubicClosedPointSerreFiniteZeroResidual_coefficientIdealTwistMap_inclusion
    (m : ℕ) :
    cubicClosedPointSerreFiniteZeroResidual_coefficientIdealTwistMap g p hp i m ≫
      (closedImmersionIdealTwistSequence
        (pullback.fst (cubicPointTraceFieldBaseChangeCubicCoefficientMap g p hp) i)
        (positiveSheafOfModules (grading (equationIdeal (p.map g) (hp.map g))) m)).f =
    (Scheme.Modules.pullback (cubicPointTraceFieldBaseChangeCubicCoefficientMap g p hp)).map
      (closedImmersionIdealTwistSequence i
        (positiveSheafOfModules (grading (equationIdeal p hp)) m)).f ≫
      cubicClosedPointSerreFiniteZeroResidual_coefficientTwistedUnitMap g p hp m := by
  let f := cubicPointTraceFieldBaseChangeCubicCoefficientMap g p hp
  let T := positiveSheafOfModules (grading (equationIdeal p hp)) m
  let T' := positiveSheafOfModules (grading (equationIdeal (p.map g) (hp.map g))) m
  let a := IdealSheafDataModule.closedImmersionModuleToUnit i
  let a' := IdealSheafDataModule.closedImmersionModuleToUnit (pullback.fst f i)
  let eI := cubicClosedPointSerreFiniteZeroResidual_coefficientIdealIso g p hp i
  let eT := cubicClosedPointSerreFiniteZeroResidual_coefficientPositiveTwistIso g p hp m
  let u := BundleSectionZeroLocus.pullbackUnitComparison f
  change (cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap f _ T ≫
      schemeModuleTensorMap eI.hom eT.hom) ≫ schemeModuleTensorMap a' (𝟙 T') =
    (Scheme.Modules.pullback f).map (schemeModuleTensorMap a (𝟙 T)) ≫
      (cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap f _ T ≫
        schemeModuleTensorMap u eT.hom)
  have hI : eI.hom ≫ a' = (Scheme.Modules.pullback f).map a ≫ u :=
    cubicClosedPointSerreFiniteZeroResidual_coefficientIdealIso_toUnit g p hp i
  have hn := cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap_naturality f a (𝟙 T)
  rw [Category.assoc, schemeModuleTensorMap_comp, hI, Category.comp_id]
  have hcomp : schemeModuleTensorMap ((Scheme.Modules.pullback f).map a)
      (𝟙 ((Scheme.Modules.pullback f).obj T)) ≫ schemeModuleTensorMap u eT.hom =
      schemeModuleTensorMap ((Scheme.Modules.pullback f).map a ≫ u) eT.hom := by
    rw [schemeModuleTensorMap_comp, Category.id_comp]
  rw [(Scheme.Modules.pullback f).map_id] at hn
  rw [← hcomp, ← Category.assoc, ← hn]
  exact Category.assoc _ _ _
end PfaffianDescent.ProjectiveNegativeTwist
