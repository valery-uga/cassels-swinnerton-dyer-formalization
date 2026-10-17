import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualProjectiveLineEndpointChart
import PfaffianDescent.SerreExtensionPencilProjectiveLine

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
open SerreExtensionData
universe u
set_option backward.isDefEq.respectTransparency false
attribute [local instance] MvPolynomial.gradedAlgebra
section
variable {K : Type u} [Field K] {X : Scheme.{u}}
  {M : SheafOfModules.{u} X.ringCatSheaf} {e : SerreExtensionData X M}
  (f : X ⟶ Spec (.of K))

private theorem endpointChart_toBase (b : Bool) :
    cubicClosedPointSerreFiniteZeroResidual_endpointChart K b ≫
      (lineProjOpenCover K).f b ≫ projectiveLineProjToBase K = 𝟙 _ := by
  rw [← Category.assoc,
    cubicClosedPointSerreFiniteZeroResidual_endpointChart_toLine,
    projectiveLineEndpoint_toBase]

def cubicClosedPointSerreFiniteZeroResidual_normalizedEndpointChart
    (C : SerreExtensionRankTwoAffineCover e) (i : C.ι) (b : Bool) :
    (C.U i : Scheme.{u}) ⟶ (C.projectiveLineOpenCover f).X (i, b) :=
  pullback.lift (𝟙 _) ((C.U i).ι ≫ f ≫
    cubicClosedPointSerreFiniteZeroResidual_endpointChart K b) (by
      simp only [Category.id_comp, Category.assoc, endpointChart_toBase, Category.comp_id]
      rfl)

@[reassoc (attr := simp)]
theorem cubicClosedPointSerreFiniteZeroResidual_normalizedEndpointChart_toSurface
    (C : SerreExtensionRankTwoAffineCover e) (i : C.ι) (b : Bool) :
    cubicClosedPointSerreFiniteZeroResidual_normalizedEndpointChart f C i b ≫
      C.projectiveLineOpenCover_toLocalScheme f (i, b) = 𝟙 _ :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem cubicClosedPointSerreFiniteZeroResidual_normalizedEndpointChart_toParameter
    (C : SerreExtensionRankTwoAffineCover e) (i : C.ι) (b : Bool) :
    cubicClosedPointSerreFiniteZeroResidual_normalizedEndpointChart f C i b ≫
      C.projectiveLineOpenCover_toLineChart f (i, b) =
    (C.U i).ι ≫ f ≫ cubicClosedPointSerreFiniteZeroResidual_endpointChart K b :=
  pullback.lift_snd _ _ _

theorem cubicClosedPointSerreFiniteZeroResidual_normalizedEndpointChart_coordinate
    (C : SerreExtensionRankTwoAffineCover e) (i : C.ι) (b : Bool) :
    (cubicClosedPointSerreFiniteZeroResidual_normalizedEndpointChart f C i b).appTop
      (C.projectiveLineLocalCoordinate f (i, b)) = 0 := by
  let v := cubicClosedPointSerreFiniteZeroResidual_normalizedEndpointChart f C i b
  change v.appTop (affineFunctionHom (C.projectiveLineOpenCover_toLineChart f (i, b)) _) = 0
  have hc := RingHom.congr_fun (affineFunctionHom_comp v
    (C.projectiveLineOpenCover_toLineChart f (i, b)))
    (AllCharacteristics.HomogeneousProjective.chartCoordinate
      (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule Bool K)) b (!b))
  apply hc.symm.trans
  have hp := congrArg (fun a : (C.U i : Scheme.{u}) ⟶ (lineProjOpenCover K).X b =>
    affineFunctionHom a (chartCoordinate
      (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule Bool K)) b (!b)))
    (cubicClosedPointSerreFiniteZeroResidual_normalizedEndpointChart_toParameter f C i b)
  apply hp.trans
  have hc' := RingHom.congr_fun (affineFunctionHom_comp ((C.U i).ι ≫ f)
    (cubicClosedPointSerreFiniteZeroResidual_endpointChart K b))
    (AllCharacteristics.HomogeneousProjective.chartCoordinate
      (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule Bool K)) b (!b))
  apply hc'.trans
  exact (congrArg ((C.U i).ι ≫ f).appTop.hom
    (cubicClosedPointSerreFiniteZeroResidual_endpointChart_coordinate K b)).trans (map_zero _)

end
end PfaffianDescent
