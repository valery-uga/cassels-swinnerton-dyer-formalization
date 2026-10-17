import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualNormalizedEndpointChart

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
open SerreExtensionData
universe u
set_option backward.isDefEq.respectTransparency false
section
variable {K : Type u} [Field K] {X : Scheme.{u}}
  {M : SheafOfModules.{u} X.ringCatSheaf} {e : SerreExtensionData X M}
  (f : X ⟶ Spec (.of K))

def cubicClosedPointSerreFiniteZeroResidual_normalizedEndpointAmbient (b : Bool) :
    X ⟶ projectiveLineAmbient K f :=
  pullback.lift (𝟙 _) (f ≫ projectiveLineEndpoint K b) (by
    simp [Category.assoc, projectiveLineEndpoint_toBase])

@[reassoc (attr := simp)]
theorem cubicClosedPointSerreFiniteZeroResidual_normalizedEndpointAmbient_toSurface (b : Bool) :
    cubicClosedPointSerreFiniteZeroResidual_normalizedEndpointAmbient f b ≫
      projectiveLineAmbientToScheme K f = 𝟙 _ := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem cubicClosedPointSerreFiniteZeroResidual_normalizedEndpointAmbient_toParameter (b : Bool) :
    cubicClosedPointSerreFiniteZeroResidual_normalizedEndpointAmbient f b ≫
      projectiveLineAmbientToLine K f = f ≫ projectiveLineEndpoint K b :=
  pullback.lift_snd _ _ _

theorem cubicClosedPointSerreFiniteZeroResidual_normalizedEndpointAmbient_local
    (C : SerreExtensionRankTwoAffineCover e) (i : C.ι) (b : Bool) :
    (C.U i).ι ≫ cubicClosedPointSerreFiniteZeroResidual_normalizedEndpointAmbient f b =
    cubicClosedPointSerreFiniteZeroResidual_normalizedEndpointChart f C i b ≫
      (C.projectiveLineOpenCover f).f (i, b) := by
  apply pullback.hom_ext
  · change (_ ≫ cubicClosedPointSerreFiniteZeroResidual_normalizedEndpointAmbient f b) ≫
      projectiveLineAmbientToScheme K f =
      (_ ≫ (C.projectiveLineOpenCover f).f (i, b)) ≫ projectiveLineAmbientToScheme K f
    rw [Category.assoc, cubicClosedPointSerreFiniteZeroResidual_normalizedEndpointAmbient_toSurface,
      Category.comp_id, Category.assoc, C.projectiveLineOpenCover_toScheme f (i, b),
      ← Category.assoc, cubicClosedPointSerreFiniteZeroResidual_normalizedEndpointChart_toSurface,
      Category.id_comp]
  · change (_ ≫ cubicClosedPointSerreFiniteZeroResidual_normalizedEndpointAmbient f b) ≫
      projectiveLineAmbientToLine K f =
      (_ ≫ (C.projectiveLineOpenCover f).f (i, b)) ≫ projectiveLineAmbientToLine K f
    rw [Category.assoc, cubicClosedPointSerreFiniteZeroResidual_normalizedEndpointAmbient_toParameter,
      Category.assoc, C.projectiveLineOpenCover_toLine f (i, b)]
    simpa only [Category.assoc, cubicClosedPointSerreFiniteZeroResidual_endpointChart_toLine] using
      (congrArg (fun a => a ≫ (lineProjOpenCover K).f b)
        (cubicClosedPointSerreFiniteZeroResidual_normalizedEndpointChart_toParameter f C i b)).symm

end
end PfaffianDescent
