import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualNormalizedEndpointAmbient

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreFiniteZeroResidual_normalizedEndpointAmbient_isPullback
    {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) (b : Bool) :
    IsPullback (cubicClosedPointSerreFiniteZeroResidual_normalizedEndpointAmbient f b)
      f (projectiveLineAmbientToLine K f) (projectiveLineEndpoint K b) := by
  have s : IsPullback (𝟙 X) f f
      (projectiveLineEndpoint K b ≫ projectiveLineProjToBase K) := by
    rw [projectiveLineEndpoint_toBase]
    exact IsPullback.of_id_fst
  let t := projectiveLineAmbientIsPullback K f
  have h := IsPullback.of_right' s t
  have he : t.lift (𝟙 X) (f ≫ projectiveLineEndpoint K b)
      (by rw [s.w, Category.assoc]) =
      cubicClosedPointSerreFiniteZeroResidual_normalizedEndpointAmbient f b := by
    apply t.hom_ext
    · simp only [IsPullback.lift_fst,
        cubicClosedPointSerreFiniteZeroResidual_normalizedEndpointAmbient_toSurface]
    · simp only [IsPullback.lift_snd,
        cubicClosedPointSerreFiniteZeroResidual_normalizedEndpointAmbient_toParameter]
  rw [he] at h
  exact h

end PfaffianDescent
