import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualArtinianFibreStalk

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

/-- Every actual zero point on a quasi-finite closed zero chart defines a
closed point of the actual ambient fibre. -/
theorem cubicClosedPointSerreFiniteZeroResidual_closed_asFibre_of_quasiFinite_zero
    {Z X E : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (f : X ⟶ E)
    [LocallyQuasiFinite (i ≫ f)] (z : Z) :
    IsClosed ({f.asFiber (i z)} : Set (f.fiber (f (i z)))) := by
  let y := f (i z)
  let v : (i ≫ f).fiber y ⟶ f.fiber y :=
    pullback.map (i ≫ f) (E.fromSpecResidueField y) f (E.fromSpecResidueField y)
      i (𝟙 _) (𝟙 _) (by simp) (by simp)
  letI : IsClosedImmersion v := by
    dsimp [v]
    rw [pullback_map_eq_pullbackFstFstIso_inv]
    infer_instance
  have hv : v ((i ≫ f).asFiber z) = f.asFiber (i z) := by
    apply (f.fiberι y).isEmbedding.injective
    change (v ≫ f.fiberι y) ((i ≫ f).asFiber z) = _
    have hc : v ≫ f.fiberι y = (i ≫ f).fiberι y ≫ i := by
      simp [v, Scheme.Hom.fiberι, pullback.map]
    rw [hc]
    change i ((i ≫ f).fiberι ((i ≫ f) z) ((i ≫ f).asFiber z)) =
      f.fiberι (f (i z)) (f.asFiber (i z))
    rw [(i ≫ f).fiberι_asFiber z, f.fiberι_asFiber (i z)]
  rw [← hv]
  exact cubicClosedPointSerreFiniteZeroResidual_closed_image_of_quasiFinite_fibre
    (i ≫ f) y v ((i ≫ f).asFiber z)

end PfaffianDescent
