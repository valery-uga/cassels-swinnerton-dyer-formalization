import PfaffianDescent.CubicClosedPointSerrePointSplittingPullback

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

/-- The first projection of the genuine base-change identification is the
usual map of fibers, followed by the original scheme identification. -/
@[reassoc] theorem pointSplittingPullbackIso_hom_fst
    {X Y Z T Q : Scheme.{u}} (f : X ⟶ Y) (c : Z ⟶ Y) (b : T ⟶ Z)
    (q : Q ⟶ Z) (e : Q ≅ pullback f c)
    (he : e.hom ≫ pullback.snd f c = q) :
    (pointSplittingPullbackIso f c b q e he).hom ≫ pullback.fst q b =
      pullback.map f (b ≫ c) f c (𝟙 X) b (𝟙 Y) (by simp) (by simp) ≫ e.inv := by
  dsimp only [pointSplittingPullbackIso]
  rw [pullback.lift_fst]
  apply (cancel_mono e.hom).1
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  apply pullback.hom_ext
  · simpa only [Category.assoc, Iso.inv_hom_id_assoc, pullback.map, pullback.lift_fst, Category.comp_id]
      using pullbackLeftPullbackSndIso_inv_fst f c b
  · simpa only [Category.assoc, Iso.inv_hom_id_assoc, pullback.map, pullback.lift_snd, Category.comp_id]
      using pullbackLeftPullbackSndIso_inv_fst_snd f c b

end PfaffianDescent
