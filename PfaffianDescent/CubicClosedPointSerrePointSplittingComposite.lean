import PfaffianDescent.CubicClosedPointSerrePointSplittingProjection

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

@[reassoc] theorem pointSplittingPullbackIso_congrHom_fst
    {X Y Z T Q : Scheme.{u}} (f : X ⟶ Y) (c : Z ⟶ Y) (b : T ⟶ Z)
    (r : T ⟶ Y) (hr : r = b ≫ c)
    (q : Q ⟶ Z) (e : Q ≅ pullback f c)
    (he : e.hom ≫ pullback.snd f c = q) :
    (pullback.congrHom (f₁ := f) (g₁ := r) rfl hr).hom ≫
      (pointSplittingPullbackIso f c b q e he).hom ≫ pullback.fst q b =
      pullback.map f r f c (𝟙 X) b (𝟙 Y) (by simp) (by simpa using hr) ≫ e.inv := by
  rw [pointSplittingPullbackIso_hom_fst]
  apply (cancel_mono e.hom).1
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  apply pullback.hom_ext <;>
    simp [pullback.congrHom, pullback.map, Category.assoc]

@[reassoc] theorem pointSplittingPullbackIso_congrHom_snd
    {X Y Z T Q : Scheme.{u}} (f : X ⟶ Y) (c : Z ⟶ Y) (b : T ⟶ Z)
    (r : T ⟶ Y) (hr : r = b ≫ c)
    (q : Q ⟶ Z) (e : Q ≅ pullback f c)
    (he : e.hom ≫ pullback.snd f c = q) :
    (pullback.congrHom (f₁ := f) (g₁ := r) rfl hr).hom ≫
      (pointSplittingPullbackIso f c b q e he).hom ≫ pullback.snd q b =
      pullback.snd f r := by
  rw [pointSplittingPullbackIso_hom_snd]
  simp [pullback.congrHom, pullback.map]

end PfaffianDescent
