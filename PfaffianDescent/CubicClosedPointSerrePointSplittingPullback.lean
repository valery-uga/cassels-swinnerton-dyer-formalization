import AllCharacteristics.ProjectiveConfigurationGenericSplitFiber

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

/-- Base change of an actual scheme identified with a fiber, preserving both
literal projections. No coefficient fields are identified. -/
def pointSplittingPullbackIso {X Y Z T Q : Scheme.{u}}
    (f : X ⟶ Y) (c : Z ⟶ Y) (b : T ⟶ Z)
    (q : Q ⟶ Z) (e : Q ≅ pullback f c)
    (he : e.hom ≫ pullback.snd f c = q) :
    pullback f (b ≫ c) ≅ pullback q b where
  hom := pullback.lift
    ((pullbackLeftPullbackSndIso f c b).inv ≫ pullback.fst (pullback.snd f c) b ≫ e.inv)
    (pullback.snd f (b ≫ c)) (by
      rw [Category.assoc, Category.assoc, ← he, Iso.inv_hom_id_assoc]
      exact pullbackLeftPullbackSndIso_inv_fst_snd f c b)
  inv := pullback.lift (pullback.fst q b ≫ e.hom ≫ pullback.fst f c)
    (pullback.snd q b) (by
      rw [Category.assoc, Category.assoc, pullback.condition,
        ← Category.assoc e.hom, he]
      simpa only [Category.assoc] using congrArg (fun t => t ≫ c)
        (pullback.condition (f := q) (g := b)))
  hom_inv_id := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst_assoc, pullback.lift_fst, pullback.lift_snd_assoc, pullback.lift_snd,
        Iso.inv_hom_id_assoc, Category.id_comp]
      exact pullbackLeftPullbackSndIso_inv_fst f c b
    · simp
  inv_hom_id := by
    apply pullback.hom_ext
    · apply (cancel_mono e.hom).1
      apply pullback.hom_ext
      · simp only [Category.assoc, pullback.lift_fst_assoc, pullback.lift_fst, pullback.lift_snd_assoc, pullback.lift_snd,
          Iso.inv_hom_id_assoc, Category.id_comp]
        rw [pullbackLeftPullbackSndIso_inv_fst]
        exact pullback.lift_fst _ _ _
      · simp only [Category.assoc, pullback.lift_fst_assoc, pullback.lift_fst, pullback.lift_snd_assoc, pullback.lift_snd,
          Iso.inv_hom_id_assoc, Category.id_comp]
        rw [pullbackLeftPullbackSndIso_inv_fst_snd]
        simp only [pullback.lift_snd_assoc]
        rw [he, pullback.condition]
    · simp

@[reassoc] theorem pointSplittingPullbackIso_hom_snd
    {X Y Z T Q : Scheme.{u}} (f : X ⟶ Y) (c : Z ⟶ Y) (b : T ⟶ Z)
    (q : Q ⟶ Z) (e : Q ≅ pullback f c)
    (he : e.hom ≫ pullback.snd f c = q) :
    (pointSplittingPullbackIso f c b q e he).hom ≫ pullback.snd q b =
      pullback.snd f (b ≫ c) := by
  exact pullback.lift_snd _ _ _

end PfaffianDescent
