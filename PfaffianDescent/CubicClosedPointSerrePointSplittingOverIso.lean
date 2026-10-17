import PfaffianDescent.CubicClosedPointSerrePointSplittingPullback

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

def pointSplittingPullbackOverIso {D Q S T : Scheme.{u}}
    (q : D ⟶ S) (q' : Q ⟶ S) (b : T ⟶ S) (e : Q ≅ D)
    (he : e.inv ≫ q' = q) : pullback q b ≅ pullback q' b := by
  have h : IsPullback (pullback.fst q b ≫ e.inv) (pullback.snd q b) q' b := by
    apply (IsPullback.of_hasPullback q b).of_iso
      (Iso.refl _) e.symm (Iso.refl _) (Iso.refl _)
    · simp
    · simp
    · simpa using he.symm
    · simp
  exact h.isoPullback

@[reassoc] theorem pointSplittingPullbackOverIso_hom_fst {D Q S T : Scheme.{u}}
    (q : D ⟶ S) (q' : Q ⟶ S) (b : T ⟶ S) (e : Q ≅ D)
    (he : e.inv ≫ q' = q) :
    (pointSplittingPullbackOverIso q q' b e he).hom ≫ pullback.fst q' b =
      pullback.fst q b ≫ e.inv := by
  exact IsPullback.isoPullback_hom_fst _

@[reassoc] theorem pointSplittingPullbackOverIso_hom_snd {D Q S T : Scheme.{u}}
    (q : D ⟶ S) (q' : Q ⟶ S) (b : T ⟶ S) (e : Q ≅ D)
    (he : e.inv ≫ q' = q) :
    (pointSplittingPullbackOverIso q q' b e he).hom ≫ pullback.snd q' b =
      pullback.snd q b := by
  exact IsPullback.isoPullback_hom_snd _

end PfaffianDescent
