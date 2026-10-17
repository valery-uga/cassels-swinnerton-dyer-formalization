import PfaffianDescent.SerreActualGroundFamilyChosenMarkedSeed

/-! The literal transported section preserves its actual old surface image. -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem serreActualGroundFamily_literalMarked_surface_original
    {S X P Q Z Y W U V : Scheme.{u}}
    (x : X ⟶ S) (p : P ⟶ S) (q : Q ⟶ S)
    (v : P ⟶ Q) (hv : v ≫ q = p)
    (n : pullback x p ⟶ pullback x q)
    (hnX : n ≫ pullback.fst x q = pullback.fst x p)
    (hnQ : n ≫ pullback.snd x q = pullback.snd x p ≫ v)
    (z : Z ⟶ pullback x q) [IsClosedImmersion z]
    (o : pullback x p ⟶ Y) (w : W ⟶ Y) [IsClosedImmersion w]
    (h : z.ker.comap n = w.ker.comap o) (b : U ⟶ P)
    (m : Fin 3 → (U ⟶ pullback b (pullback.fst o w ≫ pullback.snd x p)))
    (f : X ⟶ V) (i : Fin 3) (old : U ⟶ V)
    (hold : m i ≫ pullback.snd b (pullback.fst o w ≫ pullback.snd x p) ≫
      pullback.fst o w ≫ pullback.fst x p ≫ f = old) :
    serreActualChosenFibre_marked x q z (b ≫ v)
      (serreActualGroundFamily_transportedChosenMarked x p q v hv n hnX hnQ z o w h b m)
      i ≫ f = old := by
  simp only [serreActualChosenFibre_marked, serreActualGroundFamily_transportedChosenMarked,
    Category.assoc, serreActualGroundFamily_oldToCanonicalChosenFibreIso_hom_surface_assoc]
  exact hold

end PfaffianDescent
