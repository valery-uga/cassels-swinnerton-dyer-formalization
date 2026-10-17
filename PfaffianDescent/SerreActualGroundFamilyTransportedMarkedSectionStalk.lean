import PfaffianDescent.SerreActualGroundFamilyChosenMarkedSeed

/-! Pointwise field stalks at the literal transported sections used by the
actual chosen-incidence constructor. -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

variable {S X P Q Z Y W U : Scheme.{u}}
variable (x : X ⟶ S) (p : P ⟶ S) (q : Q ⟶ S)
variable (v : P ⟶ Q) (hv : v ≫ q = p)
variable (n : pullback x p ⟶ pullback x q)
variable (hnX : n ≫ pullback.fst x q = pullback.fst x p)
variable (hnQ : n ≫ pullback.snd x q = pullback.snd x p ≫ v)
variable (z : Z ⟶ pullback x q) [IsClosedImmersion z]
variable (o : pullback x p ⟶ Y) (w : W ⟶ Y) [IsClosedImmersion w]
variable (h : z.ker.comap n = w.ker.comap o) (b : U ⟶ P)

variable (m : Fin 3 → (U ⟶ pullback b (pullback.fst o w ≫ pullback.snd x p)))
theorem serreActualGroundFamily_transportedChosenMarked_stalk_isField
    (i : Fin 3) (t : U)
    (hf : IsField ((pullback b (pullback.fst o w ≫ pullback.snd x p)).presheaf.stalk
      (m i t))) :
    IsField ((pullback (z ≫ pullback.snd x q) (b ≫ v)).presheaf.stalk
      ((serreActualGroundFamily_transportedChosenMarked
        x p q v hv n hnX hnQ z o w h b m i) t)) := by
  rw [serreActualGroundFamily_transportedChosenMarked, Scheme.Hom.comp_apply]
  exact serreActualChosenFibreIso_stalk_isField
    (serreActualGroundFamily_oldToCanonicalChosenFibreIso x p q v hv n hnX hnQ z o w h b)
    (m i t) hf

end PfaffianDescent
