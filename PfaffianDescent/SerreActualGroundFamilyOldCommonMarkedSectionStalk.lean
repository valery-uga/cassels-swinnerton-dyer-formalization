import PfaffianDescent.SerreActualGroundFamilyOldMarkedSections

/-! Field stalks at the literal common marked sections of the actual old seed. -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

variable {S R X Y P Q Z U Cfg : Scheme.{u}}
variable (x : X ⟶ S) (y : Y ⟶ R) (p : P ⟶ R) (q : Q ⟶ S)
variable (k : R ⟶ S) (f : Y ⟶ X) (hY : IsPullback f y x k)
variable (v : P ⟶ Q) (hv : v ≫ q = p ≫ k)
variable (n : pullback y p ⟶ pullback x q)
variable (hnX : n ≫ pullback.fst x q = pullback.fst y p ≫ f)
variable (hnQ : n ≫ pullback.snd x q = pullback.snd y p ≫ v)
variable (z : Z ⟶ pullback x q) [IsClosedImmersion z] 
variable (cfg : Cfg ⟶ S) (marked : Fin 3 → (Cfg ⟶ X))
variable (hm : ∀ i, marked i ≫ x = cfg)

include hY hv hnX hnQ

theorem serreActualGroundFamily_oldSeed_commonMarkedSection_stalk_isField
    {E : Type u} [Field E]
    (bE : Spec (.of E) ⟶ P)
    (sE : Spec (.of E) ⟶ serreThreePointSectionIncidence cfg x q marked hm z)
    (hspE : sE ≫ serreThreePointSectionIncidenceToParameters cfg x q marked hm z = bE ≫ v)
    (hsE : sE (IsLocalRing.closedPoint E) ∈
      cubicClosedPointSerreFiniteZeroResidual_incidenceMarkedOpen cfg x q marked hm z)
    (i : Fin 3) :
    IsField ((pullback bE (pullback.fst n z ≫ pullback.snd y p)).presheaf.stalk
      ((serreActualGroundFamily_oldSeed_commonMarkedSection
        x y p q k f hY v hv n hnX hnQ z bE cfg marked hm sE hspE i)
        (IsLocalRing.closedPoint E))) := by
  unfold serreActualGroundFamily_oldSeed_commonMarkedSection
  rw [Scheme.Hom.comp_apply]
  exact serreActualGroundFamily_oldSeed_commonMarked_stalk_isField
    x y p q k f hY v hv n hnX hnQ z cfg marked hm bE sE hspE hsE i

end PfaffianDescent
