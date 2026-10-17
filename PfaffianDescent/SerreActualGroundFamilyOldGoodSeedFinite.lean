import PfaffianDescent.SerreActualGroundFamilyOldMarkedSeed
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualGoodPointFinite

/-! Actual old finite-good incidence seeds give finite common chosen fibres,
using the actual seed/common-fibre comparison. -/
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

/-- Finiteness transfers from the old actual incidence fibre to the literal
common chosen fibre. This uses only the old finite-good open. -/
theorem serreActualGroundFamily_oldSeed_commonFibre_finite
    {E : Type u} [Field E]
    [IsProper (serreThreePointSectionIncidenceZeroFamily cfg x q marked hm z)]
    (bE : Spec (.of E) ⟶ P)
    (sE : Spec (.of E) ⟶ serreThreePointSectionIncidence cfg x q marked hm z)
    (hspE : sE ≫ serreThreePointSectionIncidenceToParameters cfg x q marked hm z = bE ≫ v)
    (hsE : sE (IsLocalRing.closedPoint E) ∈
      cubicClosedPointSerreFiniteZeroResidual_goodOpen
        (serreThreePointSectionIncidenceZeroFamily cfg x q marked hm z)) :
    Finite (pullback bE (pullback.fst n z ≫ pullback.snd y p) : Scheme) := by
  let g := serreThreePointSectionIncidenceZeroFamily cfg x q marked hm z
  letI : Finite (pullback g sE : Scheme) :=
    cubicClosedPointSerreFiniteZeroResidual_goodOpen_fieldPoint_finite g sE hsE
  let e := serreActualGroundFamily_oldSeedToCommonFibreIso
    x y p q k f hY v hv n hnX hnQ z bE cfg marked hm sE hspE
  exact Finite.of_injective e.inv e.inv.injective

end PfaffianDescent
