import PfaffianDescent.SerreActualGroundFamilyCoefficientChosenFibreIso
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceSeedFibre
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualMarkedFibreStalk
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualIncidenceMarkedOpen
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualFlatFieldStalk

/-! An actual old marked incidence seed supplies simple stalks in the common
chosen fibre. The canonical-fibre comparison follows from the actual surface
coefficient square, rather than an assumed geometric comparison. -/
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
variable (z : Z ⟶ pullback x q) [IsClosedImmersion z] (b : U ⟶ P)
variable (cfg : Cfg ⟶ S) (marked : Fin 3 → (Cfg ⟶ X))
variable (hm : ∀ i, marked i ≫ x = cfg)
variable (s : U ⟶ serreThreePointSectionIncidence cfg x q marked hm z)
variable (hsp : s ≫ serreThreePointSectionIncidenceToParameters cfg x q marked hm z = b ≫ v)

/-- The actual incidence seed fibre and actual old common fibre have the same
chosen parameter, through the literal canonical universal-zero fibre. -/
def serreActualGroundFamily_oldSeedToCommonFibreIso :
    pullback (serreThreePointSectionIncidenceZeroFamily cfg x q marked hm z) s ≅
      pullback b (pullback.fst n z ≫ pullback.snd y p) :=
  serreIncidenceSeedFamilyFibreIso cfg x q marked hm z s ≪≫
    pullback.congrHom rfl hsp ≪≫
    (serreActualGroundFamily_coefficientChosenFibreIso x y p q k f hY v hv n hnX hnQ z b).symm

/-- The old seed/common comparison preserves the original surface point.
The coefficient-cubic lift is the actual Cartesian lift, so this compatibility
identifies marked points after postcomposing the coefficient morphism. -/
@[reassoc]
theorem serreActualGroundFamily_oldSeedToCommonFibreIso_hom_surface :
    (serreActualGroundFamily_oldSeedToCommonFibreIso x y p q k f hY v hv n hnX hnQ z b
      cfg marked hm s hsp).hom ≫
      pullback.snd b (pullback.fst n z ≫ pullback.snd y p) ≫
        pullback.fst n z ≫ pullback.fst y p ≫ f =
    pullback.fst (serreThreePointSectionIncidenceZeroFamily cfg x q marked hm z) s ≫
      pullback.fst (z ≫ pullback.snd x q)
        (serreThreePointSectionIncidenceToParameters cfg x q marked hm z) ≫
          z ≫ pullback.fst x q := by
  simp only [serreActualGroundFamily_oldSeedToCommonFibreIso, Iso.trans_hom,
    Iso.symm_hom, Category.assoc,
    serreActualGroundFamily_coefficientChosenFibreIso_inv_surface]
  simp only [serreIncidenceSeedFamilyFibreIso, pullback.congrHom, pullback.map, asIso_hom, Category.comp_id,
    Category.assoc, pullback.lift_fst_assoc,
    pullbackLeftPullbackSndIso_hom_fst_assoc]

/-- Only the old marked-three open is used. The rest of the degree-eleven
fibre need not be etale or reduced. -/
theorem serreActualGroundFamily_oldSeed_commonMarked_stalk_isField
    {E : Type u} [Field E]
    (bE : Spec (.of E) ⟶ P)
    (sE : Spec (.of E) ⟶ serreThreePointSectionIncidence cfg x q marked hm z)
    (hspE : sE ≫ serreThreePointSectionIncidenceToParameters cfg x q marked hm z = bE ≫ v)
    (hsE : sE (IsLocalRing.closedPoint E) ∈
      cubicClosedPointSerreFiniteZeroResidual_incidenceMarkedOpen cfg x q marked hm z)
    (i : Fin 3) :
    let g := serreThreePointSectionIncidenceZeroFamily cfg x q marked hm z
    let j := serreIncidenceMarkedZeroSection cfg x q marked hm z i
    let m := cubicClosedPointSerreFiniteZeroResidual_markedFibreSection g j
      (serreIncidenceMarkedZeroSection_toIncidence cfg x q marked hm z i) sE
    IsField ((pullback bE (pullback.fst n z ≫ pullback.snd y p)).presheaf.stalk
      ((serreActualGroundFamily_oldSeedToCommonFibreIso x y p q k f hY v hv n hnX hnQ z bE
        cfg marked hm sE hspE).hom (m (IsLocalRing.closedPoint E)))) := by
  let g := serreThreePointSectionIncidenceZeroFamily cfg x q marked hm z
  let j := serreIncidenceMarkedZeroSection cfg x q marked hm z i
  have hs : sE (IsLocalRing.closedPoint E) ∈
      cubicClosedPointSerreFiniteZeroResidual_markedSectionOpen g j := by
    exact (show cubicClosedPointSerreFiniteZeroResidual_incidenceMarkedOpen cfg x q marked hm z ≤
      cubicClosedPointSerreFiniteZeroResidual_markedSectionOpen g j from iInf_le _ i) hsE
  have hfield := cubicClosedPointSerreFiniteZeroResidual_markedFibreSection_stalk_isField
    g j (serreIncidenceMarkedZeroSection_toIncidence cfg x q marked hm z i) sE
    (IsLocalRing.closedPoint E) hs
  exact cubicClosedPointSerreFiniteZeroResidual_flat_stalk_isField
    (serreActualGroundFamily_oldSeedToCommonFibreIso x y p q k f hY v hv n hnX hnQ z bE
      cfg marked hm sE hspE).hom _ hfield

end PfaffianDescent
