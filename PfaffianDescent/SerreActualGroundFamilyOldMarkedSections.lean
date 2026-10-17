import PfaffianDescent.SerreActualGroundFamilyOldMarkedSeed

/-! Actual old incidence marked sections give three sections of the old
common chosen fibre, preserving the selected point base internally. -/
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

@[reassoc]
theorem serreActualGroundFamily_oldSeedToCommonFibreIso_hom_parameter :
    (serreActualGroundFamily_oldSeedToCommonFibreIso x y p q k f hY v hv n hnX hnQ z b
      cfg marked hm s hsp).hom ≫ pullback.fst b (pullback.fst n z ≫ pullback.snd y p) =
    pullback.snd (serreThreePointSectionIncidenceZeroFamily cfg x q marked hm z) s := by
  have hInv :
      (serreActualGroundFamily_coefficientChosenFibreIso x y p q k f hY v hv n hnX hnQ z b).inv ≫
        pullback.fst b (pullback.fst n z ≫ pullback.snd y p) =
      pullback.snd (z ≫ pullback.snd x q) (b ≫ v) := by
    rw [← serreActualGroundFamily_coefficientChosenFibreIso_hom_parameter
        x y p q k f hY v hv n hnX hnQ z b,
      ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  simp only [serreActualGroundFamily_oldSeedToCommonFibreIso, Iso.trans_hom,
    Iso.symm_hom, Category.assoc, hInv]
  simp only [serreIncidenceSeedFamilyFibreIso, pullback.congrHom, pullback.map, asIso_hom, Category.comp_id,
    Category.assoc, pullback.lift_snd, pullbackLeftPullbackSndIso_hom_snd]

/-- The three sections are the actual incidence-marked lifts, followed by the
actual old common-fibre identification; no vanishing certificate is supplied. -/
def serreActualGroundFamily_oldSeed_commonMarkedSection (i : Fin 3) :
    U ⟶ pullback b (pullback.fst n z ≫ pullback.snd y p) :=
  cubicClosedPointSerreFiniteZeroResidual_markedFibreSection
    (serreThreePointSectionIncidenceZeroFamily cfg x q marked hm z)
    (serreIncidenceMarkedZeroSection cfg x q marked hm z i)
    (serreIncidenceMarkedZeroSection_toIncidence cfg x q marked hm z i) s ≫
    (serreActualGroundFamily_oldSeedToCommonFibreIso x y p q k f hY v hv n hnX hnQ z b
      cfg marked hm s hsp).hom

theorem serreActualGroundFamily_oldSeed_commonMarkedSection_toParameter (i : Fin 3) :
    serreActualGroundFamily_oldSeed_commonMarkedSection x y p q k f hY v hv n hnX hnQ z b
      cfg marked hm s hsp i ≫ pullback.fst b (pullback.fst n z ≫ pullback.snd y p) = 𝟙 U := by
  simp only [serreActualGroundFamily_oldSeed_commonMarkedSection, Category.assoc,
    serreActualGroundFamily_oldSeedToCommonFibreIso_hom_parameter,
    cubicClosedPointSerreFiniteZeroResidual_markedFibreSection, pullback.lift_snd]

/-- After the genuine surface coefficient map, the transported marked section
is the original marked morphism selected by the old incidence seed. -/
@[reassoc]
theorem serreActualGroundFamily_oldSeed_commonMarkedSection_surface (i : Fin 3) :
    serreActualGroundFamily_oldSeed_commonMarkedSection x y p q k f hY v hv n hnX hnQ z b
      cfg marked hm s hsp i ≫
      pullback.snd b (pullback.fst n z ≫ pullback.snd y p) ≫
        pullback.fst n z ≫ pullback.fst y p ≫ f =
    s ≫ serreThreePointSectionIncidenceToConfiguration cfg x q marked hm z ≫ marked i := by
  simp only [serreActualGroundFamily_oldSeed_commonMarkedSection, Category.assoc,
    serreActualGroundFamily_oldSeedToCommonFibreIso_hom_surface,
    cubicClosedPointSerreFiniteZeroResidual_markedFibreSection, pullback.lift_fst_assoc,
    serreIncidenceMarkedZeroSection]
  simp only [Category.assoc, pullback.lift_fst_assoc,
    serreIncidenceMarkedToUniversalZero_comp_assoc, fixedLinearSystemIncidenceMap_fst]

end PfaffianDescent
