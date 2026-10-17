import PfaffianDescent.SerreActualGroundFamilyChosenFibreIso
import PfaffianDescent.SerreActualClosedPullbackZeroMarkedFibre
import PfaffianDescent.SerreActualChosenFibreIncidenceSeed

/-! Transport three old marked sections to the literal canonical new chosen
fibre, then construct the new incidence seed with the unchanged parameter. -/
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

def serreActualGroundFamily_oldToCanonicalChosenFibreIso :
    pullback b (pullback.fst o w ≫ pullback.snd x p) ≅
      pullback (z ≫ pullback.snd x q) (b ≫ v) :=
  (serreActualClosedPullbackZero_parameterChangeIso z w n o h (pullback.snd x p) b).symm ≪≫
    serreActualGroundFamily_chosenFibreIso x p q v hv n hnX hnQ z b

@[reassoc]
theorem serreActualGroundFamily_oldToCanonicalChosenFibreIso_hom_parameter :
    (serreActualGroundFamily_oldToCanonicalChosenFibreIso x p q v hv n hnX hnQ z o w h b).hom ≫
      pullback.snd (z ≫ pullback.snd x q) (b ≫ v) =
    pullback.fst b (pullback.fst o w ≫ pullback.snd x p) := by
  simp only [serreActualGroundFamily_oldToCanonicalChosenFibreIso,
    Iso.trans_hom, Iso.symm_hom, Category.assoc,
    serreActualGroundFamily_chosenFibreIso_hom_parameter,
    serreActualClosedPullbackZero_parameterChangeIso_inv_fst]

@[reassoc]
theorem serreActualGroundFamily_oldToCanonicalChosenFibreIso_hom_surface :
    (serreActualGroundFamily_oldToCanonicalChosenFibreIso x p q v hv n hnX hnQ z o w h b).hom ≫
      pullback.fst (z ≫ pullback.snd x q) (b ≫ v) ≫ z ≫ pullback.fst x q =
    pullback.snd b (pullback.fst o w ≫ pullback.snd x p) ≫
      pullback.fst o w ≫ pullback.fst x p := by
  simp only [serreActualGroundFamily_oldToCanonicalChosenFibreIso,
    Iso.trans_hom, Iso.symm_hom, Category.assoc,
    serreActualGroundFamily_chosenFibreIso_hom_surface,
    serreActualClosedPullbackZero_parameterChangeIso_inv_ambient_assoc]

variable (m : Fin 3 → (U ⟶ pullback b (pullback.fst o w ≫ pullback.snd x p)))
variable (hm : ∀ i, m i ≫ pullback.fst b (pullback.fst o w ≫ pullback.snd x p) = 𝟙 U)

def serreActualGroundFamily_transportedChosenMarked (i : Fin 3) :
    U ⟶ pullback (z ≫ pullback.snd x q) (b ≫ v) :=
  m i ≫ (serreActualGroundFamily_oldToCanonicalChosenFibreIso x p q v hv n hnX hnQ z o w h b).hom

include hm in
theorem serreActualGroundFamily_transportedChosenMarked_toParameter (i : Fin 3) :
    serreActualGroundFamily_transportedChosenMarked x p q v hv n hnX hnQ z o w h b m i ≫
      pullback.snd (z ≫ pullback.snd x q) (b ≫ v) = 𝟙 U := by
  simp only [serreActualGroundFamily_transportedChosenMarked, Category.assoc,
    serreActualGroundFamily_oldToCanonicalChosenFibreIso_hom_parameter, hm i]

/-- All three vanishing lifts and their chosen-parameter compatibility are
constructed by transport; no new incidence-open premise is introduced. -/
def serreActualGroundFamily_chosenMarkedSeed :=
  serreActualChosenFibre_incidenceSeed x q z (b ≫ v)
    (serreActualGroundFamily_transportedChosenMarked x p q v hv n hnX hnQ z o w h b m)
    (serreActualGroundFamily_transportedChosenMarked_toParameter x p q v hv n hnX hnQ z o w h b m hm)

@[irreducible]
def serreActualGroundFamily_chosenMarkedSeed_toParameters :=
  serreActualChosenFibre_incidenceSeed_toParameters x q z (b ≫ v)
    (serreActualGroundFamily_transportedChosenMarked x p q v hv n hnX hnQ z o w h b m)
    (serreActualGroundFamily_transportedChosenMarked_toParameter x p q v hv n hnX hnQ z o w h b m hm)

@[irreducible]
def serreActualGroundFamily_chosenMarkedSeed_surface :=
  serreActualChosenFibre_incidenceSeed_marked_surface x q z (b ≫ v)
    (serreActualGroundFamily_transportedChosenMarked x p q v hv n hnX hnQ z o w h b m)
    (serreActualGroundFamily_transportedChosenMarked_toParameter x p q v hv n hnX hnQ z o w h b m hm)

/-- The new incidence seed contains the same actual marked surface points as
its old common-fibre sections, via the native zero-family comparison. -/
theorem serreActualGroundFamily_chosenMarkedSeed_surface_fromOld (i : Fin 3) :
    serreActualGroundFamily_chosenMarkedSeed x p q v hv n hnX hnQ z o w h b m hm ≫
      serreThreePointSectionIncidenceToConfiguration ((b ≫ v) ≫ q) x q
        (serreActualChosenFibre_marked x q z (b ≫ v)
          (serreActualGroundFamily_transportedChosenMarked x p q v hv n hnX hnQ z o w h b m))
        (serreActualChosenFibre_marked_toBase x q z (b ≫ v)
          (serreActualGroundFamily_transportedChosenMarked x p q v hv n hnX hnQ z o w h b m)
          (serreActualGroundFamily_transportedChosenMarked_toParameter x p q v hv n hnX hnQ z o w h b m hm)) z ≫
      serreActualChosenFibre_marked x q z (b ≫ v)
        (serreActualGroundFamily_transportedChosenMarked x p q v hv n hnX hnQ z o w h b m) i =
    m i ≫ pullback.snd b (pullback.fst o w ≫ pullback.snd x p) ≫
      pullback.fst o w ≫ pullback.fst x p := by
  rw [serreActualGroundFamily_chosenMarkedSeed]
  rw [serreActualChosenFibre_incidenceSeed_marked_surface]
  simp only [serreActualGroundFamily_transportedChosenMarked, Category.assoc,
    serreActualGroundFamily_oldToCanonicalChosenFibreIso_hom_surface]

end PfaffianDescent
