import PfaffianDescent.SerreActualCanonicalMarkedResidualInputs
import PfaffianDescent.SerreActualChosenFibreIncidenceSeed

/-! Construct residual inputs directly from the actual chosen-fibre marked
sections. Incidence seed and marked-surface identities are supplied by the
checked constructor, avoiding a second conversion of its entire native type. -/

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

def serreActualCanonicalMarkedResidualInputsOfChosenSeed
    {F E L : Type u} [Field F] [Field E] [Field L] [Algebra F E]
    {X P Z I : Scheme.{u}}
    (x : X ⟶ Spec (.of F)) (pp : P ⟶ Spec (.of F))
    (zero : Z ⟶ pullback x pp) [IsClosedImmersion zero]
    [IsProper (zero ≫ pullback.snd x pp)]
    (i : I ⟶ X) (j : Spec (.of L) ⟶ X)
    (t : Spec (.of F) ⟶ P) (ht : t ≫ pp = 𝟙 _)
    (tE : Spec (.of E) ⟶ P)
    (htE : tE = Spec.map (CommRingCat.ofHom (algebraMap F E)) ≫ t)
    (δ : Fin 3 → (Spec (.of E) ⟶ pullback (zero ≫ pullback.snd x pp) tE))
    (hδ : ∀ n, δ n ≫ pullback.snd (zero ≫ pullback.snd x pp) tE = 𝟙 _)
    (hW : (serreActualChosenFibre_incidenceSeed x pp zero tE δ hδ)
        (IsLocalRing.closedPoint E) ∈ cubicClosedPointSerreFiniteZeroResidual_goodOpen
      (serreThreePointSectionIncidenceZeroFamily (tE ≫ pp) x pp
        (serreActualChosenFibre_marked x pp zero tE δ)
        (serreActualChosenFibre_marked_toBase x pp zero tE δ hδ) zero))
    (n : Fin 3)
    (hout : (serreActualChosenFibre_marked x pp zero tE δ n)
      (IsLocalRing.closedPoint E) ∉ Set.range i)
    (hpoint : (serreActualChosenFibre_marked x pp zero tE δ n)
      (IsLocalRing.closedPoint E) = j (IsLocalRing.closedPoint L))
    (y : (pullback (zero ≫ pullback.snd x pp)
      (Spec.map (CommRingCat.ofHom (algebraMap F E)) ≫ t) : Scheme))
    (hy : IsField ((pullback (zero ≫ pullback.snd x pp)
      (Spec.map (CommRingCat.ofHom (algebraMap F E)) ≫ t)).presheaf.stalk y))
    (hySurface : (pullback.fst (zero ≫ pullback.snd x pp)
      (Spec.map (CommRingCat.ofHom (algebraMap F E)) ≫ t) ≫ zero ≫
      pullback.fst x pp) y = j (IsLocalRing.closedPoint L)) :
    SerreActualCanonicalMarkedResidualInputs (E := E) (Cfg := Spec (.of E))
      x pp zero i j := by
  let marked := serreActualChosenFibre_marked x pp zero tE δ
  let hm := serreActualChosenFibre_marked_toBase x pp zero tE δ hδ
  let s := serreActualChosenFibre_incidenceSeed x pp zero tE δ hδ
  have hsp : s ≫ serreThreePointSectionIncidenceToParameters (tE ≫ pp) x pp
      marked hm zero = Spec.map (CommRingCat.ofHom (algebraMap F E)) ≫ t :=
    (serreActualChosenFibre_incidenceSeed_toParameters x pp zero tE δ hδ).trans htE
  have hsurface := congrArg (fun f => f (IsLocalRing.closedPoint E))
    (serreActualChosenFibre_incidenceSeed_marked_surface x pp zero tE δ hδ n)
  exact SerreActualCanonicalMarkedResidualInputs.mk
    (tE ≫ pp) marked hm t ht s hW hsp n
    (Eq.mpr (congrArg (fun z => z ∉ Set.range i) hsurface) hout)
    (hsurface.trans hpoint) y hy hySurface

end PfaffianDescent
