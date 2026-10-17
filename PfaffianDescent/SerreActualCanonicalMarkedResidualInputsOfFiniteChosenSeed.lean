import PfaffianDescent.SerreActualCanonicalMarkedResidualInputsOfChosenSeed
import PfaffianDescent.SerreActualChosenFibreGoodIncidenceSeed
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-! Actual finite support of a chosen fibre supplies its good incidence seed
and complete marked residual record internally. The native caller derives this
finiteness from the same old good seed before specializing this generic bridge. -/

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

def serreActualCanonicalMarkedResidualInputsOfFiniteChosenSeed
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
    [Finite (pullback (zero ≫ pullback.snd x pp) tE : Scheme.{u})]
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
  letI : LocallyQuasiFinite (pullback.snd (zero ≫ pullback.snd x pp) tE) :=
    LocallyQuasiFinite.of_finite_preimage_singleton _ (fun _ => Set.toFinite _)
  letI : IsFinite (pullback.snd (zero ≫ pullback.snd x pp) tE) :=
    IsFinite.of_isProper_of_locallyQuasiFinite _
  exact serreActualCanonicalMarkedResidualInputsOfChosenSeed x pp zero i j
    t ht tE htE δ hδ
    (serreActualChosenFibre_incidenceSeed_mem_goodOpen x pp zero tE δ hδ)
    n hout hpoint y hy hySurface

end PfaffianDescent
