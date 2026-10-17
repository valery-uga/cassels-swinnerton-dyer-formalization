import PfaffianDescent.SerreActualCanonicalMarkedResidualInputsOfChosenSeed

/-! Actual chosen marked geometry, independent of the finite-good calculation.
The native constructor derives every field from the same old selected seed. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

structure SerreActualChosenMarkedResidualGeometry
    {F E L : Type u} [Field F] [Field E] [Field L] [Algebra F E]
    {X P Z I : Scheme.{u}}
    (x : X ⟶ Spec (.of F)) (pp : P ⟶ Spec (.of F))
    (zero : Z ⟶ pullback x pp)
    (i : I ⟶ X) (j : Spec (.of L) ⟶ X)
    (tE : Spec (.of E) ⟶ P) where
  t : Spec (.of F) ⟶ P
  ht : t ≫ pp = 𝟙 _
  htE : tE = Spec.map (CommRingCat.ofHom (algebraMap F E)) ≫ t
  δ : Fin 3 → (Spec (.of E) ⟶ pullback (zero ≫ pullback.snd x pp) tE)
  hδ : ∀ n, δ n ≫ pullback.snd (zero ≫ pullback.snd x pp) tE = 𝟙 _
  n : Fin 3
  hout : (serreActualChosenFibre_marked x pp zero tE δ n)
    (IsLocalRing.closedPoint E) ∉ Set.range i
  hpoint : (serreActualChosenFibre_marked x pp zero tE δ n)
    (IsLocalRing.closedPoint E) = j (IsLocalRing.closedPoint L)
  y : (pullback (zero ≫ pullback.snd x pp)
    (Spec.map (CommRingCat.ofHom (algebraMap F E)) ≫ t) : Scheme)
  hy : IsField ((pullback (zero ≫ pullback.snd x pp)
    (Spec.map (CommRingCat.ofHom (algebraMap F E)) ≫ t)).presheaf.stalk y)
  hySurface : (pullback.fst (zero ≫ pullback.snd x pp)
    (Spec.map (CommRingCat.ofHom (algebraMap F E)) ≫ t) ≫ zero ≫
    pullback.fst x pp) y = j (IsLocalRing.closedPoint L)

end PfaffianDescent
