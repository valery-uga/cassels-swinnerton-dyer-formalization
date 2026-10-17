import PfaffianDescent.SerreActualChosenFibreIncidenceSeed
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualGoodPointFinite
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceSeedFibre

/-! Actual chosen-fibre finiteness places the constructed incidence seed in
the finite-fibre open. No relative marked-point open is required. -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem serreActualChosenFibre_incidenceSeed_mem_goodOpen
    {E : Type u} [Field E] {S X P Z : Scheme.{u}}
    (x : X ⟶ S) (p : P ⟶ S)
    (zero : Z ⟶ pullback x p) [IsClosedImmersion zero]
    [IsProper (zero ≫ pullback.snd x p)]
    (t : Spec (.of E) ⟶ P)
    (δ : Fin 3 → (Spec (.of E) ⟶ pullback (zero ≫ pullback.snd x p) t))
    (hδ : ∀ i, δ i ≫ pullback.snd (zero ≫ pullback.snd x p) t = 𝟙 _)
    [IsFinite (pullback.snd (zero ≫ pullback.snd x p) t)] :
    (serreActualChosenFibre_incidenceSeed x p zero t δ hδ) (IsLocalRing.closedPoint E) ∈
      cubicClosedPointSerreFiniteZeroResidual_goodOpen
        (serreThreePointSectionIncidenceZeroFamily (t ≫ p) x p
          (serreActualChosenFibre_marked x p zero t δ)
          (serreActualChosenFibre_marked_toBase x p zero t δ hδ) zero) := by
  let marked := serreActualChosenFibre_marked x p zero t δ
  let hm := serreActualChosenFibre_marked_toBase x p zero t δ hδ
  let s := serreActualChosenFibre_incidenceSeed x p zero t δ hδ
  let g := serreThreePointSectionIncidenceZeroFamily (t ≫ p) x p marked hm zero
  let e := serreIncidenceSeedFamilyFibreIso (t ≫ p) x p marked hm zero s ≪≫
    pullback.congrHom rfl (serreActualChosenFibre_incidenceSeed_toParameters x p zero t δ hδ)
  letI : Finite (pullback (zero ≫ pullback.snd x p) t : Scheme) :=
    cubicClosedPointSerreFiniteZeroResidual_finiteToField_finite
      (pullback.snd (zero ≫ pullback.snd x p) t)
  letI : Finite (pullback g s : Scheme) := Finite.of_injective e.hom e.hom.injective
  have hr : Set.range s = {s (IsLocalRing.closedPoint E)} := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      exact congrArg s (Subsingleton.elim z (IsLocalRing.closedPoint E))
    · intro hy
      exact ⟨IsLocalRing.closedPoint E, hy.symm⟩
  have hf : (Set.range (pullback.fst g s)).Finite := Set.finite_range _
  rw [Scheme.Pullback.range_fst, hr] at hf
  exact cubicClosedPointSerreFiniteZeroResidual_mem_goodOpen_of_finite_fibre
    g (s (IsLocalRing.closedPoint E)) hf

end PfaffianDescent
