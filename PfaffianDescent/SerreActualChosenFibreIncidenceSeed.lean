import PfaffianDescent.VoisinDegreeElevenSerreIncidenceSeedFactor

/-! Three actual sections of a canonical chosen zero fibre give a new
incidence seed, with its configuration and selected parameter derived. -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

variable {S X P Z T : Scheme.{u}}
variable (x : X ⟶ S) (p : P ⟶ S)
variable (zero : Z ⟶ pullback x p) [IsClosedImmersion zero]
variable (t : T ⟶ P)
variable (δ : Fin 3 → (T ⟶ pullback (zero ≫ pullback.snd x p) t))
variable (hδ : ∀ i, δ i ≫ pullback.snd (zero ≫ pullback.snd x p) t = 𝟙 T)

def serreActualChosenFibre_marked (i : Fin 3) : T ⟶ X :=
  δ i ≫ pullback.fst (zero ≫ pullback.snd x p) t ≫ zero ≫ pullback.fst x p

include hδ in
theorem serreActualChosenFibre_marked_toBase (i : Fin 3) :
    serreActualChosenFibre_marked x p zero t δ i ≫ x = t ≫ p := by
  simp only [serreActualChosenFibre_marked, Category.assoc]
  calc
    _ = δ i ≫ pullback.fst (zero ≫ pullback.snd x p) t ≫
        zero ≫ pullback.snd x p ≫ p := by rw [pullback.condition]
    _ = (δ i ≫ pullback.snd (zero ≫ pullback.snd x p) t) ≫ t ≫ p := by
      simpa only [Category.assoc] using congrArg (fun f => δ i ≫ f ≫ p)
        (pullback.condition (f := zero ≫ pullback.snd x p) (g := t))
    _ = t ≫ p := by rw [hδ i, Category.id_comp]

/-- Every marked morphism is defined from an actual vanishing section, so the
incidence factorization is constructed internally by the closed universal
zero equations. -/
def serreActualChosenFibre_incidenceSeed :
    T ⟶ serreThreePointSectionIncidence (t ≫ p) x p
      (serreActualChosenFibre_marked x p zero t δ)
      (serreActualChosenFibre_marked_toBase x p zero t δ hδ) zero := by
  let a : T ⟶ pullback (t ≫ p) p :=
    pullback.lift (𝟙 T) t (by simp only [Category.id_comp])
  let l : Fin 3 → (T ⟶ Z) := fun i => δ i ≫ pullback.fst (zero ≫ pullback.snd x p) t
  have hl : ∀ i, l i ≫ zero = a ≫ fixedLinearSystemIncidenceMap (t ≫ p) x p
      (serreActualChosenFibre_marked x p zero t δ)
      (serreActualChosenFibre_marked_toBase x p zero t δ hδ) i := by
    intro i
    apply pullback.hom_ext
    · simp only [l, a, Category.assoc, fixedLinearSystemIncidenceMap_fst,
        pullback.lift_fst_assoc, Category.id_comp, serreActualChosenFibre_marked]
    · simp only [l, a, Category.assoc, fixedLinearSystemIncidenceMap_snd,
        pullback.lift_snd]
      calc
        _ = (δ i ≫ pullback.snd (zero ≫ pullback.snd x p) t) ≫ t := by
          simpa only [Category.assoc] using congrArg (fun f => δ i ≫ f)
            (pullback.condition (f := zero ≫ pullback.snd x p) (g := t))
        _ = t := by rw [hδ i, Category.id_comp]
  exact serreIncidenceSeed (t ≫ p) x p
    (serreActualChosenFibre_marked x p zero t δ)
    (serreActualChosenFibre_marked_toBase x p zero t δ hδ) zero a l hl

@[reassoc]
theorem serreActualChosenFibre_incidenceSeed_toParameters :
    serreActualChosenFibre_incidenceSeed x p zero t δ hδ ≫
      serreThreePointSectionIncidenceToParameters (t ≫ p) x p
        (serreActualChosenFibre_marked x p zero t δ)
        (serreActualChosenFibre_marked_toBase x p zero t δ hδ) zero = t := by
  simp only [serreActualChosenFibre_incidenceSeed,
    serreIncidenceSeed_toParameters, pullback.lift_snd]

@[reassoc]
theorem serreActualChosenFibre_incidenceSeed_toConfiguration :
    serreActualChosenFibre_incidenceSeed x p zero t δ hδ ≫
      serreThreePointSectionIncidenceToConfiguration (t ≫ p) x p
        (serreActualChosenFibre_marked x p zero t δ)
        (serreActualChosenFibre_marked_toBase x p zero t δ hδ) zero = 𝟙 T := by
  simp only [serreActualChosenFibre_incidenceSeed,
    serreIncidenceSeed_toConfiguration, pullback.lift_fst]

@[reassoc]
theorem serreActualChosenFibre_incidenceSeed_marked_surface (i : Fin 3) :
    serreActualChosenFibre_incidenceSeed x p zero t δ hδ ≫
      serreThreePointSectionIncidenceToConfiguration (t ≫ p) x p
        (serreActualChosenFibre_marked x p zero t δ)
        (serreActualChosenFibre_marked_toBase x p zero t δ hδ) zero ≫
      serreActualChosenFibre_marked x p zero t δ i =
    δ i ≫ pullback.fst (zero ≫ pullback.snd x p) t ≫ zero ≫ pullback.fst x p := by
  rw [← Category.assoc, serreActualChosenFibre_incidenceSeed_toConfiguration,
    Category.id_comp]
  rfl

end PfaffianDescent
