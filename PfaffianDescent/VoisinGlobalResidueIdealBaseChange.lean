import PfaffianDescent.ProjectiveQuotientGlobalIdealBaseChange
import PfaffianDescent.VoisinResiduePrincipalIdealSheafBaseChange

/-!
# Global ideal base change for Voisin's residue-regular intersection

Residue-field regularity of the added homogeneous equation supplies
regular-principal and relative-flatness hypotheses on every standard
chart. The canonical ideal-module map for the resulting global
projective closed immersion is therefore an isomorphism after every
coefficient-ring map, including nonflat maps.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem isIso_residueRegularHypersurfaceGlobalIdealBaseChange_any
    {T S : Type u} [CommRing T] [IsLocalRing T] [CommRing S]
    (f : T →+* S)
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) T))
    [Module.Flat T (CoordinateRing J)]
    (C₀ : HomogeneousIdeal
      (homogeneousSubmodule (Fin 4) (IsLocalRing.ResidueField T)))
    (hJC₀ : J.toIdeal.map
      (MvPolynomial.map (algebraMap T (IsLocalRing.ResidueField T))) = C₀.toIdeal)
    (p : MvPolynomial (Fin 4) T) {d : ℕ} (hp : p.IsHomogeneous d)
    (hreg : IsRegular
      (homogeneousCoefficientSection J C₀ hJC₀
        (polynomialClassInGrading J p hp) : CoordinateRing C₀)) :
    let Q := J ⊔ equationIdeal p hp
    let hJQ : J.toIdeal ≤ Q.toIdeal := by
      rw [HomogeneousIdeal.toIdeal_sup]
      exact le_sup_left
    let cJ := projectiveCoefficientMap f J (coefficientChangedHomogeneousIdeal f J)
      (coefficientChangedHomogeneousIdeal_toIdeal f J)
    let q := schemeQuotientMap J Q hJQ
    letI : IsClosedImmersion q := schemeQuotientMap_closedImmersion J Q hJQ
    IsIso (closedImmersionIdealBaseChangeHom cJ q) := by
  let Q := J ⊔ equationIdeal p hp
  let hJQ : J.toIdeal ≤ Q.toIdeal := by
    rw [HomogeneousIdeal.toIdeal_sup]
    exact le_sup_left
  let q := schemeQuotientMap J Q hJQ
  letI : IsClosedImmersion q := schemeQuotientMap_closedImmersion J Q hJQ
  have H : HasRegularPrincipalStandardCharts J Q hJQ := by
    intro j
    let x : ChartRing J j :=
      p.eval₂ (chartBaseMap J j) (chartCoordinate J j)
    refine ⟨x, ?_, ?_⟩
    · change IsRegular (p.eval₂ (chartBaseMap J j) (chartCoordinate J j))
      rw [eval₂_chartCoordinate_eq_fraction J j p hp]
      exact chartSection_regular_of_residue_regular J C₀ hJC₀
        (polynomialClassInGrading J p hp) hreg j
    · exact chartQuotientMap_ker_eq_equation J p hp j
  have hflat : ∀ j : Fin 4,
      ((chartQuotientMap J Q hJQ j).comp (chartBaseMap J j)).Flat := by
    intro j
    exact flat_hypersurfaceIntersectionChart_of_residue_regular
      J C₀ hJC₀ p hp hreg j
  exact H.isIso_globalIdealBaseChange f J Q hJQ hflat

end PfaffianDescent
