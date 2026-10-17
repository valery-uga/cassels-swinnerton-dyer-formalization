import PfaffianDescent.VoisinGlobalResidueIdealBaseChange
import PfaffianDescent.VoisinFixedCubicCoordinateFlat

/-!
# Global ideal base change on a fixed cubic over a local ring

Field-to-ring base change makes the fixed cubic's homogeneous
coordinate ring flat over every local coefficient ring. Regularity of
the reduced moving equation then gives the global canonical ideal
comparison for every further coefficient map.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem isIso_fixedCubicGlobalIdealBaseChange_any
    {K T S : Type u} [Field K] [CommRing T] [Algebra K T]
    [IsLocalRing T] [CommRing S]
    (f : T →+* S)
    (a : MvPolynomial (Fin 4) K) (ha : a.IsHomogeneous 3)
    (p : MvPolynomial (Fin 4) T) {d : ℕ} (hp : p.IsHomogeneous d)
    (hreg : IsRegular (Ideal.Quotient.mk
      (equationIdeal (a.map (algebraMap K (IsLocalRing.ResidueField T)))
        (ha.map (algebraMap K (IsLocalRing.ResidueField T)))).toIdeal
      (p.map (algebraMap T (IsLocalRing.ResidueField T))))) :
    let J := equationIdeal (a.map (algebraMap K T))
      (ha.map (algebraMap K T))
    let Q := J ⊔ equationIdeal p hp
    let hJQ : J.toIdeal ≤ Q.toIdeal := by
      rw [HomogeneousIdeal.toIdeal_sup]
      exact le_sup_left
    let cJ := projectiveCoefficientMap f J (coefficientChangedHomogeneousIdeal f J)
      (coefficientChangedHomogeneousIdeal_toIdeal f J)
    let q := schemeQuotientMap J Q hJQ
    letI : IsClosedImmersion q := schemeQuotientMap_closedImmersion J Q hJQ
    IsIso (closedImmersionIdealBaseChangeHom cJ q) := by
  let J := equationIdeal (a.map (algebraMap K T))
    (ha.map (algebraMap K T))
  let C₀ := equationIdeal (a.map (algebraMap K (IsLocalRing.ResidueField T)))
    (ha.map (algebraMap K (IsLocalRing.ResidueField T)))
  letI : Module.Flat T (CoordinateRing J) := fixedCubicCoordinateRing_flat a ha
  have hmap : J.toIdeal.map
      (MvPolynomial.map (algebraMap T (IsLocalRing.ResidueField T))) =
      C₀.toIdeal := by
    dsimp [J, C₀]
    have h := equationIdeal_map_comp (algebraMap K T)
      (algebraMap T (IsLocalRing.ResidueField T)) a ha
    rw [← IsScalarTower.algebraMap_eq K T
      (IsLocalRing.ResidueField T)] at h
    simpa only [IsLocalRing.ResidueField.algebraMap_eq] using h
  have hreg' : IsRegular
      (homogeneousCoefficientSection J C₀ hmap
        (polynomialClassInGrading J p hp) : CoordinateRing C₀) := by
    simpa only [homogeneousCoefficientSection, polynomialClassInGrading,
      coordinateCoefficientMap_mk] using hreg
  exact isIso_residueRegularHypersurfaceGlobalIdealBaseChange_any
    f J C₀ hmap p hp hreg'

end PfaffianDescent
