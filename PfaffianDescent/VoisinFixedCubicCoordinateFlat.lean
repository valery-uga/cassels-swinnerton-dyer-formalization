import PfaffianDescent.ProjectiveCoordinateTensorBaseChange
import PfaffianDescent.VoisinChartBaseIdealRegular
import AllCharacteristics.HypersurfaceFiberNaturality
import Mathlib.RingTheory.Flat.Stability

/-!
# Flatness of the fixed cubic after arbitrary coefficient change

The fixed cubic surface is defined over a field. Its homogeneous coordinate
ring is therefore a flat vector space, and its coordinate ring after any
coefficient change is flat over the new coefficient ring. In particular this
supplies the flat-model assumption of the local intersection-chart theorem
for every local parameter ring.
-/

namespace PfaffianDescent

open MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Flatness of a homogeneous coordinate ring survives arbitrary coefficient
change from a field, including nonreduced coefficient rings. -/
theorem coordinateRing_flat_of_field_baseChange
    {K T : Type u} [Field K] [CommRing T] [Algebra K T]
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) T))
    (hJC : J.toIdeal.map (MvPolynomial.map (algebraMap K T)) = C.toIdeal) :
    Module.Flat T (CoordinateRing C) := by
  let e := coordinateRingTensorAlgEquiv J C hJC
  exact Module.Flat.of_linearEquiv e.symm.toLinearEquiv

/-- The homogeneous coordinate ring of a fixed cubic remains flat over any
coefficient algebra. This is the fixed-family input to the regular-section
intersection theorem. -/
theorem fixedCubicCoordinateRing_flat
    {K T : Type u} [Field K] [CommRing T] [Algebra K T]
    (a : MvPolynomial (Fin 4) K) (ha : a.IsHomogeneous 3) :
    Module.Flat T
      (CoordinateRing (equationIdeal (a.map (algebraMap K T))
        (ha.map (algebraMap K T)))) := by
  exact coordinateRing_flat_of_field_baseChange
    (equationIdeal a ha)
    (equationIdeal (a.map (algebraMap K T)) (ha.map (algebraMap K T)))
    (equationIdeal_map (algebraMap K T) a ha)

/-- On a local parameter ring, regularity of the reduced moving cubic
implies flatness of each actual affine intersection chart with the fixed
cubic. The fixed family's flatness is supplied by field base change. -/
theorem fixedCubicIntersectionChart_flat_of_residue_regular
    {K T : Type u} [Field K] [CommRing T] [Algebra K T]
    [IsLocalRing T]
    (a : MvPolynomial (Fin 4) K) (ha : a.IsHomogeneous 3)
    (p : MvPolynomial (Fin 4) T) (hp : p.IsHomogeneous 3)
    (hreg : IsRegular (Ideal.Quotient.mk
      (equationIdeal (a.map (algebraMap K (IsLocalRing.ResidueField T)))
        (ha.map (algebraMap K (IsLocalRing.ResidueField T)))).toIdeal
      (p.map (algebraMap T (IsLocalRing.ResidueField T)))))
    (j : Fin 4) :
    let J := equationIdeal (a.map (algebraMap K T))
      (ha.map (algebraMap K T))
    ((chartQuotientMap J (J ⊔ equationIdeal p hp)
      (by rw [HomogeneousIdeal.toIdeal_sup]; exact le_sup_left) j).comp
      (chartBaseMap J j)).Flat := by
  let J := equationIdeal (a.map (algebraMap K T))
    (ha.map (algebraMap K T))
  let C₀ := equationIdeal (a.map (algebraMap K (IsLocalRing.ResidueField T)))
    (ha.map (algebraMap K (IsLocalRing.ResidueField T)))
  let _ : Module.Flat T (CoordinateRing J) :=
    fixedCubicCoordinateRing_flat a ha
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
  exact flat_hypersurfaceIntersectionChart_of_residue_regular
    J C₀ hmap p hp hreg' j

/-- The equation cutting the moving cubic on each affine chart of the fixed
cubic surface is a non-zero-divisor whenever its residue equation is
regular.  Its principal ideal is the kernel of the actual chart map. -/
theorem fixedCubicIntersectionChart_regular_principalKernel_of_residue_regular
    {K T : Type u} [Field K] [CommRing T] [Algebra K T]
    [IsLocalRing T]
    (a : MvPolynomial (Fin 4) K) (ha : a.IsHomogeneous 3)
    (p : MvPolynomial (Fin 4) T) (hp : p.IsHomogeneous 3)
    (hreg : IsRegular (Ideal.Quotient.mk
      (equationIdeal (a.map (algebraMap K (IsLocalRing.ResidueField T)))
        (ha.map (algebraMap K (IsLocalRing.ResidueField T)))).toIdeal
      (p.map (algebraMap T (IsLocalRing.ResidueField T)))))
    (j : Fin 4) :
    let J := equationIdeal (a.map (algebraMap K T))
      (ha.map (algebraMap K T))
    let x := p.eval₂ (chartBaseMap J j) (chartCoordinate J j)
    IsRegular x ∧
      RingHom.ker (chartQuotientMap J (J ⊔ equationIdeal p hp)
        (by rw [HomogeneousIdeal.toIdeal_sup]; exact le_sup_left) j) =
        Ideal.span ({x} : Set (ChartRing J j)) := by
  let J := equationIdeal (a.map (algebraMap K T))
    (ha.map (algebraMap K T))
  let C₀ := equationIdeal (a.map (algebraMap K (IsLocalRing.ResidueField T)))
    (ha.map (algebraMap K (IsLocalRing.ResidueField T)))
  let _ : Module.Flat T (CoordinateRing J) := fixedCubicCoordinateRing_flat a ha
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
  constructor
  · rw [eval₂_chartCoordinate_eq_fraction J j p hp]
    exact chartSection_regular_of_residue_regular J C₀ hmap
      (polynomialClassInGrading J p hp) hreg' j
  · exact chartQuotientMap_ker_eq_equation J p hp j

end PfaffianDescent
