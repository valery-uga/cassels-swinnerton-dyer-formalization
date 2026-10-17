import AllCharacteristics.AffineChartPresentation
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.Flat.Localization

/-!
# Coordinate charts are retracts of ordinary localizations

Normalized coordinate evaluation factors through a homogeneous polynomial
quotient. It sends the distinguished coordinate to one, so it extends to the
ordinary localization. This extension retracts the inclusion of the actual
homogeneous chart. Flatness of the homogeneous quotient therefore implies
flatness of every chart over an arbitrary commutative coefficient ring.
-/

open MvPolynomial HomogeneousLocalization
namespace AllCharacteristics
namespace HomogeneousProjective
universe u
variable {R : Type u} {σ : Type} [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra
variable (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ R)) (j : σ)

/-- Normalize all homogeneous coordinates in the distinguished chart. -/
noncomputable def coordinateRingToChart : CoordinateRing I →+* ChartRing I j :=
  Ideal.Quotient.lift I.toIdeal
    (eval₂Hom (chartBaseMap I j) (chartCoordinate I j))
    (fun p hp ↦ eval₂_chartCoordinate_eq_zero_of_mem I j p hp)

/-- Normalization of a polynomial class is normalized polynomial evaluation. -/
theorem coordinateRingToChart_mk (p : MvPolynomial σ R) :
    coordinateRingToChart I j (Ideal.Quotient.mk I.toIdeal p) =
      p.eval₂ (chartBaseMap I j) (chartCoordinate I j) := rfl

/-- Normalization sends coordinates to the corresponding chart coordinates. -/
theorem coordinateRingToChart_coordinate (i : σ) :
    coordinateRingToChart I j (coordinate I i) = chartCoordinate I j i := by
  change (X i : MvPolynomial σ R).eval₂ _ _ = _
  rw [eval₂_X]

/-- Normalization preserves the specified coefficient homomorphism. -/
theorem coordinateRingToChart_algebraMap (r : R) :
    coordinateRingToChart I j (algebraMap R (CoordinateRing I) r) = chartBaseMap I j r := by
  change (C r : MvPolynomial σ R).eval₂ _ _ = _
  rw [eval₂_C]

/-- Extending normalization to the ordinary localization gives the chart
retraction. -/
noncomputable def chartLocalizationRetraction :
    Localization (Submonoid.powers (coordinate I j)) →+* ChartRing I j :=
  IsLocalization.Away.lift (coordinate I j)
    ((coordinateRingToChart_coordinate I j j).trans (chartCoordinate_self I j) ▸ isUnit_one)

/-- On the homogeneous coordinate algebra, the retraction is normalization. -/
theorem chartLocalizationRetraction_algebraMap (a : CoordinateRing I) :
    chartLocalizationRetraction I j
      (algebraMap (CoordinateRing I) (Localization (Submonoid.powers (coordinate I j))) a) =
        coordinateRingToChart I j a :=
  IsLocalization.Away.lift_eq _ _ a

/-- The retraction is the identity on the included homogeneous chart. -/
theorem chartLocalizationRetraction_val (x : ChartRing I j) :
    chartLocalizationRetraction I j x.val = x := by
  let L := Localization (Submonoid.powers (coordinate I j))
  let h := (chartLocalizationRetraction I j).comp (algebraMap (ChartRing I j) L)
  have he : h.comp (eval₂Hom (chartBaseMap I j) (chartCoordinate I j)) =
      eval₂Hom (chartBaseMap I j) (chartCoordinate I j) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, eval₂Hom_C]
      change chartLocalizationRetraction I j
        (algebraMap (CoordinateRing I) L (algebraMap R (CoordinateRing I) r)) =
          chartBaseMap I j r
      exact (chartLocalizationRetraction_algebraMap I j _).trans
        (coordinateRingToChart_algebraMap I j r)
    · intro i
      simp only [RingHom.comp_apply, eval₂Hom_X']
      exact (GradedChart.liftCoordinateOne_normalized (grading I) (coordinate I j)
        (coordinateRingToChart I j)
        ((coordinateRingToChart_coordinate I j j).trans (chartCoordinate_self I j))
        (coordinate_mem I j) (coordinate I i) (coordinate_mem I i)).trans
          (coordinateRingToChart_coordinate I j i)
  obtain ⟨p, rfl⟩ := eval₂_chartCoordinate_surjective I j x
  exact DFunLike.congr_fun he p

/-- Every actual coordinate chart of a flat homogeneous polynomial quotient
is flat over the coefficient ring, without a Dedekind or domain hypothesis. -/
theorem flat_chartRing_of_flat_coordinateRing [Module.Flat R (CoordinateRing I)] :
    let := (chartBaseMap I j).toAlgebra
    Module.Flat R (ChartRing I j) := by
  let := (chartBaseMap I j).toAlgebra
  let L := Localization (Submonoid.powers (coordinate I j))
  have : Module.Flat R L := Module.Flat.trans R (CoordinateRing I) L
  let v : ChartRing I j →ₐ[R] L := {
    __ := algebraMap (ChartRing I j) L
    commutes' := fun r ↦ GradedChart.val_baseMap (grading I) (z := coordinate I j) r }
  let w : L →ₐ[R] ChartRing I j := {
    __ := chartLocalizationRetraction I j
    commutes' := fun r ↦ (chartLocalizationRetraction_algebraMap I j
      (algebraMap R (CoordinateRing I) r)).trans (coordinateRingToChart_algebraMap I j r) }
  apply Module.Flat.of_retract v.toLinearMap w.toLinearMap
  apply LinearMap.ext
  intro x
  exact chartLocalizationRetraction_val I j x

end HomogeneousProjective
end AllCharacteristics
