import AllCharacteristics.GradedCoefficientMap
import AllCharacteristics.GradedAwayMap
import AllCharacteristics.ProjectiveChartBaseChange

/-!
# Global projective coefficient change and its affine charts

The global Proj morphism induced by coefficient change agrees on each
coordinate chart with the already constructed affine coefficient map.
It commutes with the structure morphisms to the coefficient spectra.
-/

open MvPolynomial AlgebraicGeometry CategoryTheory HomogeneousLocalization
namespace AllCharacteristics
namespace HomogeneousProjective
universe u
variable {R S : Type u} {σ : Type} [CommRing R] [CommRing S]
attribute [local instance] MvPolynomial.gradedAlgebra
variable (f : R →+* S)
variable (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ R))
variable (J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ S))
variable (h : I.toIdeal.map (MvPolynomial.map f) = J.toIdeal)

/-- The global projective morphism induced by changing coefficients. -/
noncomputable def projectiveCoefficientMap : scheme J ⟶ scheme I :=
  Proj.map (gradedCoefficientMap f I J h) (irrelevant_le_map_gradedCoefficientMap f I J h)

/-- The homogeneous-localization form of the coefficient map on a coordinate
chart, with the target coordinate identified explicitly. -/
noncomputable def chartGradedCoefficientMap (j : σ) : ChartRing I j →+* ChartRing J j :=
  gradedAwayMapOfEq (gradedCoefficientMap f I J h) (coordinate I j) (coordinate J j)
    (gradedCoefficientMap_coordinate f I J h j)

/-- The localization map preserves normalized evaluation of homogeneous
polynomials, changing only their coefficients. -/
theorem chartGradedCoefficientMap_eval_homogeneous
    (j : σ) (p : MvPolynomial σ R) {d : ℕ} (hp : p.IsHomogeneous d) :
    chartGradedCoefficientMap f I J h j (p.eval₂ (chartBaseMap I j) (chartCoordinate I j)) =
      (p.map f).eval₂ (chartBaseMap J j) (chartCoordinate J j) := by
  rw [eval₂_chartCoordinate_eq_fraction I j p hp,
    eval₂_chartCoordinate_eq_fraction J j (p.map f) (hp.map f)]
  unfold chartGradedCoefficientMap
  rw [gradedAwayMapOfEq_mk _ _ _ _ _ (coordinate_mem J j)]
  apply HomogeneousLocalization.val_injective
  simp only [Away.val_mk]
  congr 1

/-- The localization construction equals the coefficient map obtained from
the affine polynomial-quotient presentation. -/
theorem chartGradedCoefficientMap_eq (j : σ) :
    chartGradedCoefficientMap f I J h j = chartCoefficientMap f I J h j := by
  have he : (chartGradedCoefficientMap f I J h j).comp
      (eval₂Hom (chartBaseMap I j) (chartCoordinate I j)) =
      (chartCoefficientMap f I J h j).comp
        (eval₂Hom (chartBaseMap I j) (chartCoordinate I j)) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      change chartGradedCoefficientMap f I J h j
        ((C r).eval₂ (chartBaseMap I j) (chartCoordinate I j)) =
          chartCoefficientMap f I J h j ((C r).eval₂ (chartBaseMap I j) (chartCoordinate I j))
      rw [chartGradedCoefficientMap_eval_homogeneous f I J h j _ (isHomogeneous_C σ r),
        chartCoefficientMap_eval]
    · intro i
      change chartGradedCoefficientMap f I J h j
        ((X i).eval₂ (chartBaseMap I j) (chartCoordinate I j)) =
          chartCoefficientMap f I J h j ((X i).eval₂ (chartBaseMap I j) (chartCoordinate I j))
      rw [chartGradedCoefficientMap_eval_homogeneous f I J h j _ (isHomogeneous_X R i),
        chartCoefficientMap_eval]
  apply RingHom.ext
  intro x
  obtain ⟨p, rfl⟩ := eval₂_chartCoordinate_surjective I j x
  exact congr($he p)

/-- The global projective coefficient map agrees with the affine chart maps. -/
theorem chartι_projectiveCoefficientMap (j : σ) :
    chartι J j ≫ projectiveCoefficientMap f I J h =
      Spec.map (CommRingCat.ofHom (chartCoefficientMap f I J h j)) ≫ chartι I j := by
  have hm := awayι_comp_map_of_eq (gradedCoefficientMap f I J h)
    (irrelevant_le_map_gradedCoefficientMap f I J h)
    (coordinate I j) (coordinate J j) (gradedCoefficientMap_coordinate f I J h j)
    (by decide : 0 < 1) (coordinate_mem I j) (coordinate_mem J j)
  change chartι J j ≫ projectiveCoefficientMap f I J h =
    Spec.map (CommRingCat.ofHom (chartGradedCoefficientMap f I J h j)) ≫ chartι I j at hm
  rw [chartGradedCoefficientMap_eq] at hm
  exact hm

/-- The projective coefficient morphism is over the original coefficient
spectrum, with the target's coefficient morphism supplied by base change. -/
theorem projectiveCoefficientMap_toBase :
    projectiveCoefficientMap f I J h ≫ toBase I =
      toBase J ≫ Spec.map (CommRingCat.ofHom f) := by
  apply (coordinateOpenCover J).openCover.hom_ext
  intro j
  change σ at j
  change chartι J j ≫ (projectiveCoefficientMap f I J h ≫ toBase I) =
    chartι J j ≫ (toBase J ≫ Spec.map (CommRingCat.ofHom f))
  rw [← Category.assoc, chartι_projectiveCoefficientMap, Category.assoc,
    chartι_toBase, ← Category.assoc, chartι_toBase, ← Spec.map_comp, ← Spec.map_comp]
  exact congrArg Spec.map (isPushout_chartCoefficientMap f I J h j).w

end HomogeneousProjective
end AllCharacteristics
