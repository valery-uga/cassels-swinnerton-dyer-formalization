import AllCharacteristics.NormalizedChartGeneration

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory HomogeneousLocalization
open AllCharacteristics.HomogeneousProjective
universe u
section
variable {K : Type u} [CommRing K] {σ : Type}
attribute [local instance] MvPolynomial.gradedAlgebra
variable (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K))
    (z : CoordinateRing I) (hz : z ∈ grading I 1)

/-- Original homogeneous coordinates divided by a general degree-one chart denominator. -/
noncomputable def linearChartCoordinate (j : σ) : Away (grading I) z :=
  AllCharacteristics.GradedChart.normalized (grading I) hz (coordinate I j) (coordinate_mem I j)

lemma eval₂_linearChartCoordinate_eq_fraction
    (p : MvPolynomial σ K) {d : ℕ} (hp : p.IsHomogeneous d) :
    p.eval₂ (AllCharacteristics.GradedChart.baseMap (grading I) (z := z))
      (linearChartCoordinate I z hz) =
      Away.mk (grading I) hz d (Ideal.Quotient.mk I.toIdeal p)
        (by simpa using polynomial_class_mem_grading I p hp) := by
  apply val_injective
  refine (AllCharacteristics.GradedChart.val_eval₂_normalized (grading I) hz
    (coordinate I) (coordinate_mem I) p hp).trans ?_
  have he : p.eval₂ (algebraMap K (CoordinateRing I)) (coordinate I) =
      Ideal.Quotient.mk I.toIdeal p := (congrFun (MvPolynomial.mk_eq_eval₂ I.toIdeal) p).symm
  rw [he, Away.val_mk]
  simp only [Localization.mk_pow, one_pow, ← Localization.mk_one_eq_algebraMap,
    Localization.mk_mul, one_mul, mul_one]
  rfl

/-- Normalized homogeneous coordinates generate every degree-one affine chart. -/
theorem eval₂_linearChartCoordinate_surjective :
    Function.Surjective (MvPolynomial.eval₂Hom
      (AllCharacteristics.GradedChart.baseMap (grading I) (z := z))
      (linearChartCoordinate I z hz)) := by
  intro a
  obtain ⟨n, b, hb, rfl⟩ := Away.mk_surjective (grading I) hz a
  have hb' : b ∈ grading I n := by simpa using hb
  obtain ⟨p, hp, rfl⟩ := hb'
  exact ⟨p, eval₂_linearChartCoordinate_eq_fraction I z hz p hp⟩

/-- Every homogeneous defining equation vanishes on the general linear chart. -/
theorem eval₂_linearChartCoordinate_eq_zero
    (p : MvPolynomial σ K) {d : ℕ} (hp : p.IsHomogeneous d) (hI : p ∈ I.toIdeal) :
    p.eval₂ (AllCharacteristics.GradedChart.baseMap (grading I) (z := z))
      (linearChartCoordinate I z hz) = 0 := by
  apply AllCharacteristics.GradedChart.eval₂_normalized_eq_zero
    (grading I) hz (coordinate I) (coordinate_mem I) p hp
  exact (congrFun (MvPolynomial.mk_eq_eval₂ I.toIdeal) p).symm.trans
    (Ideal.Quotient.eq_zero_iff_mem.mpr hI)

end
end PfaffianDescent
