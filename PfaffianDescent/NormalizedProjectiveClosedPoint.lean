import AllCharacteristics.AffineChartPresentation
import AllCharacteristics.FiniteLocalClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Finite

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u
section
variable {K A : Type u} [Field K] [CommRing A] [Algebra K A]
    {σ : Type} [Finite σ]
attribute [local instance] MvPolynomial.gradedAlgebra
variable (I : HomogeneousIdeal (homogeneousSubmodule σ K))
    (x : σ → A) (j : σ) (hx : x j = 1)
    (he : ∀ p ∈ I.toIdeal, p.eval₂ (algebraMap K A) x = 0)

noncomputable def normalizedPointChartMap : ChartRing I j →+* A :=
  AllCharacteristics.GradedChart.liftCoordinateOne (grading I) (coordinate I j)
    (Ideal.Quotient.lift I.toIdeal (eval₂Hom (algebraMap K A) x) he)
    (by change eval₂Hom (algebraMap K A) x (X j) = 1; simpa using hx)

lemma normalizedPointChartMap_base (r : K) :
    normalizedPointChartMap I x j hx he (chartBaseMap I j r) = algebraMap K A r := by
  let e := Ideal.Quotient.lift I.toIdeal (eval₂Hom (algebraMap K A) x) he
  have hej : e (coordinate I j) = 1 := by
    change eval₂Hom (algebraMap K A) x (X j) = 1
    simpa using hx
  exact (AllCharacteristics.GradedChart.liftCoordinateOne_baseMap
    (grading I) (coordinate I j) e hej r).trans (eval₂_C _ _ r)

lemma normalizedPointChartMap_coordinate (k : σ) :
    normalizedPointChartMap I x j hx he (chartCoordinate I j k) = x k := by
  let e := Ideal.Quotient.lift I.toIdeal (eval₂Hom (algebraMap K A) x) he
  have hej : e (coordinate I j) = 1 := by
    change eval₂Hom (algebraMap K A) x (X j) = 1
    simpa using hx
  exact (AllCharacteristics.GradedChart.liftCoordinateOne_normalized
    (grading I) (coordinate I j) e hej (coordinate_mem I j) (coordinate I k)
      (coordinate_mem I k)).trans (eval₂_X _ _ k)

lemma normalizedPointChartMap_eval (p : MvPolynomial σ K) :
    normalizedPointChartMap I x j hx he (p.eval₂ (chartBaseMap I j) (chartCoordinate I j)) =
      p.eval₂ (algebraMap K A) x := by
  rw [hom_eval₂]
  have hb : (normalizedPointChartMap I x j hx he).comp (chartBaseMap I j) = algebraMap K A :=
    RingHom.ext (normalizedPointChartMap_base I x j hx he)
  rw [hb]
  congr 1
  funext k
  exact normalizedPointChartMap_coordinate I x j hx he k

include j hx he in
/-- Normalized coordinates generating a finite algebra define a closed
immersion of its spectrum into the actual projective scheme. -/
theorem closed_point_of_normalized_coordinates [Module.Finite K A]
    (hgen : Function.Surjective (eval₂Hom (algebraMap K A) x)) :
    ∃ q : Spec (.of A) ⟶ scheme I, IsClosedImmersion q ∧
      q ≫ toBase I = Spec.map (CommRingCat.ofHom (algebraMap K A)) := by
  let g := normalizedPointChartMap I x j hx he
  have hg : Function.Surjective g := by
    intro a
    obtain ⟨p, hp⟩ := hgen a
    exact ⟨p.eval₂ (chartBaseMap I j) (chartCoordinate I j),
      (normalizedPointChartMap_eval I x j hx he p).trans hp⟩
  let q := Spec.map (CommRingCat.ofHom g) ≫ chartι I j
  have hs : IsClosedImmersion (Spec.map (CommRingCat.ofHom g)) :=
    IsClosedImmersion.spec_of_surjective _ hg
  have hq : q ≫ toBase I = Spec.map (CommRingCat.ofHom (algebraMap K A)) := by
    rw [Category.assoc, chartι_toBase, ← Spec.map_comp]
    apply congrArg Spec.map
    exact CommRingCat.hom_ext (RingHom.ext (normalizedPointChartMap_base I x j hx he))
  have : IsFinite (q ≫ toBase I) := by
    rw [hq]
    exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  have : IsFinite q := IsFinite.of_comp q (toBase I)
  have : IsPreimmersion q := inferInstanceAs
    (IsPreimmersion (Spec.map (CommRingCat.ofHom g) ≫ chartι I j))
  exact ⟨q, IsClosedImmersion.of_isPreimmersion q q.isClosedMap.isClosed_range, hq⟩

end
end PfaffianDescent
