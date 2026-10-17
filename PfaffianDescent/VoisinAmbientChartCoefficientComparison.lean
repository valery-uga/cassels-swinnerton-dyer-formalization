import AllCharacteristics.HomogeneousProjectiveAmbient

/-! Recovering coordinate-chart values from equality after coefficient change. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Two maps of the same ambient coordinate chart that give the same
projective point after coefficient change agree on the entire original
chart ring. -/
theorem ambientChartMap_eq_of_coefficientChangedPoint_eq
    {R S F : Type u} [CommRing R] [CommRing S] [Field F]
    (f : R →+* S) (j : Fin 4)
    (gS : Away (homogeneousSubmodule (Fin 4) S) (X j) →+* F)
    (gR : Away (homogeneousSubmodule (Fin 4) R) (X j) →+* F)
    (hpoint :
      (Spec.map (CommRingCat.ofHom gS) ≫
        Proj.awayι (homogeneousSubmodule (Fin 4) S) (X j)
          (isHomogeneous_X S j) (by decide : 0 < 1)) ≫
        ambientCoefficientMap f =
      Spec.map (CommRingCat.ofHom gR) ≫
        Proj.awayι (homogeneousSubmodule (Fin 4) R) (X j)
          (isHomogeneous_X R j) (by decide : 0 < 1)) :
    gS.comp (ambientCoefficientChartMap f j) = gR := by
  rw [Category.assoc, awayι_comp_ambientCoefficientMap,
    ← Category.assoc, ← Spec.map_comp] at hpoint
  exact ambientCoefficientChartMap_eq_of_projective_eq j
    (gS.comp (ambientCoefficientChartMap f j)) gR hpoint

/-- Equality after coefficient change identifies all normalized coordinate
ratios on a common ambient projective chart. -/
theorem ambientChartCoordinate_eq_of_coefficientChangedPoint_eq
    {R S F : Type u} [CommRing R] [CommRing S] [Field F]
    (f : R →+* S) (j i : Fin 4)
    (gS : Away (homogeneousSubmodule (Fin 4) S) (X j) →+* F)
    (gR : Away (homogeneousSubmodule (Fin 4) R) (X j) →+* F)
    (hpoint :
      (Spec.map (CommRingCat.ofHom gS) ≫
        Proj.awayι (homogeneousSubmodule (Fin 4) S) (X j)
          (isHomogeneous_X S j) (by decide : 0 < 1)) ≫
        ambientCoefficientMap f =
      Spec.map (CommRingCat.ofHom gR) ≫
        Proj.awayι (homogeneousSubmodule (Fin 4) R) (X j)
          (isHomogeneous_X R j) (by decide : 0 < 1)) :
    gS (AllCharacteristics.GradedChart.normalized
      (homogeneousSubmodule (Fin 4) S) (isHomogeneous_X S j)
      (X i) (isHomogeneous_X S i)) =
    gR (AllCharacteristics.GradedChart.normalized
      (homogeneousSubmodule (Fin 4) R) (isHomogeneous_X R j)
      (X i) (isHomogeneous_X R i)) := by
  have hmap := ambientChartMap_eq_of_coefficientChangedPoint_eq
    f j gS gR hpoint
  calc
    gS (AllCharacteristics.GradedChart.normalized
        (homogeneousSubmodule (Fin 4) S) (isHomogeneous_X S j)
        (X i) (isHomogeneous_X S i)) =
      (gS.comp (ambientCoefficientChartMap f j))
        (AllCharacteristics.GradedChart.normalized
          (homogeneousSubmodule (Fin 4) R) (isHomogeneous_X R j)
          (X i) (isHomogeneous_X R i)) := by
            rw [RingHom.comp_apply, ambientCoefficientChartMap_coordinate]
    _ = _ := by rw [hmap]

/-- A field-valued point over the changed coefficient ring inherits an
ordinary ambient coordinate-chart presentation whenever its image over the
original ring has one. The resulting chart homomorphism lies over the
original chart map. -/
theorem exists_ambientChartMap_of_coefficientChangedPoint_eq
    {R S F : Type u} [CommRing R] [CommRing S] [Field F]
    (f : R →+* S) (j : Fin 4)
    (qS : Spec (.of F) ⟶
      Proj (homogeneousSubmodule (Fin 4) S))
    (gR : Away (homogeneousSubmodule (Fin 4) R) (X j) →+* F)
    (hpoint : qS ≫ ambientCoefficientMap f =
      Spec.map (CommRingCat.ofHom gR) ≫
        Proj.awayι (homogeneousSubmodule (Fin 4) R) (X j)
          (isHomogeneous_X R j) (by decide : 0 < 1)) :
    ∃ gS : Away (homogeneousSubmodule (Fin 4) S) (X j) →+* F,
      (Spec.map (CommRingCat.ofHom gS) ≫
        Proj.awayι (homogeneousSubmodule (Fin 4) S) (X j)
          (isHomogeneous_X S j) (by decide : 0 < 1) = qS) ∧
      gS.comp (ambientCoefficientChartMap f j) = gR := by
  let sq := isPullback_ambientCoefficientMap_chart f j
  let c := sq.lift (Spec.map (CommRingCat.ofHom gR)) qS hpoint.symm
  let gS : Away (homogeneousSubmodule (Fin 4) S) (X j) →+* F :=
    (Spec.preimage c).hom
  have hc : Spec.map (CommRingCat.ofHom gS) = c := by
    exact Spec.map_preimage c
  refine ⟨gS, ?_, ?_⟩
  · rw [hc]
    exact sq.lift_snd _ _ _
  · apply ambientChartMap_eq_of_coefficientChangedPoint_eq f j gS gR
    rw [hc, sq.lift_snd]
    exact hpoint

end PfaffianDescent
