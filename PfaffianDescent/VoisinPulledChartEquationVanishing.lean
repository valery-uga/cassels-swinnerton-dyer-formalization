import PfaffianDescent.VoisinAffineChartCoordinateSections
import PfaffianDescent.SchemeAffineFunctions
import PfaffianDescent.PolynomialProjectiveMap

/-!
# Defining equations on pulled affine projective charts

A homogeneous equation in a projective ideal vanishes after pulling its
normalized coordinates to any affine ordered-configuration chart.  The
coefficient ring map is the chart's map to the original base.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem pulledLinearChartCoordinate_eq_affineFunctionHom
    {L : Type u} [Field L]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) L))
    (z : CoordinateRing I) (hz : z ∈ grading I 1)
    (U : Scheme.{u})
    (t : U ⟶ Spec (.of (Away (grading I) z)))
    (j : Fin 4) :
    pulledLinearChartCoordinate I z hz U t j =
      affineFunctionHom t (linearChartCoordinate I z hz j) := by
  rfl

/-- A defining homogeneous equation vanishes on the pulled normalized
coordinates whenever the chart lift respects the chosen base map. -/
theorem pulledLinearChartCoordinate_equation_zero
    {L : Type u} [Field L]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) L))
    (z : CoordinateRing I) (hz : z ∈ grading I 1)
    (U : Scheme.{u})
    (t : U ⟶ Spec (.of (Away (grading I) z)))
    (tBase : U ⟶ Spec (.of L))
    (hbase : t ≫ Spec.map (CommRingCat.ofHom
      (AllCharacteristics.GradedChart.baseMap (grading I) (z := z))) = tBase)
    (p : MvPolynomial (Fin 4) L)
    (hp : p.IsHomogeneous 3) (hI : p ∈ I.toIdeal) :
    (p.map (affineFunctionHom tBase)).eval
      (fun j => pulledLinearChartCoordinate I z hz U t j) = 0 := by
  have hcoeff : affineFunctionHom tBase =
      (affineFunctionHom t).comp
        (AllCharacteristics.GradedChart.baseMap (grading I) (z := z)) := by
    rw [← affineFunctionHom_comp_Spec t
      (AllCharacteristics.GradedChart.baseMap (grading I) (z := z)), hbase]
  have hzero := eval₂_linearChartCoordinate_eq_zero I z hz p hp hI
  have hmap := congrArg (affineFunctionHom t) hzero
  rw [MvPolynomial.hom_eval₂, map_zero, ← hcoeff] at hmap
  simpa only [MvPolynomial.eval₂_eq_eval_map,
    pulledLinearChartCoordinate_eq_affineFunctionHom] using hmap

/-- Every ordered coordinate lift into the same affine Proj chart has the
same coefficient map, namely that of the ordered configuration base. -/
theorem orderedChartLift_baseMap
    {L : Type u} [Field L]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) L))
    (z : CoordinateRing I) (hz : z ∈ grading I 1)
    (U : Scheme.{u})
    (i : U ⟶ (AllCharacteristics.orderedFamilyConfigurationOver
      (toBase I) 8).left)
    (t : Fin 8 → (U ⟶ Spec (.of (Away (grading I) z))))
    (ht : ∀ k, t k ≫ Proj.awayι (grading I) z hz
      (by decide : 0 < 1) =
        (i ≫ Over.Hom.left
          (AllCharacteristics.orderedFamilyConfigurationι (toBase I) 8)) ≫
          (AllCharacteristics.orderedFamilyCoordinate (toBase I) 8 k).left)
    (k : Fin 8) :
    t k ≫ Spec.map (CommRingCat.ofHom
      (AllCharacteristics.GradedChart.baseMap (grading I) (z := z))) =
      i ≫ (AllCharacteristics.orderedFamilyConfigurationOver
        (toBase I) 8).hom := by
  let q := Proj.awayι (grading I) z hz (by decide : 0 < 1)
  let cfg := AllCharacteristics.orderedFamilyConfigurationι (toBase I) 8
  let pr := AllCharacteristics.orderedFamilyCoordinate (toBase I) 8 k
  have hq := homogeneousChart_toBase I z hz (by decide : 0 < 1)
  have hpr := AllCharacteristics.orderedFamilyCoordinate_toBase (toBase I) 8 k
  calc
    t k ≫ Spec.map (CommRingCat.ofHom
      (AllCharacteristics.GradedChart.baseMap (grading I) (z := z))) =
        (t k ≫ q) ≫ toBase I := by
          rw [← hq]
          exact (Category.assoc _ _ _).symm
    _ = ((i ≫ cfg.left) ≫ pr.left) ≫ toBase I := by
      exact congrArg (fun v : U ⟶ Proj (grading I) => v ≫ toBase I) (ht k)
    _ = i ≫ (AllCharacteristics.orderedFamilyConfigurationOver
        (toBase I) 8).hom := by
      rw [Category.assoc (i ≫ cfg.left) pr.left (toBase I), hpr]
      simpa only [Category.assoc] using
        (congrArg (fun v => i ≫ v) cfg.w)

theorem pulledEightLinearChartCoordinates_equation_zero
    {L : Type u} [Field L]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) L))
    (z : CoordinateRing I) (hz : z ∈ grading I 1)
    (U : Scheme.{u})
    (i : U ⟶ (AllCharacteristics.orderedFamilyConfigurationOver
      (toBase I) 8).left)
    (t : Fin 8 → (U ⟶ Spec (.of (Away (grading I) z))))
    (ht : ∀ k, t k ≫ Proj.awayι (grading I) z hz
      (by decide : 0 < 1) =
        (i ≫ Over.Hom.left
          (AllCharacteristics.orderedFamilyConfigurationι (toBase I) 8)) ≫
          (AllCharacteristics.orderedFamilyCoordinate (toBase I) 8 k).left)
    (p : MvPolynomial (Fin 4) L)
    (hp : p.IsHomogeneous 3) (hI : p ∈ I.toIdeal) :
    ∀ k : Fin 8,
      (p.map (affineFunctionHom
        (i ≫ (AllCharacteristics.orderedFamilyConfigurationOver
          (toBase I) 8).hom))).eval
        (pulledEightLinearChartCoordinates I z hz U t k) = 0 := by
  intro k
  exact pulledLinearChartCoordinate_equation_zero I z hz U (t k)
    (i ≫ (AllCharacteristics.orderedFamilyConfigurationOver
      (toBase I) 8).hom)
    (orderedChartLift_baseMap I z hz U i t ht k) p hp hI

/-- The chosen chart denominator evaluates to one on its regular
normalized coordinates. -/
theorem linearChartCoordinate_denominator_one
    {L : Type u} [Field L]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) L))
    (c : Fin 4 → L) :
    let z : CoordinateRing I :=
      Ideal.Quotient.mk I.toIdeal (homogeneousLinearForm c)
    let hz : z ∈ grading I 1 :=
      polynomial_class_mem_grading I (homogeneousLinearForm c)
        (homogeneousLinearForm_isHomogeneous c)
    (homogeneousLinearForm c).eval₂
      (AllCharacteristics.GradedChart.baseMap (grading I) (z := z))
      (linearChartCoordinate I z hz) = 1 := by
  dsimp only
  let z : CoordinateRing I :=
    Ideal.Quotient.mk I.toIdeal (homogeneousLinearForm c)
  let hz : z ∈ grading I 1 :=
    polynomial_class_mem_grading I (homogeneousLinearForm c)
      (homogeneousLinearForm_isHomogeneous c)
  rw [eval₂_linearChartCoordinate_eq_fraction I z hz
    (homogeneousLinearForm c) (homogeneousLinearForm_isHomogeneous c)]
  exact AllCharacteristics.GradedChart.normalized_self (grading I) hz

theorem pulledLinearChartCoordinate_denominator_one
    {L : Type u} [Field L]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) L))
    (c : Fin 4 → L)
    (U : Scheme.{u})
    (t : U ⟶ Spec (.of (Away (grading I)
      (Ideal.Quotient.mk I.toIdeal (homogeneousLinearForm c)))))
    (tBase : U ⟶ Spec (.of L))
    (hbase : t ≫ Spec.map (CommRingCat.ofHom
      (AllCharacteristics.GradedChart.baseMap (grading I)
        (z := Ideal.Quotient.mk I.toIdeal (homogeneousLinearForm c)))) = tBase) :
    ((homogeneousLinearForm c).map (affineFunctionHom tBase)).eval
      (fun j => pulledLinearChartCoordinate I
        (Ideal.Quotient.mk I.toIdeal (homogeneousLinearForm c))
        (polynomial_class_mem_grading I (homogeneousLinearForm c)
          (homogeneousLinearForm_isHomogeneous c)) U t j) = 1 := by
  let z : CoordinateRing I :=
    Ideal.Quotient.mk I.toIdeal (homogeneousLinearForm c)
  let hz : z ∈ grading I 1 :=
    polynomial_class_mem_grading I (homogeneousLinearForm c)
      (homogeneousLinearForm_isHomogeneous c)
  have hcoeff : affineFunctionHom tBase =
      (affineFunctionHom t).comp
        (AllCharacteristics.GradedChart.baseMap (grading I) (z := z)) := by
    rw [← affineFunctionHom_comp_Spec t
      (AllCharacteristics.GradedChart.baseMap (grading I) (z := z)), hbase]
  have h := congrArg (affineFunctionHom t)
    (linearChartCoordinate_denominator_one I c)
  rw [MvPolynomial.hom_eval₂, map_one, ← hcoeff] at h
  simpa only [MvPolynomial.eval₂_eq_eval_map,
    pulledLinearChartCoordinate_eq_affineFunctionHom] using h

theorem pulledEightLinearChartCoordinates_denominator_one
    {L : Type u} [Field L]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) L))
    (c : Fin 4 → L)
    (U : Scheme.{u})
    (i : U ⟶ (AllCharacteristics.orderedFamilyConfigurationOver
      (toBase I) 8).left)
    (t : Fin 8 → (U ⟶ Spec (.of (Away (grading I)
      (Ideal.Quotient.mk I.toIdeal (homogeneousLinearForm c))))))
    (ht : ∀ k, t k ≫ Proj.awayι (grading I)
      (Ideal.Quotient.mk I.toIdeal (homogeneousLinearForm c))
      (polynomial_class_mem_grading I (homogeneousLinearForm c)
        (homogeneousLinearForm_isHomogeneous c))
      (by decide : 0 < 1) =
        (i ≫ Over.Hom.left
          (AllCharacteristics.orderedFamilyConfigurationι (toBase I) 8)) ≫
          (AllCharacteristics.orderedFamilyCoordinate (toBase I) 8 k).left) :
    let z : CoordinateRing I :=
      Ideal.Quotient.mk I.toIdeal (homogeneousLinearForm c)
    let hz : z ∈ grading I 1 :=
      polynomial_class_mem_grading I (homogeneousLinearForm c)
        (homogeneousLinearForm_isHomogeneous c)
    ∀ k : Fin 8,
      ((homogeneousLinearForm c).map (affineFunctionHom
        (i ≫ (AllCharacteristics.orderedFamilyConfigurationOver
          (toBase I) 8).hom))).eval
        (pulledEightLinearChartCoordinates I z hz U t k) = 1 := by
  dsimp only
  intro k
  exact pulledLinearChartCoordinate_denominator_one I c U (t k)
    (i ≫ (AllCharacteristics.orderedFamilyConfigurationOver
      (toBase I) 8).hom)
    (orderedChartLift_baseMap I _ _ U i t ht k)

end PfaffianDescent
