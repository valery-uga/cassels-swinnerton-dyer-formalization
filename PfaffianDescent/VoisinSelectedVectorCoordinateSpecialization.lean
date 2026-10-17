import PfaffianDescent.VoisinAffineChartCoordinateSections
import PfaffianDescent.VoisinProjectiveVectorChartMap

/-!
# Specialization of an ordered chart coordinate to its selected vector

The affine Proj chart is an open immersion, hence a monomorphism. An
equality of projective points therefore identifies their affine chart
maps. The regular coordinate sections then specialize to the normalized
coordinates of the selected vector.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem pulledLinearChartCoordinate_value_of_projectiveVectorPoint
    {L : Type u} [Field L]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) L))
    (c v : Fin 4 → L)
    (hv : ∀ p ∈ I.toIdeal, p.eval v = 0)
    (hcv : (homogeneousLinearForm c).eval v ≠ 0)
    (U : Scheme.{u})
    (a : Spec (.of L) ⟶ U)
    (t : U ⟶ Spec (.of (Away (grading I)
      (Ideal.Quotient.mk I.toIdeal (homogeneousLinearForm c)))))
    (hpoint : (a ≫ t) ≫
        Proj.awayι (grading I)
          (Ideal.Quotient.mk I.toIdeal (homogeneousLinearForm c))
          (polynomial_class_mem_grading I
            (homogeneousLinearForm c) (homogeneousLinearForm_isHomogeneous c))
          (by decide : 0 < 1) =
        projectiveVectorSchemePointInLinearChart I c v hv hcv)
    (j : Fin 4) :
    a.appTop.hom
        (pulledLinearChartCoordinate I
          (Ideal.Quotient.mk I.toIdeal (homogeneousLinearForm c))
          (polynomial_class_mem_grading I
            (homogeneousLinearForm c) (homogeneousLinearForm_isHomogeneous c))
          U t j) =
      (StructureSheaf.globalSectionsIso L).hom
        (normalizedVectorInLinearChart c v j) := by
  let z : CoordinateRing I :=
    Ideal.Quotient.mk I.toIdeal (homogeneousLinearForm c)
  have hz : z ∈ grading I 1 := polynomial_class_mem_grading I
    (homogeneousLinearForm c) (homogeneousLinearForm_isHomogeneous c)
  let chart := Proj.awayι (grading I) z hz (by decide : 0 < 1)
  have hmap : a ≫ t = Spec.map (CommRingCat.ofHom
      (projectiveVectorSchemePointInLinearChartMap I c v hv hcv)) := by
    apply (cancel_mono chart).mp
    exact hpoint.trans
      (projectiveVectorSchemePointInLinearChart_eq_chartMap I c v hv hcv)
  have hvalue := pulledLinearChartCoordinate_value_of_chartMap I z hz U a t
    (projectiveVectorSchemePointInLinearChartMap I c v hv hcv) hmap j
  rw [projectiveVectorSchemePointInLinearChartMap_coordinate] at hvalue
  exact hvalue

/-- When all eight ordered projective points are represented by selected
vectors, the eight regular chart-coordinate sections specialize to their
normalized vector coordinates at the selected field-valued point. -/
theorem pulledEightLinearChartCoordinates_value_of_selectedConfiguration
    {L : Type u} [Field L]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) L))
    (c : Fin 4 → L)
    (y : Fin 8 → Fin 4 → L)
    (hy : ∀ k, ∀ p ∈ I.toIdeal, p.eval (y k) = 0)
    (hc : ∀ k, (homogeneousLinearForm c).eval (y k) ≠ 0)
    (U : Scheme.{u})
    (i : U ⟶ (AllCharacteristics.orderedFamilyConfigurationOver
      (toBase I) 8).left)
    (A : Spec (.of L) ⟶
      (AllCharacteristics.orderedFamilyConfigurationOver (toBase I) 8).left)
    (a : Spec (.of L) ⟶ U) (ha : a ≫ i = A)
    (t : Fin 8 → (U ⟶ Spec (.of (Away (grading I)
      (Ideal.Quotient.mk I.toIdeal (homogeneousLinearForm c))))))
    (ht : ∀ k, t k ≫ Proj.awayι (grading I)
      (Ideal.Quotient.mk I.toIdeal (homogeneousLinearForm c))
      (polynomial_class_mem_grading I
        (homogeneousLinearForm c) (homogeneousLinearForm_isHomogeneous c))
      (by decide : 0 < 1) =
        (i ≫ Over.Hom.left
          (AllCharacteristics.orderedFamilyConfigurationι (toBase I) 8)) ≫
          (AllCharacteristics.orderedFamilyCoordinate (toBase I) 8 k).left)
    (hcoord : ∀ k,
      (A ≫ Over.Hom.left
        (AllCharacteristics.orderedFamilyConfigurationι (toBase I) 8)) ≫
        (AllCharacteristics.orderedFamilyCoordinate (toBase I) 8 k).left =
          projectiveVectorSchemePointInLinearChart I c (y k) (hy k) (hc k)) :
    ∀ k j,
      a.appTop.hom
          (pulledEightLinearChartCoordinates I
            (Ideal.Quotient.mk I.toIdeal (homogeneousLinearForm c))
            (polynomial_class_mem_grading I
              (homogeneousLinearForm c) (homogeneousLinearForm_isHomogeneous c))
            U t k j) =
        (StructureSheaf.globalSectionsIso L).hom
          (normalizedVectorInLinearChart c (y k) j) := by
  intro k j
  let chart := Proj.awayι (grading I)
    (Ideal.Quotient.mk I.toIdeal (homogeneousLinearForm c))
    (polynomial_class_mem_grading I
      (homogeneousLinearForm c) (homogeneousLinearForm_isHomogeneous c))
    (by decide : 0 < 1)
  have hpoint : (a ≫ t k) ≫ chart =
      projectiveVectorSchemePointInLinearChart I c (y k) (hy k) (hc k) := by
    rw [Category.assoc a (t k) chart, ht k]
    change ((a ≫ i) ≫ Over.Hom.left
      (AllCharacteristics.orderedFamilyConfigurationι (toBase I) 8)) ≫
      (AllCharacteristics.orderedFamilyCoordinate (toBase I) 8 k).left = _
    rw [ha]
    exact hcoord k
  exact pulledLinearChartCoordinate_value_of_projectiveVectorPoint
    I c (y k) (hy k) (hc k) U a (t k) hpoint j

/-- A pulled chart coordinate can be evaluated at a point over an extension
field without first changing the coefficient ring of the projective scheme.
The coordinate is the corresponding normalized residue-field coordinate. -/
theorem pulledLinearChartCoordinate_value_of_normalizedPointAt
    {K F : Type u} [Field K] [Field F] [Algebra K F]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (z : CoordinateRing I) (hz : z ∈ grading I 1)
    (x : Fin 4 → F)
    (he : ∀ p ∈ I.toIdeal, p.eval₂ (algebraMap K F) x = 0)
    (hzOne : (Ideal.Quotient.lift I.toIdeal
      (eval₂Hom (algebraMap K F) x) he) z = 1)
    (U : Scheme.{u}) (a : Spec (.of F) ⟶ U)
    (t : U ⟶ Spec (.of (Away (grading I) z)))
    (hpoint : (a ≫ t) ≫ Proj.awayι (grading I) z hz
        (by decide : 0 < 1) =
      linearNormalizedPointAt I x he z hz hzOne)
    (j : Fin 4) :
    a.appTop.hom (pulledLinearChartCoordinate I z hz U t j) =
      (StructureSheaf.globalSectionsIso F).hom (x j) := by
  let chart := Proj.awayι (grading I) z hz (by decide : 0 < 1)
  let g := linearNormalizedPointChartMapAt I x he z hz hzOne
  have hmap : a ≫ t = Spec.map (CommRingCat.ofHom g) := by
    apply (cancel_mono chart).mp
    exact hpoint.trans (by rfl)
  have hvalue := pulledLinearChartCoordinate_value_of_chartMap
    I z hz U a t g hmap j
  rw [linearNormalizedPointChartMapAt_coordinate] at hvalue
  exact hvalue

/-- The preceding extension-field specialization simultaneously for the
eight coordinate lifts on an ordered configuration chart. -/
theorem pulledEightLinearChartCoordinates_value_of_normalizedConfiguration
    {K F : Type u} [Field K] [Field F] [Algebra K F]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (z : CoordinateRing I) (hz : z ∈ grading I 1)
    (x : Fin 8 → Fin 4 → F)
    (he : ∀ k, ∀ p ∈ I.toIdeal,
      p.eval₂ (algebraMap K F) (x k) = 0)
    (hzOne : ∀ k, (Ideal.Quotient.lift I.toIdeal
      (eval₂Hom (algebraMap K F) (x k)) (he k)) z = 1)
    (U : Scheme.{u})
    (i : U ⟶ (AllCharacteristics.orderedFamilyConfigurationOver
      (toBase I) 8).left)
    (A : Spec (.of F) ⟶
      (AllCharacteristics.orderedFamilyConfigurationOver (toBase I) 8).left)
    (a : Spec (.of F) ⟶ U) (ha : a ≫ i = A)
    (t : Fin 8 → (U ⟶ Spec (.of (Away (grading I) z))))
    (ht : ∀ k, t k ≫ Proj.awayι (grading I) z hz
      (by decide : 0 < 1) =
        (i ≫ Over.Hom.left
          (AllCharacteristics.orderedFamilyConfigurationι (toBase I) 8)) ≫
          (AllCharacteristics.orderedFamilyCoordinate (toBase I) 8 k).left)
    (hcoord : ∀ k,
      (A ≫ Over.Hom.left
        (AllCharacteristics.orderedFamilyConfigurationι (toBase I) 8)) ≫
        (AllCharacteristics.orderedFamilyCoordinate (toBase I) 8 k).left =
          linearNormalizedPointAt I (x k) (he k) z hz (hzOne k)) :
    ∀ k j,
      a.appTop.hom (pulledEightLinearChartCoordinates I z hz U t k j) =
        (StructureSheaf.globalSectionsIso F).hom (x k j) := by
  intro k j
  have hpoint : (a ≫ t k) ≫ Proj.awayι (grading I) z hz
      (by decide : 0 < 1) =
      linearNormalizedPointAt I (x k) (he k) z hz (hzOne k) := by
    rw [Category.assoc, ht k]
    change ((a ≫ i) ≫ Over.Hom.left
      (AllCharacteristics.orderedFamilyConfigurationι (toBase I) 8)) ≫
      (AllCharacteristics.orderedFamilyCoordinate (toBase I) 8 k).left = _
    rw [ha]
    exact hcoord k
  exact pulledLinearChartCoordinate_value_of_normalizedPointAt
    I z hz (x k) (he k) (hzOne k) U a (t k) hpoint j

end PfaffianDescent
