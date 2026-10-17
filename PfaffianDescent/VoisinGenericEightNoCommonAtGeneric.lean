import PfaffianDescent.VoisinCanonicalOrderedGenericPoint
import PfaffianDescent.VoisinGenericQuadraticEvaluation
import PfaffianDescent.VoisinProjectiveLinearSystem
import AllCharacteristics.UniversalProjectiveFiniteIncidence

/-! Quadratic avoidance at the integral ordered configuration's generic point. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The fixed eight-dimensional quadratic frame's bad incidence locus on
the ordered configuration scheme. This definition makes sense without
assuming that the ground field is algebraically closed. -/
noncomputable def quadraticEightFixedFrameBadLocus
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [hsep : IsSeparated (hypersurfaceToBase p hp)] :
    Set (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 8).left :=
  projectiveUniversalFiniteIncidenceBadLocus K (Fin 4) 2
    (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 8).hom
    (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 8) K)))
    (fun i => @orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
      (grading (equationIdeal p hp)) _ (hypersurfaceToBase p hp) hsep 8
      (hypersurfaceToAmbient p hp) i)
    (homogeneousFrameToParameters 2
      ((Fintype.equivFin (Monomials (Fin 4) 2)).symm)
      (quadraticEightFrame K) (quadraticEightFrame_linearIndependent K))

/-- One point of the ordered configuration outside the fixed-frame bad
locus forces quadratic avoidance at its generic point, over any field. -/
theorem quadraticEightNoCommon_at_ordered_generic_of_goodPoint
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [hsep : IsSeparated (hypersurfaceToBase p hp)]
    [hint : IsIntegral (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 8).left]
    (hgood : ∃ z : (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 8).left,
      z ∉ quadraticEightFixedFrameBadLocus p hp) :
    QuadraticEightNoCommonResidueFieldEquationAt p hp
      (genericPoint (orderedFamilyConfigurationOver
        (hypersurfaceToBase p hp) 8).left) := by
  let O := (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 8).left
  have havoid : O.fromSpecStalk (genericPoint O)
      (IsLocalRing.closedPoint O.functionField) ∉
      quadraticEightFixedFrameBadLocus p hp := by
    exact genericFunctionField_closedPoint_avoids_projectiveUniversalFiniteIncidence_of_exists
      K (Fin 4) 2
      (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 8).hom
      (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 8) K)))
      (fun i => @orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
        (grading (equationIdeal p hp)) _ (hypersurfaceToBase p hp) hsep 8
        (hypersurfaceToAmbient p hp) i)
      (homogeneousFrameToParameters 2
        ((Fintype.equivFin (Monomials (Fin 4) 2)).symm)
        (quadraticEightFrame K) (quadraticEightFrame_linearIndependent K))
      hgood
  have hgeneric : genericPoint O ∉ quadraticEightFixedFrameBadLocus p hp := by
    simpa only [Scheme.fromSpecStalk_closedPoint] using havoid
  unfold QuadraticEightNoCommonResidueFieldEquationAt
  exact not_exists_common_residueFieldPoints_of_not_mem_projectiveUniversalFiniteIncidenceBadLocus
    K (Fin 4) 2
    (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 8).hom
    (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 8) K)))
    (fun i => @orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
      (grading (equationIdeal p hp)) _ (hypersurfaceToBase p hp) hsep 8
      (hypersurfaceToAmbient p hp) i)
    (homogeneousFrameToParameters 2
      ((Fintype.equivFin (Monomials (Fin 4) 2)).symm)
      (quadraticEightFrame K) (quadraticEightFrame_linearIndependent K))
    hgeneric

theorem quadraticEightNoCommon_at_ordered_generic
    {K : Type u} [Field K] [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hpne : p ≠ 0)
    (hpprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    [IsSeparated (hypersurfaceToBase p hp)]
    [IsIntegral (projectiveConfigurationQuotientOpen
      (grading (equationIdeal p hp))
      (hypersurfaceToBase p hp) 8).toScheme]
    [IsIntegral (cubicConfigurationBase p hp 8)]
    [IsIntegral (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 8).left] :
    QuadraticEightNoCommonResidueFieldEquationAt p hp
      (genericPoint (orderedFamilyConfigurationOver
        (hypersurfaceToBase p hp) 8).left) := by
  obtain ⟨z, hz, hno⟩ :=
    exists_orderedPointOver_genericEight_with_noCommonQuadraticEightEquation
      p hp hpne hpprime
  have hz' : configurationQuotientMap (equationIdeal p hp) 8 z =
      (cubicConfigurationBase p hp 8).fromSpecStalk
        (genericPoint (cubicConfigurationBase p hp 8))
        (IsLocalRing.closedPoint
          (cubicConfigurationBase p hp 8).functionField) := hz
  rw [cubicOrderedPointOverGeneric_eq_generic p hp z hz'] at hno
  exact hno

/-- Quadratic avoidance is independent of which ordered lift over the
generic unordered configuration is used. -/
theorem quadraticEightNoCommon_at_every_generic_ordered_lift
    {K : Type u} [Field K] [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hpne : p ≠ 0)
    (hpprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    [IsSeparated (hypersurfaceToBase p hp)]
    [IsIntegral (projectiveConfigurationQuotientOpen
      (grading (equationIdeal p hp))
      (hypersurfaceToBase p hp) 8).toScheme]
    [IsIntegral (cubicConfigurationBase p hp 8)]
    [IsIntegral (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 8).left]
    (z : (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 8).left)
    (hz : configurationQuotientMap (equationIdeal p hp) 8 z =
      (cubicConfigurationBase p hp 8).fromSpecStalk
        (genericPoint (cubicConfigurationBase p hp 8))
        (IsLocalRing.closedPoint
          (cubicConfigurationBase p hp 8).functionField)) :
    QuadraticEightNoCommonResidueFieldEquationAt p hp z := by
  have hg := quadraticEightNoCommon_at_ordered_generic
    p hp hpne hpprime
  rw [cubicOrderedPointOverGeneric_eq_generic p hp z hz]
  exact hg

/-- The same avoidance result over an arbitrary ground field, conditional
only on one geometric configuration outside the explicit bad locus. The
chosen good point need not lie over a rational point of the ground field. -/
theorem quadraticEightNoCommon_at_every_generic_ordered_lift_of_goodPoint
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [IsSeparated (hypersurfaceToBase p hp)]
    [IsIntegral (projectiveConfigurationQuotientOpen
      (grading (equationIdeal p hp))
      (hypersurfaceToBase p hp) 8).toScheme]
    [IsIntegral (cubicConfigurationBase p hp 8)]
    [IsIntegral (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 8).left]
    (hgood : ∃ w : (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 8).left,
      w ∉ quadraticEightFixedFrameBadLocus p hp)
    (z : (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 8).left)
    (hz : configurationQuotientMap (equationIdeal p hp) 8 z =
      (cubicConfigurationBase p hp 8).fromSpecStalk
        (genericPoint (cubicConfigurationBase p hp 8))
        (IsLocalRing.closedPoint
          (cubicConfigurationBase p hp 8).functionField)) :
    QuadraticEightNoCommonResidueFieldEquationAt p hp z := by
  have hg := quadraticEightNoCommon_at_ordered_generic_of_goodPoint
    p hp hgood
  rw [cubicOrderedPointOverGeneric_eq_generic p hp z hz]
  exact hg

end PfaffianDescent
