import PfaffianDescent.VoisinGenericSixteenFixedCurveLowDegree
import PfaffianDescent.QuarticTwistedCubicAlgebraicQuadraticPiece

/-!
# Generic sixteen points avoid geometrically standard twisted cubics

The intrinsic twisted-cubic ideal theorem supplies quadratic generation.
The generic sixteen-point avoidance theorem then rules out intersection with
any such twisted cubic contained in the cubic surface.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A geometrically standard twisted cubic on the coefficient-changed cubic
surface cannot meet the generic rank-sixteen configuration. -/
theorem cubicConfigurationGenericSixteen_misses_geometricallyStandardTwistedCubic
    {K : Type u} [Field K] [IsAlgClosed K]
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    (hcubic_ne : cubic ≠ 0)
    (hcubic_prime :
      (Ideal.span ({cubic} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    [hsep : IsSeparated (hypersurfaceToBase cubic hcubic)]
    [hlft : LocallyOfFiniteType (hypersurfaceToBase cubic hcubic)]
    [hint : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16).toScheme]
    [hordered : IsIntegral
      (orderedFamilyConfigurationOver (hypersurfaceToBase cubic hcubic) 16).left]
    [hbase : IsIntegral (cubicConfigurationBase cubic hcubic 16)]
    [Infinite (cubicConfigurationBase cubic hcubic 16).functionField]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase cubic hcubic 16).functionField)
    (ha : Spec.map a = cubicConfigurationGenericBaseMap cubic hcubic 16 ≫
      cubicConfigurationToBase cubic hcubic 16)
    {m : ℕ} (e : Fin m ≃ Monomials (Fin 4) 2)
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4)
      (cubicConfigurationBase cubic hcubic 16).functionField))
    (hCp : cubic.map a.hom ∈ C.toIdeal)
    (hgeo : QuarticNet.GeometricallyStandardTwistedCubic C) :
    IsEmpty (pullback
      (homogeneousFixedCurveToCubic
        (cubic.map a.hom) (hcubic.map a.hom) C hCp)
      (cubicConfigurationGenericFiniteSubscheme
        cubic hcubic 16 a ha).val.subschemeι : Scheme.{u}) := by
  exact cubicConfigurationGenericSixteen_misses_quadraticallyGeneratedCurve
    cubic hcubic hcubic_ne hcubic_prime a ha e C hCp
      (QuarticNet.quadraticPieceGenerates_of_geometricallyStandardTwistedCubic hgeo)

end PfaffianDescent
