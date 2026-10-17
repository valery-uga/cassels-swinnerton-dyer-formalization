import PfaffianDescent.VoisinFixedCurveCubicSurfaceRankThree
import PfaffianDescent.VoisinSeparatedCubicSystemRank

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The fixed-curve cubic system of the generic sixteen-point scheme admits
a polynomial lift of rank at most three, separated from the surface equation. -/
theorem exists_cubicConfigurationGenericSixteen_fixedCurve_separatedCubicSystem_rank_le_three
    {K : Type u} [Field K] [IsAlgClosed K]
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    (hcubic_ne : cubic ≠ 0)
    (hcubic_prime : (Ideal.span ({cubic} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    [hsep : IsSeparated (hypersurfaceToBase cubic hcubic)]
    [hlft : LocallyOfFiniteType (hypersurfaceToBase cubic hcubic)]
    [hint : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16).toScheme]
    [hbase : IsIntegral (cubicConfigurationBase cubic hcubic 16)]
    [Infinite (cubicConfigurationBase cubic hcubic 16).functionField]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase cubic hcubic 16).functionField)
    (ha : Spec.map a = cubicConfigurationGenericBaseMap cubic hcubic 16 ≫
      cubicConfigurationToBase cubic hcubic 16)
    {m : ℕ} (e : Fin m ≃ Monomials (Fin 4) 3)
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4)
      (cubicConfigurationBase cubic hcubic 16).functionField))
    (hCp : cubic.map a.hom ∈ C.toIdeal)
    (h : (cubicConfigurationGenericFiniteSubscheme
      cubic hcubic 16 a ha).val.subscheme ⟶ scheme C)
    (hfac : h ≫ homogeneousFixedCurveToCubic
        (cubic.map a.hom) (hcubic.map a.hom) C hCp =
      (cubicConfigurationGenericFiniteSubscheme
        cubic hcubic 16 a ha).val.subschemeι) :
    let Q := cubicConfigurationBase cubic hcubic 16
    ∃ W : Submodule Q.functionField
        (homogeneousSubmodule (Fin 4) Q.functionField 3),
      W ≤ homogeneousIdealPiece C 3 ∧
      (∀ q ∈ W,
        q.1 ∈ Ideal.span ({cubic.map a.hom} : Set
          (MvPolynomial (Fin 4) Q.functionField)) → q = 0) ∧
      W.map (cubicSurfaceHomogeneousCoordinateProjection
        (cubic.map a.hom) (hcubic.map a.hom) 3) =
        fixedCurveCubicSurfaceSystem
          (cubic.map a.hom) (hcubic.map a.hom) C ∧
      finrank Q.functionField W ≤ 3 := by
  dsimp only
  have hthree :=
    cubicConfigurationGenericSixteen_fixedCurve_cubicSurfaceSystem_finrank_le_three
      cubic hcubic hcubic_ne hcubic_prime a ha e C hCp h hfac
  exact exists_fixedCurveCubicSystem_separated_of_system_finrank_le
    (cubic.map a.hom) (hcubic.map a.hom) C 3 hthree

end PfaffianDescent
