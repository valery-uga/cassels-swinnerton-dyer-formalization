import PfaffianDescent.VoisinProjectiveLinearSystem
import PfaffianDescent.CubicSurfaceSectionDimensions
import PfaffianDescent.VoisinVeryAmpleCubicSections

/-!
# Generic sixteen-point fixed-component dimension

The generic incidence theorem excludes a fixed homogeneous system of at most
sixteen sections that contains the generic sixteen-point configuration.
Consequently a fixed system containing that configuration has at least
seventeen sections.  For cubic sections on a cubic surface, a complementary
three-dimensional moving system then exceeds the nineteen-dimensional
ambient system whenever their sum satisfies the usual properness bound.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics AllCharacteristics.UniversalHomogeneous
open HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The generic unordered length-sixteen configuration belongs to the image
of the universal incidence of a fixed homogeneous frame. -/
noncomputable def GenericSixteenConfigurationInHomogeneousFrameIncidence
    {K : Type u} [Field K]
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    (d : ℕ) {m n : ℕ}
    (e : Fin m ≃ Monomials (Fin 4) d)
    (q : Fin n → homogeneousSubmodule (Fin 4) K d)
    (hqliq : LinearIndependent K q)
    [hsep : IsSeparated (hypersurfaceToBase cubic hcubic)]
    [hint : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16).toScheme] : Prop :=
  (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
    (hypersurfaceToBase cubic hcubic) 16).toScheme.fromSpecStalk
    (genericPoint
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16).toScheme)
    (IsLocalRing.closedPoint
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16).toScheme.functionField) ∈
    projectiveConfigurationQuotientMap (grading (equationIdeal cubic hcubic))
      (hypersurfaceToBase cubic hcubic) 16 ''
      projectiveUniversalFiniteIncidenceBadLocus K (Fin 4) d
        (orderedFamilyConfigurationOver (hypersurfaceToBase cubic hcubic) 16).hom
        (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)))
        (fun i => @orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
          (grading (equationIdeal cubic hcubic)) _
          (hypersurfaceToBase cubic hcubic) hsep 16
          (hypersurfaceToAmbient cubic hcubic) i)
        (homogeneousFrameToParameters d e q hqliq)

/-- A fixed homogeneous system containing the generic sixteen-point
configuration has at least seventeen independent sections. -/
theorem seventeen_le_finrank_of_genericSixteenConfigurationInHomogeneousFrameIncidence
    {K : Type u} [Field K] [IsAlgClosed K]
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    (hcubic_ne : cubic ≠ 0)
    (hcubic_prime : (Ideal.span ({cubic} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    {d m n : ℕ} (hd : 0 < d)
    (W : Submodule K (MvPolynomial (Fin 4) K)) [FiniteDimensional K W]
    (hhom : ∀ z ∈ W, z.IsHomogeneous d)
    (hseparate : ∀ z ∈ W,
      z ∈ Ideal.span ({cubic} : Set (MvPolynomial (Fin 4) K)) → z = 0)
    (qW : Fin n → W) (q : Fin n → homogeneousSubmodule (Fin 4) K d)
    (hq : ∀ j, (qW j : MvPolynomial (Fin 4) K) = (q j).1)
    (hqli : LinearIndependent K qW) (hqliq : LinearIndependent K q)
    (hn : Module.finrank K W = n)
    (e : Fin m ≃ Monomials (Fin 4) d)
    [hsep : IsSeparated (hypersurfaceToBase cubic hcubic)]
    [hlft : LocallyOfFiniteType (hypersurfaceToBase cubic hcubic)]
    [hint : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16).toScheme]
    (hinc : GenericSixteenConfigurationInHomogeneousFrameIncidence
      cubic hcubic d e q hqliq) :
    17 ≤ Module.finrank K W := by
  by_contra h
  have hdim : Module.finrank K W ≤ 16 := by omega
  have havoid :=
    genericFunctionField_closedPoint_avoids_sixteen_cubicConfigurationQuotientHomogeneousFrameFiniteIncidence_of_submodule_evaluation
      cubic hcubic hcubic_ne hcubic_prime hd W hhom hseparate hdim
        qW q hq hqli hqliq hn e
  exact havoid (by
    simpa only [GenericSixteenConfigurationInHomogeneousFrameIncidence] using hinc)

/-- The meeting branch for sixteen generic points: seventeen fixed sections
and three moving sections cannot fit in the nineteen cubic sections of a
cubic surface when their dimensions satisfy the properness bound. -/
theorem cubicSurface_degreeSixteen_fixedComponent_meets_genericIncidence_contradiction
    {K : Type u} [Field K] [IsAlgClosed K]
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    (hcubic_ne : cubic ≠ 0)
    (hcubic_prime : (Ideal.span ({cubic} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    {d m n : ℕ} (hd : 0 < d)
    (fixed : Submodule K (MvPolynomial (Fin 4) K)) [FiniteDimensional K fixed]
    (hhom : ∀ z ∈ fixed, z.IsHomogeneous d)
    (hseparate : ∀ z ∈ fixed,
      z ∈ Ideal.span ({cubic} : Set (MvPolynomial (Fin 4) K)) → z = 0)
    (qW : Fin n → fixed) (q : Fin n → homogeneousSubmodule (Fin 4) K d)
    (hq : ∀ j, (qW j : MvPolynomial (Fin 4) K) = (q j).1)
    (hqli : LinearIndependent K qW) (hqliq : LinearIndependent K q)
    (hn : Module.finrank K fixed = n)
    (e : Fin m ≃ Monomials (Fin 4) d)
    [hsep : IsSeparated (hypersurfaceToBase cubic hcubic)]
    [hlft : LocallyOfFiniteType (hypersurfaceToBase cubic hcubic)]
    [hint : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16).toScheme]
    (hinc : GenericSixteenConfigurationInHomogeneousFrameIncidence
      cubic hcubic d e q hqliq)
    (movingDim : ℕ) (hmove : 3 ≤ movingDim)
    (hproper : Module.finrank K fixed + movingDim ≤
      Module.finrank K (grading (equationIdeal cubic hcubic) 3)) : False := by
  have hfixed : 17 ≤ Module.finrank K fixed :=
    seventeen_le_finrank_of_genericSixteenConfigurationInHomogeneousFrameIncidence
      cubic hcubic hcubic_ne hcubic_prime hd fixed hhom hseparate
        qW q hq hqli hqliq hn e hinc
  rw [cubicSurface_grade_three_finrank cubic hcubic hcubic_ne] at hproper
  omega

/-- The disjoint branch: a moving cubic system containing the generic
sixteen-point configuration has at least seventeen sections, while vanishing
at three distinct points of a fixed curve leaves at most sixteen. -/
theorem cubicSurface_degreeSixteen_fixedComponent_disjoint_genericIncidence_contradiction
    {K : Type u} [Field K] [IsAlgClosed K]
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    (hcubic_ne : cubic ≠ 0)
    (hcubic_prime : (Ideal.span ({cubic} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    (moving : Submodule K (MvPolynomial (Fin 4) K))
    [FiniteDimensional K moving]
    (hhom : ∀ z ∈ moving, z.IsHomogeneous 3)
    (hseparate : ∀ z ∈ moving,
      z ∈ Ideal.span ({cubic} : Set (MvPolynomial (Fin 4) K)) → z = 0)
    {m n : ℕ}
    (qW : Fin n → moving) (q : Fin n → homogeneousSubmodule (Fin 4) K 3)
    (hq : ∀ j, (qW j : MvPolynomial (Fin 4) K) = (q j).1)
    (hqli : LinearIndependent K qW) (hqliq : LinearIndependent K q)
    (hn : Module.finrank K moving = n)
    (e : Fin m ≃ Monomials (Fin 4) 3)
    [hsep : IsSeparated (hypersurfaceToBase cubic hcubic)]
    [hlft : LocallyOfFiniteType (hypersurfaceToBase cubic hcubic)]
    [hint : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16).toScheme]
    (hinc : GenericSixteenConfigurationInHomogeneousFrameIncidence
      cubic hcubic 3 e q hqliq)
    (x : Fin 3 → cubicSurfaceAffinePoints cubic)
    (hdir : ∀ i j, i ≠ j → ∀ a : K, a • (x i).1 ≠ (x j).1)
    (hvan : ∀ z : moving, ∀ i,
      MvPolynomial.aeval (x i).1 z.1 = 0) : False := by
  have hgeneric : 17 ≤ Module.finrank K moving :=
    seventeen_le_finrank_of_genericSixteenConfigurationInHomogeneousFrameIncidence
      cubic hcubic hcubic_ne hcubic_prime (by decide)
        moving hhom hseparate qW q hq hqli hqliq hn e hinc
  have hbound : Module.finrank K moving ≤ 16 :=
    homogeneousCubicPolynomialSubmodule_finrank_le_sixteen_of_pointwise_vanishing
      cubic hcubic hcubic_ne x hdir moving hhom hseparate hvan
  omega

end PfaffianDescent
