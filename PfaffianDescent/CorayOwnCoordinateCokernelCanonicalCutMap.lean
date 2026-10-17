import PfaffianDescent.CorayOwnPositiveCoordinateCokernelHZero
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualPositiveGradedPullbackHom
import PfaffianDescent.HomogeneousQuotientMap

/-! SOURCE ONLY. A canonical comparison from the ACTUAL coordinate
multiplication cokernel to the actual whole coordinate-cut twist pushforward.
Its projection is the existing actual graded restriction. No Iso/kernel/rank
comparison certificate is supplied; invertibility is not yet asserted. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AllCharacteristics AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Multiplication by the zero homogeneous element is the zero native sheaf
morphism, proved on every actual section and every projective point. -/
theorem positiveMulHomogeneous_zero_nativeCut
    {A ρ : Type u} [CommRing A] [SetLike ρ A] [AddSubgroupClass ρ A]
    (𝒜 : ℕ → ρ) [GradedRing 𝒜] (d m : ℕ) :
    positiveMulHomogeneous 𝒜 (0 : 𝒜 d) m = 0 := by
  ext U z
  apply Subtype.ext
  funext x
  change algebraMap A (PositiveFiber 𝒜 x.1) (0 : A) * z.1 x = 0
  rw [map_zero, zero_mul]

/-- The SAME coordinate vanishes in the literal WHOLE coordinate cut.
This uses membership in the whole equation ideal, without taking a radical. -/
theorem ownCoordinateCut_gradedQuotient_coordinate_eq_zero
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K)) (j : Fin 4) :
    gradedQuotientMap C
      (C ⊔ equationIdeal (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X K j))
      le_sup_left (coordinate C j) = 0 := by
  rw [gradedQuotientMap_coordinate]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  have hx : MvPolynomial.X j ∈
      (equationIdeal (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X K j)).toIdeal :=
    Ideal.subset_span (Set.mem_singleton _)
  exact (show (equationIdeal (MvPolynomial.X j)
    (MvPolynomial.isHomogeneous_X K j)).toIdeal ≤
      (C ⊔ equationIdeal (MvPolynomial.X j)
        (MvPolynomial.isHomogeneous_X K j)).toIdeal from le_sup_right) hx

/-- Literal positive-twist restriction along the actual graded coordinate
quotient. Its target is the whole cut's actual intrinsic twist pushforward. -/
def ownCoordinateCutPositiveRestriction
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (j : Fin 4) (m : ℕ) :
    positiveSheafOfModules (grading C) (m + 1) ⟶
      (Scheme.Modules.pushforward (schemeQuotientMap C
        (C ⊔ equationIdeal (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X K j))
        le_sup_left)).obj
        (positiveSheafOfModules (grading
          (C ⊔ equationIdeal (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X K j)))
          (m + 1)) :=
  gradedRingHomPositiveTwistToPushforward (grading C)
    (grading (C ⊔ equationIdeal (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X K j)))
    (gradedQuotientMap C
      (C ⊔ equationIdeal (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X K j)) le_sup_left)
    (gradedSurjective_irrelevant_le _ (gradedQuotientMap_surjective C
      (C ⊔ equationIdeal (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X K j)) le_sup_left))
    (m + 1)

/-- Restriction kills the SAME coordinate multiplication, by actual graded
multiplication naturality and the literal quotient coordinate equality. -/
theorem ownCoordinateCutPositiveRestriction_comp_coordinate_zero
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (j : Fin 4) (m : ℕ) :
    ownPositiveCoordinateMultiplication C j m ≫ ownCoordinateCutPositiveRestriction C j m = 0 := by
  let D := C ⊔ equationIdeal (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X K j)
  let f := gradedQuotientMap C D le_sup_left
  let hf := gradedSurjective_irrelevant_le f (gradedQuotientMap_surjective C D le_sup_left)
  let s : grading C 1 := ⟨coordinate C j, coordinate_mem C j⟩
  have hs : (⟨f s, f.2 s.2⟩ : grading D 1) = 0 := by
    apply Subtype.ext
    exact ownCoordinateCut_gradedQuotient_coordinate_eq_zero C j
  have h := gradedRingHomPositiveTwistToPushforward_positiveMulHomogeneous
    (grading C) (grading D) f hf s m
  rw [hs, positiveMulHomogeneous_zero_nativeCut, Functor.map_zero, comp_zero] at h
  exact h

/-- The actual cokernel comparison is constructed by the universal property;
it is not an extra geometric outcome hypothesis. -/
def ownCoordinateCokernelToWholeCutPositiveTwist
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (j : Fin 4) (m : ℕ) :
    cokernel (ownPositiveCoordinateMultiplication C j m) ⟶
      (Scheme.Modules.pushforward (schemeQuotientMap C
        (C ⊔ equationIdeal (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X K j))
        le_sup_left)).obj
        (positiveSheafOfModules (grading
          (C ⊔ equationIdeal (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X K j)))
          (m + 1)) :=
  cokernel.desc (ownPositiveCoordinateMultiplication C j m)
    (ownCoordinateCutPositiveRestriction C j m)
    (ownCoordinateCutPositiveRestriction_comp_coordinate_zero C j m)

/-- The entire native cokernel projection followed by the canonical comparison
is EXACTLY the actual graded restriction, preserving the whole map. -/
theorem ownCoordinateCokernelToWholeCutPositiveTwist_projection
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (j : Fin 4) (m : ℕ) :
    cokernel.π (ownPositiveCoordinateMultiplication C j m) ≫
      ownCoordinateCokernelToWholeCutPositiveTwist C j m =
        ownCoordinateCutPositiveRestriction C j m := by
  exact cokernel.π_desc _ _ _

end PfaffianDescent.Coray
