import PfaffianDescent.VoisinDegreeEightFixedCurveSections

/-!
# The moving-class obstruction in the disjoint fixed-curve branch

Let `C` be a fixed curve of a quadratic system on a cubic surface.  The
moving system has class `2H - C`; its sections are not, by themselves,
quadratic sections.  Multiplication by the defining section of `C` gives the
relevant map from that moving space into quadratic sections.  This file
states the disjoint-branch contradiction using precisely such a map.

The remaining geometric work is to construct this multiplication map from
the fixed Cartier divisor and prove maximal-rank interpolation of the moving
class at the generic eight-point configuration.  The pointwise formulation
also requires two geometric points of `C`; the prime-ideal formulation below
uses an existing algebraic-closure argument to remove that requirement.
Generic maximal rank is not automatic when the moving class itself varies
with the eight points.  In particular, no fixed ambient quadratic frame is
inferred from descent of the Picard class.
-/

namespace PfaffianDescent

open MvPolynomial Module
open AllCharacteristics.HomogeneousProjective

universe u v

variable {K : Type u} [Field K]

attribute [local instance] MvPolynomial.gradedAlgebra

set_option linter.style.haveILetI false in
/-- A section space for the moving class `2H-C` cannot have a nonzero
section vanishing at eight independently imposed points if multiplication
by `C` embeds it in the quadratic system and the image vanishes at two
distinct projective points of `C`.  The abstract space `V` is deliberately
separate from the space of ambient quadrics. -/
theorem cubicSurface_degreeEight_disjoint_contradiction_of_movingClassMultiplication
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    {V : Type v} [AddCommGroup V] [Module K V]
    (mulC : V →ₗ[K] grading (equationIdeal p hp) 2)
    (hmulC : Function.Injective mulC)
    (ev : V →ₗ[K] (Fin 8 → K))
    (heval : Function.Surjective ev)
    (hsection : ∃ s : V, s ≠ 0 ∧ ev s = 0)
    (x y : cubicSurfaceAffinePoints p)
    (hdir : ∀ a : K, y.1 ≠ a • x.1)
    (hvan : ∀ s : V,
      cubicSurfaceCoordinatePointEvaluation p hp (mulC s) x = 0 ∧
      cubicSurfaceCoordinatePointEvaluation p hp (mulC s) y = 0) : False := by
  letI : Module.Finite K (grading (equationIdeal p hp) 2) :=
    Module.Finite.of_surjective
      (cubicSurfaceHomogeneousCoordinateProjection p hp 2)
      (cubicSurfaceHomogeneousCoordinateProjection_surjective p hp 2)
  letI : Module.Finite K V := Module.Finite.of_injective mulC hmulC
  have hnine : 9 ≤ finrank K V := by
    simpa using
      succ_le_finrank_of_surjective_evaluation_with_nonzero_kernel
        (K := K) (V := V) 8 ev heval hsection
  have hvanRange : ∀ q : LinearMap.range mulC,
      cubicSurfaceCoordinatePointEvaluation p hp q.1 x = 0 ∧
      cubicSurfaceCoordinatePointEvaluation p hp q.1 y = 0 := by
    intro q
    obtain ⟨s, hs⟩ := q.2
    simpa only [hs] using hvan s
  have height : finrank K (LinearMap.range mulC) ≤ 8 :=
    cubicSurfaceQuadraticSubmodule_finrank_le_eight_of_pointwise_vanishing
      p hp hne x y hdir (LinearMap.range mulC) hvanRange
  rw [LinearMap.finrank_range_of_inj hmulC] at height
  omega

/-- Maximal-rank interpolation is enough in the preceding theorem: the
nonzero kernel supplied by the moving pencil rules out injectivity, so
maximal rank forces surjectivity onto the eight evaluation coordinates. -/
theorem cubicSurface_degreeEight_disjoint_contradiction_of_movingClassMaximalRank
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    {V : Type v} [AddCommGroup V] [Module K V]
    (mulC : V →ₗ[K] grading (equationIdeal p hp) 2)
    (hmulC : Function.Injective mulC)
    (ev : V →ₗ[K] (Fin 8 → K))
    (hmax : Function.Injective ev ∨ Function.Surjective ev)
    (hsection : ∃ s : V, s ≠ 0 ∧ ev s = 0)
    (x y : cubicSurfaceAffinePoints p)
    (hdir : ∀ a : K, y.1 ≠ a • x.1)
    (hvan : ∀ s : V,
      cubicSurfaceCoordinatePointEvaluation p hp (mulC s) x = 0 ∧
      cubicSurfaceCoordinatePointEvaluation p hp (mulC s) y = 0) : False := by
  have heval : Function.Surjective ev := by
    rcases hmax with hinj | hsurj
    · obtain ⟨s, hs, hzero⟩ := hsection
      exact (hs (hinj (by simpa using hzero))).elim
    · exact hsurj
  exact cubicSurface_degreeEight_disjoint_contradiction_of_movingClassMultiplication
    p hp hne mulC hmulC ev heval hsection x y hdir hvan

set_option linter.style.haveILetI false in
/-- The disjoint-curve argument with the fixed curve represented by a
height-two homogeneous prime.  Multiplication by its defining section must
land in the quadratic ideal of `C`; the existing arbitrary-field dimension
bound for that ideal removes the need to find rational points on `C`. -/
theorem degreeEight_disjoint_contradiction_of_primeCurveMovingClassMultiplication
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hprime : C.toIdeal.IsPrime) (hheight : C.toIdeal.height = 2)
    {V : Type v} [AddCommGroup V] [Module K V]
    (mulC : V →ₗ[K] fixedCurveQuadraticPolynomialSystem C)
    (hmulC : Function.Injective mulC)
    (ev : V →ₗ[K] (Fin 8 → K))
    (heval : Function.Surjective ev)
    (hsection : ∃ s : V, s ≠ 0 ∧ ev s = 0) : False := by
  letI : Module.Finite K V := Module.Finite.of_injective mulC hmulC
  have hnine : 9 ≤ finrank K V := by
    simpa using
      succ_le_finrank_of_surjective_evaluation_with_nonzero_kernel
        (K := K) (V := V) 8 ev heval hsection
  have height : finrank K V ≤ 8 := by
    calc
      finrank K V = finrank K (LinearMap.range mulC) :=
        (LinearMap.finrank_range_of_inj hmulC).symm
      _ ≤ finrank K (fixedCurveQuadraticPolynomialSystem C) := by
        simpa using (Submodule.finrank_mono
          (le_top : LinearMap.range mulC ≤ ⊤))
      _ ≤ 8 :=
        fixedCurveQuadraticPolynomialSystem_finrank_le_eight_of_prime_height_two_arbitrary_field
          C hprime hheight
  omega

/-- A fixed moving class with generic maximal-rank evaluation cannot have
a nonzero member through eight generic points if its fixed multiplier lands
in the quadratic ideal of a height-two prime curve. -/
theorem degreeEight_disjoint_contradiction_of_primeCurveMovingClassMaximalRank
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hprime : C.toIdeal.IsPrime) (hheight : C.toIdeal.height = 2)
    {V : Type v} [AddCommGroup V] [Module K V]
    (mulC : V →ₗ[K] fixedCurveQuadraticPolynomialSystem C)
    (hmulC : Function.Injective mulC)
    (ev : V →ₗ[K] (Fin 8 → K))
    (hmax : Function.Injective ev ∨ Function.Surjective ev)
    (hsection : ∃ s : V, s ≠ 0 ∧ ev s = 0) : False := by
  have heval : Function.Surjective ev := by
    rcases hmax with hinj | hsurj
    · obtain ⟨s, hs, hzero⟩ := hsection
      exact (hs (hinj (by simpa using hzero))).elim
    · exact hsurj
  exact degreeEight_disjoint_contradiction_of_primeCurveMovingClassMultiplication
    C hprime hheight mulC hmulC ev heval hsection

end PfaffianDescent
