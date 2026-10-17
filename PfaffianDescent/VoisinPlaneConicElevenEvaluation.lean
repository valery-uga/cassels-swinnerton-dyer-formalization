import PfaffianDescent.VoisinCubicElevenSelection
import PfaffianDescent.VoisinConicCubicRestrictionKernel
import PfaffianDescent.CubicFiniteSubschemeHyperplane

/-!
# Eleven generic points versus cubic sections containing a plane conic

This is the coordinate-section count in the conic branch of Voisin's middle
Serre argument.  Cubics on the surface that contain a fixed plane conic form
a space of dimension at most twelve.  Eleven suitably selected geometric
points therefore leave at most one such cubic.
-/

noncomputable section

namespace PfaffianDescent

open AlgebraicGeometry MvPolynomial Module
open AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Eleven maximal-rank points leave at most one cubic section containing a
fixed nonzero plane conic on a prime cubic surface. -/
theorem planeConic_cubicElevenSelectedEvaluation_ker_finrank_le_one
    {K : Type u} [Field K] [IsAlgClosed K]
    (p ell q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    (hell : ell.IsHomogeneous 1) (hell0 : ell ≠ 0)
    (hq : q.IsHomogeneous 2) (hq0 : q ≠ 0)
    (hpc : p ∈ Ideal.span ({ell, q} : Set (MvPolynomial (Fin 4) K))) :
    letI : Module.Finite K (grading (equationIdeal p hp) 3) :=
      polynomialQuotientGrade_finite (equationIdeal p hp) 3
    let W := fixedCurveCubicSurfaceSystem p hp
      (planeConicHomogeneousIdeal ell q hell hq)
    finrank K (LinearMap.ker
      (cubicElevenSelectedEvaluation p hp hp0 hprime W)) ≤ 1 := by
  letI : Module.Finite K (grading (equationIdeal p hp) 3) :=
    polynomialQuotientGrade_finite (equationIdeal p hp) 3
  let W := fixedCurveCubicSurfaceSystem p hp
    (planeConicHomogeneousIdeal ell q hell hq)
  have hW : finrank K W ≤ 12 :=
    fixedCurveCubicSurfaceSystem_finrank_le_twelve_of_plane_conic
      p hp hp0 (planeConicHomogeneousIdeal ell q hell hq)
      ⟨ell, hell⟩ ⟨q, hq⟩ hell0 hq0 rfl hpc
  exact cubicElevenSelectedEvaluation_ker_finrank_le_one
    p hp hp0 hprime W hW

/-- Smoothness supplies the primeness hypothesis in the preceding conic
evaluation bound. -/
theorem planeConic_cubicElevenSelectedEvaluation_ker_finrank_le_one_of_smooth
    {K : Type u} [Field K] [IsAlgClosed K]
    (p ell q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (hell : ell.IsHomogeneous 1) (hell0 : ell ≠ 0)
    (hq : q.IsHomogeneous 2) (hq0 : q ≠ 0)
    (hpc : p ∈ Ideal.span ({ell, q} : Set (MvPolynomial (Fin 4) K))) :
    letI : Module.Finite K (grading (equationIdeal p hp) 3) :=
      polynomialQuotientGrade_finite (equationIdeal p hp) 3
    let hprime : (Ideal.span
        ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime :=
      principalIdeal_prime_of_irreducible_cubic p
        (irreducible_of_smooth_homogeneous_cubic_of_field p hp hp0)
    let W := fixedCurveCubicSurfaceSystem p hp
      (planeConicHomogeneousIdeal ell q hell hq)
    finrank K (LinearMap.ker
      (cubicElevenSelectedEvaluation p hp hp0 hprime W)) ≤ 1 := by
  letI : Module.Finite K (grading (equationIdeal p hp) 3) :=
    polynomialQuotientGrade_finite (equationIdeal p hp) 3
  exact planeConic_cubicElevenSelectedEvaluation_ker_finrank_le_one
    p ell q hp hp0
    (principalIdeal_prime_of_irreducible_cubic p
      (irreducible_of_smooth_homogeneous_cubic_of_field p hp hp0))
    hell hell0 hq hq0 hpc

end PfaffianDescent
