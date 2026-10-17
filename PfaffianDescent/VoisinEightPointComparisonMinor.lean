import PfaffianDescent.VoisinEightPointComparisonData
import PfaffianDescent.VoisinQuadraticMinorRatioFamilies

/-! Matching selected and canonical marked points have matching
quadratic evaluation minor invertibility. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem EightPointNormalizedComparison.minor_isUnit_iff
    {K Q F : Type u} [Field K] [Field Q] [Field F]
    [Algebra K F] [Algebra Q F]
    (f : K →+* Q)
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) Q))
    (d : EightPointNormalizedComparison f p hp I)
    (m : Fin 8 ↪ Monomials (Fin 4) 2) :
    IsUnit (eightPointQuadraticEvaluationMinor (R := F) m d.y).det ↔
      IsUnit (eightPointQuadraticEvaluationMinor (R := F) m d.x).det := by
  classical
  let j : Fin 8 → Fin 4 := fun k =>
    (exists_nonzero_coordinate_of_linear_normalization
      d.ellx d.hellx (d.x k) (d.hxOne k)).choose
  have hxj : ∀ k, d.x k (j k) ≠ 0 := by
    intro k
    exact (exists_nonzero_coordinate_of_linear_normalization
      d.ellx d.hellx (d.x k) (d.hxOne k)).choose_spec
  apply eightPointQuadraticEvaluationMinor_isUnit_det_iff_of_ratioFamilies
    m d.x d.y j hxj
  intro k i
  exact selectedCanonical_normalizedCoordinateRatios_eq
    f p hp (d.x k) d.ellx d.hellx (d.hex k) (d.hxOne k)
    I (d.y k) d.elly d.helly (d.hey k) (d.hyOne k)
    (d.hpoint k) (j k) (hxj k) i

end PfaffianDescent
