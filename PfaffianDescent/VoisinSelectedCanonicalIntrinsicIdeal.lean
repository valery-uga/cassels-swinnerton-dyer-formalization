import PfaffianDescent.VoisinSelectedCanonicalChartRatios
import PfaffianDescent.VoisinIntrinsicIdealRatioFamilies
import PfaffianDescent.VoisinNormalizedVectorNonzero

/-! Intrinsic-ideal equality from selected/canonical marked-point equality. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Two families of normalized vectors over a common residue field have
the same intrinsic eight-point ideal when the selected hypersurface points
and the coefficient-changed canonical quotient points have the same
labeled ambient images. The two normalizing forms and ground fields may
differ. -/
theorem selectedCanonical_intrinsicEightPointTripleHomogeneousIdeal_eq
    {K Q F : Type u} [Field K] [Field Q] [Field F]
    [Algebra K F] [Algebra Q F]
    (f : K →+* Q)
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (pF : MvPolynomial (Fin 4) F) (hpF : pF.IsHomogeneous 3)
    (x y : Fin 8 → Fin 4 → F)
    (ellx : MvPolynomial (Fin 4) K)
    (hellx : ellx.IsHomogeneous 1)
    (hex : ∀ k, ∀ q ∈ (equationIdeal p hp).toIdeal,
      q.eval₂ (algebraMap K F) (x k) = 0)
    (hxOne : ∀ k, (Ideal.Quotient.lift (equationIdeal p hp).toIdeal
      (eval₂Hom (algebraMap K F) (x k)) (hex k))
        (Ideal.Quotient.mk (equationIdeal p hp).toIdeal ellx) = 1)
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) Q))
    (elly : MvPolynomial (Fin 4) Q)
    (helly : elly.IsHomogeneous 1)
    (hey : ∀ k, ∀ q ∈ I.toIdeal,
      q.eval₂ (algebraMap Q F) (y k) = 0)
    (hyOne : ∀ k, (Ideal.Quotient.lift I.toIdeal
      (eval₂Hom (algebraMap Q F) (y k)) (hey k))
        (Ideal.Quotient.mk I.toIdeal elly) = 1)
    (hpoint : ∀ k,
      (linearNormalizedPointAt I (y k) (hey k)
        (Ideal.Quotient.mk I.toIdeal elly)
        (polynomial_class_mem_grading I elly helly) (hyOne k) ≫
          quotientProjMap I) ≫ ambientCoefficientMap f =
      linearNormalizedPointAt (equationIdeal p hp) (x k) (hex k)
        (Ideal.Quotient.mk (equationIdeal p hp).toIdeal ellx)
        (polynomial_class_mem_grading (equationIdeal p hp) ellx hellx)
        (hxOne k) ≫ hypersurfaceToAmbient p hp) :
    intrinsicEightPointTripleHomogeneousIdeal pF hpF y =
      intrinsicEightPointTripleHomogeneousIdeal pF hpF x := by
  classical
  let j : Fin 8 → Fin 4 := fun k =>
    (exists_nonzero_coordinate_of_linear_normalization
      ellx hellx (x k) (hxOne k)).choose
  have hxj : ∀ k, x k (j k) ≠ 0 := by
    intro k
    exact (exists_nonzero_coordinate_of_linear_normalization
      ellx hellx (x k) (hxOne k)).choose_spec
  apply intrinsicEightPointTripleHomogeneousIdeal_eq_of_ratioFamilies
    pF hpF x y j hxj
  intro k i
  exact selectedCanonical_normalizedCoordinateRatios_eq
    f p hp (x k) ellx hellx (hex k) (hxOne k)
    I (y k) elly helly (hey k) (hyOne k)
    (hpoint k) (j k) (hxj k) i

end PfaffianDescent
