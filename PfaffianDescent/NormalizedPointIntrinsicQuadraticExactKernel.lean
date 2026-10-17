import PfaffianDescent.NormalizedPointIntrinsicQuadraticRestriction

/- SOURCE ONLY / UNVERIFIED. Exact full intrinsic system of the SAME
normalized finite coordinate algebra; square-zero directions are retained. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem normalizedFiniteEquationPoint_intrinsicQuadratics_eq_evaluationKernel
    {K A : Type u} [Field K] [CommRing A] [Algebra K A] [Module.Finite K A]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (x : Fin 4 → A) (ell : MvPolynomial (Fin 4) K)
    (hell : ell.IsHomogeneous 1) (hOne : ell.eval₂ (algebraMap K A) x = 1)
    (he : ∀ p ∈ I.toIdeal, p.eval₂ (algebraMap K A) x = 0)
    (j : Fin 4) (u : Aˣ) (hu : (u : A) = x j) :
    intrinsicFullQuadraticSystem
      (normalizedFiniteEquationPoint I x ell hell hOne he ≫ quotientProjMap I) =
        homogeneousVanishingPolynomialSubmodule x 2 := by
  apply le_antisymm
  · intro Q hQ
    apply (mem_homogeneousVanishingPolynomialSubmodule_iff x 2 Q).mpr
    exact ⟨hQ.1,
      linearNormalizedPoint_intrinsicQuadratics_evaluation_zero_of_unit_coordinate
        I x ell hell hOne he j u hu Q hQ⟩
  · exact normalizedFiniteEquationPoint_evaluationQuadrics_le_intrinsic
      I x ell hell hOne he

end PfaffianDescent
