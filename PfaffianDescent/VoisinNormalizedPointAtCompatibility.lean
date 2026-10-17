import PfaffianDescent.VoisinProjectivePointIntrinsicIdeal

/-! The explicit chart-element and linear-form normalized points agree. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- When the chosen degree-one chart element comes from the normalizing
linear form, the `At` construction is the ordinary normalized point. -/
theorem linearNormalizedPointAt_mk_eq_linearNormalizedPoint
    {K A : Type u} [Field K] [CommRing A] [Algebra K A]
    {σ : Type} [Finite σ]
    (I : HomogeneousIdeal (homogeneousSubmodule σ K))
    (x : σ → A)
    (he : ∀ p ∈ I.toIdeal, p.eval₂ (algebraMap K A) x = 0)
    (ell : MvPolynomial σ K) (hell : ell.IsHomogeneous 1)
    (hzOne : (Ideal.Quotient.lift I.toIdeal
      (eval₂Hom (algebraMap K A) x) he)
        (Ideal.Quotient.mk I.toIdeal ell) = 1) :
    linearNormalizedPointAt I x he
      (Ideal.Quotient.mk I.toIdeal ell)
      (polynomial_class_mem_grading I ell hell) hzOne =
    linearNormalizedPoint I x ell hell hzOne he := by
  rfl

end PfaffianDescent
