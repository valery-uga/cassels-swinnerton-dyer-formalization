import AllCharacteristics.FiniteSchemeBaseChangeRank
import AllCharacteristics.ProjectiveBaseChange

/-!
# Finite rank under projective coefficient extension

This specializes the general finite-scheme base-change rank theorem to a
homogeneous projective quotient.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace AllCharacteristics
namespace HomogeneousProjective

universe u

variable {k K : Type u} {σ : Type} [Field k] [Field K] [Algebra k K]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The finite rank of a homogeneous projective scheme is unchanged after
extending its coefficient field. -/
theorem projective_finiteSchemeRank_baseChange
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ k))
    (J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K))
    (hIJ : I.toIdeal.map (MvPolynomial.map (algebraMap k K)) = J.toIdeal)
    [IsFinite (toBase I)] [IsFinite (toBase J)] :
    finiteSchemeRank (toBase I) = finiteSchemeRank (toBase J) := by
  apply finiteSchemeRank_eq_of_field_baseChange (toBase I)
    (Spec.map (CommRingCat.ofHom (algebraMap k K))) (toBase J)
    (projectiveBaseChangeIso (algebraMap k K) I J hIJ)
  exact projectiveBaseChangeIso_hom_snd (algebraMap k K) I J hIJ

end HomogeneousProjective
end AllCharacteristics
