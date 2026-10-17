import PfaffianDescent.IntrinsicFiniteCycle
import AllCharacteristics.HomogeneousProjective

/-! SOURCE ONLY / UNVERIFIED. Literal zero-dimensional projective schemes
are finite over their field. Properness supplies the structural finiteness
hypotheses; no finite-morphism certificate is an input. -/
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem projectiveHomogeneousIdeal_isFinite_of_zeroDimensional
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hzero : topologicalKrullDim (scheme I) ≤ 0) : IsFinite (toBase I) := by
  letI : IsArtinianScheme (scheme I) :=
    isArtinianScheme_of_topologicalKrullDim_le_zero_of_locallyOfFiniteType
      (toBase I) hzero
  exact isFinite_of_isArtinianScheme_of_locallyOfFiniteType (toBase I)

end PfaffianDescent
