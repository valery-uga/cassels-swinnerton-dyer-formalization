import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualCoefficientCanonicalSupportAvoidance

noncomputable section
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent.ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The literal marked-surface comparison transfers avoidance of the original
support to its canonical coefficient-base-change support. -/
theorem cubicClosedPointSerreFiniteZeroResidual_coefficientMarked_not_mem_range
    {K F : Type u} [Field K] [Field F] (g : K →+* F)
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    {D U : Scheme.{u}} [IsAffine D]
    (i : D ⟶ hypersurface p hp) [IsClosedImmersion i]
    (marked : U ⟶ hypersurface (p.map g) (hp.map g))
    (original : U ⟶ hypersurface p hp)
    (hmarked : marked ≫ cubicPointTraceFieldBaseChangeCubicCoefficientMap g p hp = original)
    (q : U) (hout : original q ∉ Set.range i) :
    marked q ∉ Set.range
      (cubicClosedPointSerreFiniteZeroResidual_coefficientCanonicalPoint g p hp i) := by
  apply cubicClosedPointSerreFiniteZeroResidual_coefficientCanonicalPoint_not_mem_range
    g p hp i (marked q)
  have hpoint := congrArg (fun f : U ⟶ hypersurface p hp => f q) hmarked
  rw [Scheme.Hom.comp_apply] at hpoint
  rw [hpoint]
  exact hout

end PfaffianDescent.ProjectiveNegativeTwist
