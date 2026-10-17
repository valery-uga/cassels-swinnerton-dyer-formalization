import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualCoefficientCanonicalSerre

/-! Avoiding the original support implies avoiding its actual canonical
coefficient-base-change support. -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent.ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

private theorem coefficientCanonicalSupport_range_comp_subset
    {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z) :
    Set.range (a ≫ b) ⊆ Set.range b := by
  rintro x ⟨z, rfl⟩
  exact ⟨a z, (Scheme.Hom.comp_apply a b z).symm⟩

theorem cubicClosedPointSerreFiniteZeroResidual_coefficientCanonicalPoint_not_mem_range
    {K F : Type u} [Field K] [Field F] (g : K →+* F)
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    {D : Scheme.{u}} [IsAffine D] (i : D ⟶ hypersurface p hp) [IsClosedImmersion i]
    (y : hypersurface (p.map g) (hp.map g))
    (hy : cubicPointTraceFieldBaseChangeCubicCoefficientMap g p hp y ∉ Set.range i) :
    y ∉ Set.range (cubicClosedPointSerreFiniteZeroResidual_coefficientCanonicalPoint g p hp i) := by
  letI : IsAffineHom (cubicPointTraceFieldBaseChangeCubicCoefficientMap g p hp) :=
    serreIncidenceCubicCoefficientMap_affine g p hp
  intro h
  unfold cubicClosedPointSerreFiniteZeroResidual_coefficientCanonicalPoint at h
  have hfst : y ∈ Set.range
      (pullback.fst (cubicPointTraceFieldBaseChangeCubicCoefficientMap g p hp) i) :=
    coefficientCanonicalSupport_range_comp_subset _ _ h
  rw [Scheme.Pullback.range_fst] at hfst
  exact hy hfst

end PfaffianDescent.ProjectiveNegativeTwist
