import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualEmbedding

noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

def cubicClosedPointSerreFiniteZeroResidual_fieldPoint_support_embedding
    {L : Type u} [Field L] {X T : Scheme.{u}}
    (c : T ⟶ X) [IsClosedImmersion c]
    (j : Spec (.of L) ⟶ X)
    (hj : j (IsLocalRing.closedPoint L) ∈ Set.range c) : Spec (.of L) ⟶ T :=
  IsClosedImmersion.lift c j
    (cubicClosedPointSerreFiniteZeroResidual_kernel_le_of_reduced_range j c (by
      rintro _ ⟨z,rfl⟩
      exact (congrArg j (Subsingleton.elim z (IsLocalRing.closedPoint L))) ▸ hj))

@[reassoc]
theorem cubicClosedPointSerreFiniteZeroResidual_fieldPoint_support_embedding_comp
    {L : Type u} [Field L] {X T : Scheme.{u}}
    (c : T ⟶ X) [IsClosedImmersion c]
    (j : Spec (.of L) ⟶ X)
    (hj : j (IsLocalRing.closedPoint L) ∈ Set.range c) :
    cubicClosedPointSerreFiniteZeroResidual_fieldPoint_support_embedding c j hj ≫ c = j :=
  IsClosedImmersion.lift_fac _ _ _

theorem cubicClosedPointSerreFiniteZeroResidual_fieldPoint_support_embedding_isClosedImmersion
    {L : Type u} [Field L] {X T : Scheme.{u}}
    (c : T ⟶ X) [IsClosedImmersion c]
    (j : Spec (.of L) ⟶ X) [IsClosedImmersion j]
    (hj : j (IsLocalRing.closedPoint L) ∈ Set.range c) :
    IsClosedImmersion (cubicClosedPointSerreFiniteZeroResidual_fieldPoint_support_embedding c j hj) := by
  let w := cubicClosedPointSerreFiniteZeroResidual_fieldPoint_support_embedding c j hj
  letI : IsClosedImmersion (w ≫ c) := by
    rw [cubicClosedPointSerreFiniteZeroResidual_fieldPoint_support_embedding_comp]
    infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion w c

end PfaffianDescent
