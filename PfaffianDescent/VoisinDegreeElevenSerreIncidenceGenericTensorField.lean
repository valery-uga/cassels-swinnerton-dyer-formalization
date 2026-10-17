import PfaffianDescent.VoisinDegreeElevenSerreIncidenceGenericCoefficientMap
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceOpenBaseCoefficient

/-! # A finite support remains a field over the actual generic configuration field -/
noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped TensorProduct
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem serreIncidenceGeometric_generic_tensor_isField
    {K L : Type u} [Field K] [Field L] [Algebra K L] [Module.Finite K L]
    {X : Scheme.{u}} [IsIntegral X]
    (base : X ⟶ Spec (.of K)) [GeometricallyIntegral base]
    (a : CommRingCat.of K ⟶ X.functionField)
    (ha : Spec.map a = X.fromSpecStalk (genericPoint X) ≫ base) :
    letI := a.hom.toAlgebra
    IsField (L ⊗[K] X.functionField) := by
  letI := a.hom.toAlgebra
  obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset
    (X := X) (x := genericPoint X) (U := ⊤) trivial
  letI : Nonempty U := ⟨⟨genericPoint X, hx⟩⟩
  letI : Nonempty (U : Scheme.{u}) := ⟨⟨genericPoint X, hx⟩⟩
  letI := RingHom.toAlgebra (schemeOpenBaseRingHom base U)
  letI : IsScalarTower K Γ(X, U) X.functionField := by
    apply IsScalarTower.of_algebraMap_eq'
    ext k
    change a.hom k = X.germToFunctionField U (schemeOpenBaseRingHom base U k)
    rw [serreIncidenceGenericCoefficientMap_eq base a ha]
    simp only [RingHom.comp_apply, schemeOpenBaseRingHom_top_apply]
    exact (X.presheaf.germ_res_apply (homOfLE (show U ≤ ⊤ from le_top))
      (genericPoint X) hx (affineFunctionHom base k)).symm
  letI : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  letI : IsDomain (L ⊗[K] Γ(X, U)) :=
    serreIncidenceGeometric_open_tensor_isDomain (L := L) base U hU
  exact serreIncidenceFractionTensor_isField (R := Γ(X, U))

end PfaffianDescent
