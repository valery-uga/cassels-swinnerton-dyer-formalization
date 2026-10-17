import PfaffianDescent.VoisinDegreeElevenSerreIncidenceAffineGeometricTensor
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceFractionTensorField
import Mathlib.AlgebraicGeometry.FunctionField

/-! # Actual geometrically integral affine function fields retain finite field supports -/
noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped TensorProduct
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem serreIncidenceGeometricAffine_functionField_tensor_isField
    {K L : Type u} [Field K] [Field L] [Algebra K L] [Module.Finite K L]
    {X : Scheme.{u}} [IsAffine X] [IsIntegral X]
    (base : X ⟶ Spec (.of K)) [GeometricallyIntegral base] :
    letI : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
    letI := RingHom.toAlgebra (schemeOpenBaseRingHom base ⊤)
    letI := RingHom.toAlgebra
      ((X.germToFunctionField ⊤).hom.comp (schemeOpenBaseRingHom base ⊤))
    IsField (L ⊗[K] X.functionField) := by
  letI : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
  letI := RingHom.toAlgebra (schemeOpenBaseRingHom base ⊤)
  letI := RingHom.toAlgebra
    ((X.germToFunctionField ⊤).hom.comp (schemeOpenBaseRingHom base ⊤))
  letI : IsScalarTower K Γ(X, ⊤) X.functionField :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsFractionRing Γ(X, ⊤) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X ⊤ (isAffineOpen_top X)
  letI : IsDomain (L ⊗[K] Γ(X, ⊤)) :=
    serreIncidenceGeometricAffine_tensor_isDomain (L := L) base
  exact serreIncidenceFractionTensor_isField (R := Γ(X, ⊤))

end PfaffianDescent
