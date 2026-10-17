import PfaffianDescent.SchemeModuleCanonicalChartFunctionField
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceOpenBaseCoefficient
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceFractionTensorDomain
import PfaffianDescent.VoisinGenericCubicResidual

/-! Source-only / unverified. The original-pi function-field action is
retained. Geometric integrality proves the actual tensor field-ring is a
domain for every coefficient-field extension, with no finiteness premise. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory
open scoped TensorProduct PfaffianDescent.Coray
universe u
variable {K B : Type u} [Field K] [Field B] [Algebra K B]

/-- Identity on the actual field carrier, proving that its existing
original-pi Module action is the SAME multiplication action of the original
coefficient hom. This installs no new action on the existing alias. -/
def schemeFunctionFieldOriginalRingLinearEquiv {X : Scheme.{u}} [IsIntegral X]
    (pi : X ⟶ Spec (.of K)) :
    letI : Algebra K X.functionField := (schemeFunctionFieldGroundRingHom pi).toAlgebra
    SchemeFunctionFieldOver pi ≃ₗ[K] X.functionField := by
  letI : Algebra K X.functionField := (schemeFunctionFieldGroundRingHom pi).toAlgebra
  refine { toFun := fun s => (show X.functionField from s)
           invFun := fun s => (show SchemeFunctionFieldOver pi from s)
           left_inv := fun _ => rfl
           right_inv := fun _ => rfl
           map_add' := fun _ _ => rfl
           map_smul' := ?_ }
  intro c s
  change schemeFunctionFieldGroundRingHom pi c * (show X.functionField from s) =
    schemeFunctionFieldGroundRingHom pi c * (show X.functionField from s)
  rfl

/-- Geometric integrality on an actual affine open gives a domain after
field extension; localization then gives the domain property for the SAME
original-pi function-field tensor. B/K is not assumed finite or separable. -/
theorem originalFunctionField_tensor_isDomain {X : Scheme.{u}} [IsIntegral X]
    (pi : X ⟶ Spec (.of K)) [GeometricallyIntegral pi] :
    letI : Algebra K X.functionField := (schemeFunctionFieldGroundRingHom pi).toAlgebra
    IsDomain (B ⊗[K] X.functionField) := by
  letI : Algebra K X.functionField := (schemeFunctionFieldGroundRingHom pi).toAlgebra
  obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset
    (X := X) (x := genericPoint X) (U := ⊤) trivial
  letI : Nonempty U := ⟨⟨genericPoint X, hx⟩⟩
  letI : Nonempty (U : Scheme.{u}) := ⟨⟨genericPoint X, hx⟩⟩
  letI : Algebra K Γ(X, U) := (schemeOpenBaseRingHom pi U).toAlgebra
  letI : IsScalarTower K Γ(X, U) X.functionField := by
    apply IsScalarTower.of_algebraMap_eq'
    ext c
    change schemeFunctionFieldGroundRingHom pi c =
      X.germToFunctionField U (schemeOpenBaseRingHom pi U c)
    exact schemeFunctionFieldGroundRingHom_eq_openGerm pi U c
  letI : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  letI : IsDomain (B ⊗[K] Γ(X, U)) :=
    PfaffianDescent.serreIncidenceGeometric_open_tensor_isDomain (L := B) pi U hU
  exact PfaffianDescent.serreIncidenceFractionTensor_isDomain
    (K := K) (L := B) (R := Γ(X, U)) (F := X.functionField)

/-- For the actual original smooth cubic, geometric integrality is
constructed internally. No image or generic tensor-domain certificate is
an input. -/
theorem cubicOriginalFunctionField_tensor_isDomain
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (AllCharacteristics.HomogeneousProjective.hypersurfaceToBase p hp)]
    [IsIntegral (AllCharacteristics.HomogeneousProjective.hypersurface p hp)] :
    letI : Algebra K (AllCharacteristics.HomogeneousProjective.hypersurface p hp).functionField :=
      (schemeFunctionFieldGroundRingHom
        (AllCharacteristics.HomogeneousProjective.hypersurfaceToBase p hp)).toAlgebra
    IsDomain (B ⊗[K] (AllCharacteristics.HomogeneousProjective.hypersurface p hp).functionField) := by
  letI : GeometricallyIntegral
      (AllCharacteristics.HomogeneousProjective.hypersurfaceToBase p hp) :=
    PfaffianDescent.geometricallyIntegral_hypersurfaceToBase_of_smooth p hp hp0
  exact originalFunctionField_tensor_isDomain (B := B)
    (AllCharacteristics.HomogeneousProjective.hypersurfaceToBase p hp)

end PfaffianDescent.Coray
end
