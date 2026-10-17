import PfaffianDescent.ActualQuarticTensorIntrinsicQuadraticSystem
import PfaffianDescent.ProjectiveLinearCoordinateSchemeIso

/-! Actual projective full-base scheme transport derived from full quadratic
submodule equality. The specialization uses the same supplied-algebra tensor
coordinates and actual residue-basis matrix; no scheme comparison is assumed. -/

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial Module Matrix
open AllCharacteristics.HomogeneousProjective
open scoped TensorProduct
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Full quadratic submodule transport yields transport of the corresponding
homogeneous base ideals, with no finite-base assumption. -/
theorem intrinsicFullQuadraticBaseIdeal_map_of_system_map
    {K : Type u} [Field K] {Z Y : Scheme.{u}}
    (i : Z ⟶ Proj (homogeneousSubmodule (Fin 4) K))
    (j : Y ⟶ Proj (homogeneousSubmodule (Fin 4) K))
    (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnit M.det)
    (hW : (intrinsicFullQuadraticSystem i).map
      (linearSubstitutionEquiv M hM).toLinearEquiv.toLinearMap =
      intrinsicFullQuadraticSystem j) :
    (intrinsicFullQuadraticBaseIdeal j).toIdeal =
      (intrinsicFullQuadraticBaseIdeal i).toIdeal.map
        (linearSubstitutionEquiv M hM).toRingHom := by
  change Ideal.span (intrinsicFullQuadraticSystem j : Set (MvPolynomial (Fin 4) K)) =
    (Ideal.span (intrinsicFullQuadraticSystem i : Set (MvPolynomial (Fin 4) K))).map
      (linearSubstitutionEquiv M hM).toRingHom
  rw [Ideal.map_span]
  apply congrArg Ideal.span
  rw [← hW]
  rfl

/-- This is the actual projective scheme isomorphism, over K, associated
to the same full-system coordinate substitution. -/
def intrinsicFullQuadraticBaseSchemeIso_of_system_map
    {K : Type u} [Field K] {Z Y : Scheme.{u}}
    (i : Z ⟶ Proj (homogeneousSubmodule (Fin 4) K))
    (j : Y ⟶ Proj (homogeneousSubmodule (Fin 4) K))
    (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnit M.det)
    (hW : (intrinsicFullQuadraticSystem i).map
      (linearSubstitutionEquiv M hM).toLinearEquiv.toLinearMap =
      intrinsicFullQuadraticSystem j) :
    scheme (intrinsicFullQuadraticBaseIdeal i) ≅
      scheme (intrinsicFullQuadraticBaseIdeal j) :=
  linearCoordinateChangeSchemeIso M hM _ _
    (intrinsicFullQuadraticBaseIdeal_map_of_system_map i j M hM hW)

theorem intrinsicFullQuadraticBaseSchemeIso_of_system_map_toBase
    {K : Type u} [Field K] {Z Y : Scheme.{u}}
    (i : Z ⟶ Proj (homogeneousSubmodule (Fin 4) K))
    (j : Y ⟶ Proj (homogeneousSubmodule (Fin 4) K))
    (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnit M.det)
    (hW : (intrinsicFullQuadraticSystem i).map
      (linearSubstitutionEquiv M hM).toLinearEquiv.toLinearMap =
      intrinsicFullQuadraticSystem j) :
    (intrinsicFullQuadraticBaseSchemeIso_of_system_map i j M hM hW).hom ≫
      toBase (intrinsicFullQuadraticBaseIdeal j) =
      toBase (intrinsicFullQuadraticBaseIdeal i) :=
  linearCoordinateChangeSchemeIso_hom_toBase M hM _ _
    (intrinsicFullQuadraticBaseIdeal_map_of_system_map i j M hM hW)

namespace QuarticNet
variable {k L K A : Type u} [Field k] [Field L] [Field K] [CommRing A]
  [Algebra k L] [Algebra k K] [Algebra k A]
  [IsAlgClosed K] [FiniteDimensional k L] [Algebra.IsSeparable k L]
  [FiniteDimensional k A]

/-- The actual supplied-algebra tensor point and actual four-tangent point
have isomorphic FULL base schemes under the internally derived matrix. -/
def actualQuarticTensor_fullQuadraticBaseSchemeIso
    (eA : A ≃ₐ[k] DualNumber L) (x : Fin 4 → A)
    (b : Basis (Fin 4) k L) (v : Fin 4 → L)
    (hx : ∀ r, eA (x r) = TrivSqZeroExt.inl (b r) + TrivSqZeroExt.inr (v r))
    (hb : b 0 = 1) (hv : v 0 = 0)
    (full : Fin 4 ≃ (L →ₐ[k] K)) (l : Fin 4 → K) (hl : ∀ row, l row ≠ 0) :
    let hs := conjugate_basis_span b full
    let U := rescaleTangentDirections l (conjugateTangentMatrix full b v hs)
    scheme (intrinsicFullQuadraticBaseIdeal
      (actualQuarticTensorNormalizedToProjective (K := K) eA x b v hx hb hv ≫
        quotientProjMap ⊥)) ≅
      scheme (intrinsicFullQuadraticBaseIdeal
        (fourTangentDualToProjective U ≫ quotientProjMap ⊥)) := by
  let hs := conjugate_basis_span b full
  let cb := conjugateBasis full b hs
  exact intrinsicFullQuadraticBaseSchemeIso_of_system_map _ _
    (basisCoordinateMatrix cb) (basisCoordinateMatrix_isUnit cb)
    (actualQuarticTensor_intrinsicFullQuadraticSystem_map eA x b v hx hb hv full l hl)

/-- The full base scheme comparison retains the actual K-structure maps. -/
theorem actualQuarticTensor_fullQuadraticBaseSchemeIso_toBase
    (eA : A ≃ₐ[k] DualNumber L) (x : Fin 4 → A)
    (b : Basis (Fin 4) k L) (v : Fin 4 → L)
    (hx : ∀ r, eA (x r) = TrivSqZeroExt.inl (b r) + TrivSqZeroExt.inr (v r))
    (hb : b 0 = 1) (hv : v 0 = 0)
    (full : Fin 4 ≃ (L →ₐ[k] K)) (l : Fin 4 → K) (hl : ∀ row, l row ≠ 0) :
    let hs := conjugate_basis_span b full
    let U := rescaleTangentDirections l (conjugateTangentMatrix full b v hs)
    (actualQuarticTensor_fullQuadraticBaseSchemeIso eA x b v hx hb hv full l hl).hom ≫
      toBase (intrinsicFullQuadraticBaseIdeal
        (fourTangentDualToProjective U ≫ quotientProjMap ⊥)) =
      toBase (intrinsicFullQuadraticBaseIdeal
        (actualQuarticTensorNormalizedToProjective (K := K) eA x b v hx hb hv ≫
          quotientProjMap ⊥)) := by
  let hs := conjugate_basis_span b full
  let cb := conjugateBasis full b hs
  exact intrinsicFullQuadraticBaseSchemeIso_of_system_map_toBase _ _
    (basisCoordinateMatrix cb) (basisCoordinateMatrix_isUnit cb)
    (actualQuarticTensor_intrinsicFullQuadraticSystem_map eA x b v hx hb hv full l hl)

end QuarticNet
end PfaffianDescent
