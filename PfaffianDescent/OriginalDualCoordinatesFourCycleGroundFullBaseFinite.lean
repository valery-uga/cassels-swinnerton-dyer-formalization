import PfaffianDescent.FourCycleIntrinsicFullBaseFinite
import PfaffianDescent.FourTangentRelabelFullBaseTransport
import PfaffianDescent.ActualQuarticOriginalTensorFullBaseAlternative
import PfaffianDescent.NormalizedIntrinsicQuadraticFieldExtension
import PfaffianDescent.ProjectiveCoefficientFiniteDescent

/-! SOURCE ONLY, UNVERIFIED. Actual four-cycle full-base finiteness descends
from the SAME supplied original algebra/coordinates to the original field.
The displayed scalar entries are the literal C4 branch, not a finite-base,
full-system comparison or descent certificate. -/
noncomputable section
namespace PfaffianDescent.QuarticNet
open AlgebraicGeometry CategoryTheory MvPolynomial Module Matrix
open AllCharacteristics.HomogeneousProjective
open scoped TensorProduct
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k L A : Type u} [Field k] [PerfectField k] [Field L] [CommRing A]
  [Algebra k L] [Algebra k A] [FiniteDimensional k L]
  [Algebra.IsSeparable k L] [FiniteDimensional k A]

theorem originalDualCoordinates_fourCycle_groundFullBase_isFinite
    (eA : A ≃ₐ[k] DualNumber L) (x : Fin 4 → A)
    (j : Fin 4) (hxj : x j = 1) (pi : Equiv.Perm (Fin 4)) (hpi : pi 0 = j)
    (b : Basis (Fin 4) k L) (v : Fin 4 → L)
    (hx : ∀ r, eA (x (pi r)) = TrivSqZeroExt.inl (b r) + TrivSqZeroExt.inr (v r))
    (hb : b 0 = 1) (hv : v 0 = 0)
    (full : Fin 4 ≃ (L →ₐ[k] AlgebraicClosure k))
    (l : Fin 4 → AlgebraicClosure k) (hl : ∀ r, l r ≠ 0)
    (rho : Equiv.Perm (Fin 4)) :
    let hs := conjugate_basis_span b full
    let U := rescaleTangentDirections l (conjugateTangentMatrix full b v hs)
    let V := tangentRelabel U rho
    (∀ r s, V r s = -V s r) →
    V 0 1 = 0 → V 2 3 = 0 →
    V 0 2 ≠ 0 → V 0 3 ≠ 0 → V 1 2 ≠ 0 → V 1 3 ≠ 0 →
    IsFinite (toBase (intrinsicFullQuadraticBaseIdeal
      (ambientNormalizedCoordinateChartPoint (F := k) x j hxj))) := by
  dsimp only
  intro hskew h01 h23 h02 h03 h12 h13
  let K := AlgebraicClosure k
  let hs := conjugate_basis_span b full
  let U := rescaleTangentDirections l (conjugateTangentMatrix full b v hs)
  let V := tangentRelabel U rho
  have hdiag (r : Fin 4) : U r r = 0 := by
    simp only [U, rescaleTangentDirections, conjugateTangentMatrix_diagonal, mul_zero]
  have hV : V = skewTangentDirections 0 (V 0 2) (V 0 3) (V 1 2) (V 1 3) 0 := by
    have h := skew_matrix_eq_parameters V (fun r => hdiag (rho r)) hskew
    change V 0 1 = 0 at h01
    change V 2 3 = 0 at h23
    rw [h01, h23] at h
    exact h
  letI : IsFinite (toBase (intrinsicFullQuadraticBaseIdeal
      (fourTangentDualToProjective V ≫ quotientProjMap ⊥))) := by
    rw [hV]
    exact fourCycle_intrinsicFullQuadraticBase_isFinite
      (V 0 2) (V 0 3) (V 1 2) (V 1 3) h02 h03 h12 h13
  letI : IsFinite (toBase (intrinsicFullQuadraticBaseIdeal
      (fourTangentDualToProjective U ≫ quotientProjMap ⊥))) :=
    fourTangent_intrinsicFullBase_finite_of_relabel U hdiag rho
  let q0 := ambientNormalizedCoordinateChartPoint (F := k) x j hxj
  let qT := ambientNormalizedCoordinateChartPoint (F := K)
    (fun r => (1 : K) ⊗ₜ[k] x r) j (tensor_coordinate_eq_one x j hxj)
  let M := basisCoordinateMatrix (conjugateBasis full b hs)
  let P := Equiv.Perm.permMatrix K pi.symm
  have hPM : IsUnit (P * M).det := by
    rw [Matrix.det_mul]
    exact (permutationMatrix_isUnit_det pi.symm).mul (basisCoordinateMatrix_isUnit _)
  have hW := actualQuarticOriginalTensor_intrinsicQuadratics_map
    eA x j hxj pi hpi b v hx hb hv full l hl
  let eBase := intrinsicFullQuadraticBaseSchemeIso_of_system_map qT
    (fourTangentDualToProjective U ≫ quotientProjMap ⊥) (P * M) hPM hW
  have hBase : eBase.hom ≫ toBase (intrinsicFullQuadraticBaseIdeal
      (fourTangentDualToProjective U ≫ quotientProjMap ⊥)) =
      toBase (intrinsicFullQuadraticBaseIdeal qT) :=
    intrinsicFullQuadraticBaseSchemeIso_of_system_map_toBase qT
      (fourTangentDualToProjective U ≫ quotientProjMap ⊥) (P * M) hPM hW
  letI : IsFinite (toBase (intrinsicFullQuadraticBaseIdeal qT)) := by
    rw [← hBase]
    infer_instance
  have hB : intrinsicFullQuadraticBaseIdeal qT =
      HomogeneousIdeal.map (ambientCoefficientGradedRingHom (algebraMap k K))
        (intrinsicFullQuadraticBaseIdeal q0) :=
    ambientNormalizedCoordinateChartPoint_intrinsicFullBase_fieldExtension x j hxj
  letI : IsFinite (toBase (HomogeneousIdeal.map
      (ambientCoefficientGradedRingHom (algebraMap k K))
        (intrinsicFullQuadraticBaseIdeal q0))) := by
    rw [← hB]
    infer_instance
  exact projectiveCoefficientExtension_isFinite_descend (K := K)
    (intrinsicFullQuadraticBaseIdeal q0)

end PfaffianDescent.QuarticNet
