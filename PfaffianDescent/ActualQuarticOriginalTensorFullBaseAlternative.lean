import PfaffianDescent.ActualTensorCoordinateFiniteEmbedding
import PfaffianDescent.IntrinsicFullBaseAlternativeTransport

/-! The nondegenerate base-scheme alternative for the ORIGINAL tensor chart
embedding. All ideal and comparison data are derived from the actual algebra
presentation; the original chart permutation is retained. This is a derived-
data adapter for supplied-Z extraction, not a universal geometric parametrization. -/

noncomputable section
namespace PfaffianDescent.QuarticNet
open AlgebraicGeometry CategoryTheory MvPolynomial Module Matrix
open AllCharacteristics.HomogeneousProjective
open scoped TensorProduct
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k L K A : Type u} [Field k] [Field L] [Field K] [CommRing A]
  [Algebra k L] [Algebra k K] [Algebra k A]
  [IsAlgClosed K] [FiniteDimensional k L] [Algebra.IsSeparable k L]
  [FiniteDimensional k A]

/-- The inverse chart permutation and residue-basis matrix combine to the
actual coordinate substitution carrying the entire original full series. -/
theorem actualQuarticOriginalTensor_intrinsicQuadratics_map
    (eA : A ≃ₐ[k] DualNumber L) (x : Fin 4 → A)
    (j : Fin 4) (hxj : x j = 1) (pi : Equiv.Perm (Fin 4)) (hpi : pi 0 = j)
    (b : Basis (Fin 4) k L) (v : Fin 4 → L)
    (hx : ∀ r, eA (x (pi r)) = TrivSqZeroExt.inl (b r) + TrivSqZeroExt.inr (v r))
    (hb : b 0 = 1) (hv : v 0 = 0)
    (full : Fin 4 ≃ (L →ₐ[k] K)) (l : Fin 4 → K) (hl : ∀ row, l row ≠ 0) :
    let hs := conjugate_basis_span b full
    let M := basisCoordinateMatrix (conjugateBasis full b hs)
    let P := Equiv.Perm.permMatrix K pi.symm
    let hPM : IsUnit (P * M).det := by
      rw [Matrix.det_mul]
      exact (permutationMatrix_isUnit_det pi.symm).mul (basisCoordinateMatrix_isUnit _)
    let U := rescaleTangentDirections l (conjugateTangentMatrix full b v hs)
    (intrinsicFullQuadraticSystem
      (ambientNormalizedCoordinateChartPoint (F := K)
        (fun r => (1 : K) ⊗ₜ[k] x r) j (tensor_coordinate_eq_one x j hxj))).map
        (linearSubstitutionEquiv (P * M) hPM).toLinearEquiv.toLinearMap =
      intrinsicFullQuadraticSystem (fourTangentDualToProjective U ≫ quotientProjMap ⊥) := by
  let hs := conjugate_basis_span b full
  let M := basisCoordinateMatrix (conjugateBasis full b hs)
  let P := Equiv.Perm.permMatrix K pi.symm
  let y : Fin 4 → K ⊗[k] A := fun r => (1 : K) ⊗ₜ[k] x r
  let q := ambientNormalizedCoordinateChartPoint (F := K) y j (tensor_coordinate_eq_one x j hxj)
  let qp := ambientNormalizedCoordinateChartPoint (F := K) (fun r => y (pi r)) 0
    (by rw [hpi]; exact tensor_coordinate_eq_one x j hxj)
  have hP : (intrinsicFullQuadraticSystem q).map
      (linearSubstitutionEquiv P (permutationMatrix_isUnit_det pi.symm)).toLinearEquiv.toLinearMap =
      intrinsicFullQuadraticSystem qp :=
    ambientNormalizedCoordinateChartPoint_intrinsicQuadratics_permutation y j
      (tensor_coordinate_eq_one x j hxj) pi hpi
  have hM : (intrinsicFullQuadraticSystem qp).map
      (linearSubstitutionEquiv M (basisCoordinateMatrix_isUnit _)).toLinearEquiv.toLinearMap =
      intrinsicFullQuadraticSystem
        (fourTangentDualToProjective
          (rescaleTangentDirections l (conjugateTangentMatrix full b v hs)) ≫ quotientProjMap ⊥) := by
    have hpoint := actualQuarticTensorNormalizedToProjective_toAmbient
      (K := K) eA (fun r => x (pi r)) b v hx hb hv
    have hqp : actualQuarticTensorNormalizedToProjective (K := K)
        eA (fun r => x (pi r)) b v hx hb hv ≫ quotientProjMap ⊥ = qp := hpoint
    rw [← hqp]
    exact actualQuarticTensor_intrinsicFullQuadraticSystem_map
      eA (fun r => x (pi r)) b v hx hb hv full l hl
  calc
    _ = ((intrinsicFullQuadraticSystem q).map
          (linearSubstitutionEquiv P (permutationMatrix_isUnit_det pi.symm)).toLinearEquiv.toLinearMap).map
          (linearSubstitutionEquiv M (basisCoordinateMatrix_isUnit _)).toLinearEquiv.toLinearMap := by
      rw [← Submodule.map_comp]
      apply congrArg (Submodule.map · (intrinsicFullQuadraticSystem q))
      apply LinearMap.ext
      intro p
      change linearSubstitution (P * M) p = linearSubstitution M (linearSubstitution P p)
      rw [← AlgHom.comp_apply, linearSubstitution_comp]
    _ = _ := by rw [hP, hM]

/-- Nondegenerate branch, retaining the SAME original tensor embedding.
Its closed immersion, rank eight, and full-system comparison are proved here.
The extraction supplies the dual/basis/rescaling data; six nonzero entries
are the literal nondegeneracy condition of the coordinate calculation. -/
theorem actualQuarticOriginalTensor_fullBase_embedded_alternative
    (eA : A ≃ₐ[k] DualNumber L) (x : Fin 4 → A)
    (hgen : Function.Surjective (aeval (R := k) x))
    (j : Fin 4) (hxj : x j = 1) (pi : Equiv.Perm (Fin 4)) (hpi : pi 0 = j)
    (b : Basis (Fin 4) k L) (v : Fin 4 → L)
    (hx : ∀ r, eA (x (pi r)) = TrivSqZeroExt.inl (b r) + TrivSqZeroExt.inr (v r))
    (hb : b 0 = 1) (hv : v 0 = 0)
    (full : Fin 4 ≃ (L →ₐ[k] K)) (l : Fin 4 → K) (hl : ∀ row, l row ≠ 0)
    (hskew : ∀ r s, l r * conjugateTangentMatrix full b v (conjugate_basis_span b full) r s =
      -(l s * conjugateTangentMatrix full b v (conjugate_basis_span b full) s r))
    (hnonzero : ∀ r s, r ≠ s →
      conjugateTangentMatrix full b v (conjugate_basis_span b full) r s ≠ 0) :
    let q := ambientNormalizedCoordinateChartPoint (F := K)
      (fun r => (1 : K) ⊗ₜ[k] x r) j (tensor_coordinate_eq_one x j hxj)
    (∃ f : Spec (.of (K ⊗[k] A)) ⟶ scheme (intrinsicFullQuadraticBaseIdeal q),
      IsIso f ∧ f ≫ quotientProjMap (intrinsicFullQuadraticBaseIdeal q) = q) ∨
      GroundTwistedCubicPresentation (intrinsicFullQuadraticBaseIdeal q) := by
  let hs := conjugate_basis_span b full
  let M := basisCoordinateMatrix (conjugateBasis full b hs)
  let P := Equiv.Perm.permMatrix K pi.symm
  let y : Fin 4 → K ⊗[k] A := fun r => (1 : K) ⊗ₜ[k] x r
  let q := ambientNormalizedCoordinateChartPoint (F := K) y j (tensor_coordinate_eq_one x j hxj)
  let U := rescaleTangentDirections l (conjugateTangentMatrix full b v hs)
  have hdiag : ∀ r, U r r = 0 := by
    intro r
    simp only [U, rescaleTangentDirections, conjugateTangentMatrix_diagonal, mul_zero]
  have hUskew : ∀ r s, U r s = -U s r := hskew
  have hU : U = skewTangentDirections (U 0 1) (U 0 2) (U 0 3)
      (U 1 2) (U 1 3) (U 2 3) := skew_matrix_eq_parameters U hdiag hUskew
  have hUne : ∀ r s, r ≠ s → U r s ≠ 0 := by
    intro r s hrs
    exact mul_ne_zero (hl r) (hnonzero r s hrs)
  letI : IsClosedImmersion q := ambientNormalizedCoordinateChartPoint_isClosedImmersion
    y j (tensor_coordinate_eq_one x j hxj) (tensorCoordinates_aeval_surjective x hgen)
  letI : IsFinite (q ≫ ambientToBase) :=
    ambientNormalizedCoordinateChartPoint_finite_toBase y j (tensor_coordinate_eq_one x j hxj)
  have hq8 : AllCharacteristics.finiteSchemeRank (q ≫ ambientToBase) = 8 :=
    (ambientNormalizedCoordinateChartPoint_finiteSchemeRank y j
      (tensor_coordinate_eq_one x j hxj)).trans (actualQuarticTensor_finrank_eight eA b full)
  have hPM : IsUnit (P * M).det := by
    rw [Matrix.det_mul]
    exact (permutationMatrix_isUnit_det pi.symm).mul (basisCoordinateMatrix_isUnit _)
  have hW := actualQuarticOriginalTensor_intrinsicQuadratics_map
    eA x j hxj pi hpi b v hx hb hv full l hl
  change (intrinsicFullQuadraticSystem q).map
      (linearSubstitutionEquiv (P * M) hPM).toLinearEquiv.toLinearMap =
      intrinsicFullQuadraticSystem (fourTangentDualToProjective U ≫ quotientProjMap ⊥) at hW
  rw [hU] at hW
  exact intrinsicFullQuadraticBase_embedded_alternative_of_skew_system_map q hq8
    (U 0 1) (U 0 2) (U 0 3) (U 1 2) (U 1 3) (U 2 3)
    (hUne 0 1 (by decide)) (hUne 0 2 (by decide)) (hUne 0 3 (by decide))
    (hUne 1 2 (by decide)) (hUne 1 3 (by decide)) (hUne 2 3 (by decide))
    (P * M) hPM hW

end PfaffianDescent.QuarticNet
