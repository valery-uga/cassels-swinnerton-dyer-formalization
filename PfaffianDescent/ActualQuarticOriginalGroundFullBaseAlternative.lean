import PfaffianDescent.ActualQuarticOriginalTensorFullBaseAlternative
import PfaffianDescent.IntrinsicFullBaseAlternativeSourceIso
import PfaffianDescent.IntrinsicGroundQuadraticCompleteIntersection
import PfaffianDescent.NormalizedIntrinsicQuadraticFieldExtension
import PfaffianDescent.ProjectiveCoefficientFiniteDescent
import AllCharacteristics.TwistedCubicLemma

/-! The actual quartic-dual original embedding's nondegenerate full-base
alternative DESCENDS TO THE ORIGINAL perfect ground field. Scalar extension,
finite descent and twisted presentation descent are derived internally. -/

noncomputable section
namespace PfaffianDescent.QuarticNet
open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics.HomogeneousProjective
open scoped TensorProduct
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k L A : Type u} [Field k] [PerfectField k] [Field L] [CommRing A]
  [Algebra k L] [Algebra k A] [FiniteDimensional k L]
  [Algebra.IsSeparable k L] [FiniteDimensional k A]

/-- This adapter takes actual coordinate data, not a full-system/base
comparison or a supplied ground curve/triple. Its supplied-Z caller derives
ALL these data from the actual embedding. -/
theorem actualQuarticOriginalGround_fullBase_embedded_alternative
    (eA : A ≃ₐ[k] DualNumber L) (x : Fin 4 → A)
    (hgen : Function.Surjective (aeval (R := k) x))
    (j : Fin 4) (hxj : x j = 1) (pi : Equiv.Perm (Fin 4)) (hpi : pi 0 = j)
    (b : Basis (Fin 4) k L) (v : Fin 4 → L)
    (hx : ∀ r, eA (x (pi r)) = TrivSqZeroExt.inl (b r) + TrivSqZeroExt.inr (v r))
    (hb : b 0 = 1) (hv : v 0 = 0)
    (full : Fin 4 ≃ (L →ₐ[k] AlgebraicClosure k))
    (l : Fin 4 → AlgebraicClosure k) (hl : ∀ row, l row ≠ 0)
    (hskew : ∀ r s, l r * conjugateTangentMatrix full b v (conjugate_basis_span b full) r s =
      -(l s * conjugateTangentMatrix full b v (conjugate_basis_span b full) s r))
    (hnonzero : ∀ r s, r ≠ s →
      conjugateTangentMatrix full b v (conjugate_basis_span b full) r s ≠ 0) :
    IntrinsicFullBaseEmbeddedAlternative (ambientNormalizedCoordinateChartPoint (F := k) x j hxj) := by
  let K := AlgebraicClosure k
  let q0 := ambientNormalizedCoordinateChartPoint (F := k) x j hxj
  let qT := ambientNormalizedCoordinateChartPoint (F := K)
    (fun r => (1 : K) ⊗ₜ[k] x r) j (tensor_coordinate_eq_one x j hxj)
  let B0 := intrinsicFullQuadraticBaseIdeal q0
  let BT := intrinsicFullQuadraticBaseIdeal qT
  have hB : BT = HomogeneousIdeal.map
      (ambientCoefficientGradedRingHom (algebraMap k K)) B0 :=
    ambientNormalizedCoordinateChartPoint_intrinsicFullBase_fieldExtension x j hxj
  letI : IsClosedImmersion q0 :=
    ambientNormalizedCoordinateChartPoint_isClosedImmersion (K := k) x j hxj hgen
  letI : IsFinite (q0 ≫ ambientToBase) :=
    ambientNormalizedCoordinateChartPoint_finite_toBase (K := k) x j hxj
  letI : IsFinite (qT ≫ ambientToBase) :=
    ambientNormalizedCoordinateChartPoint_finite_toBase (K := K)
      (fun r => (1 : K) ⊗ₜ[k] x r) j (tensor_coordinate_eq_one x j hxj)
  rcases actualQuarticOriginalTensor_fullBase_embedded_alternative
      eA x hgen j hxj pi hpi b v hx hb hv full l hl hskew hnonzero with
      ⟨f, hf, hfac⟩ | hTwisted
  · letI : IsIso f := hf
    have hbase : f ≫ toBase BT = qT ≫ ambientToBase := by
      rw [← quotientProjMap_toBase, ← Category.assoc, hfac]
    have hbase' : toBase BT = inv f ≫ (qT ≫ ambientToBase) := by
      rw [← hbase]
      simp only [← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
    letI : IsFinite (toBase BT) := by rw [hbase']; infer_instance
    letI : IsFinite (toBase (HomogeneousIdeal.map
        (ambientCoefficientGradedRingHom (algebraMap k K)) B0)) := by
      rw [← hB]
      infer_instance
    letI : IsFinite (toBase B0) := projectiveCoefficientExtension_isFinite_descend (K := K) B0
    letI : Module.Free k A := Module.Free.of_divisionRing k A
    have hA8 : finrank k A = 8 :=
      (Module.finrank_baseChange (R := K) (S := k) (M' := A)).symm.trans
        (actualQuarticTensor_finrank_eight (k := k) (K := K) (A := A) eA b full)
    have hq08 : AllCharacteristics.finiteSchemeRank (q0 ≫ ambientToBase) = 8 :=
      (ambientNormalizedCoordinateChartPoint_finiteSchemeRank (K := k) x j hxj).trans hA8
    apply Or.inl
    exact ⟨(intrinsicGroundFullQuadraticBaseIso q0 hq08).hom, inferInstance,
      intrinsicGroundFullQuadraticBaseIso_ambient q0 hq08⟩
  · apply Or.inr
    have hbar : GroundTwistedCubicPresentation (HomogeneousIdeal.map
        (ambientCoefficientGradedRingHom (algebraMap k K)) B0) := by
      rw [← hB]
      exact hTwisted
    exact groundTwistedCubicPresentation_of_geometricallyStandardTwistedCubic
      (AllCharacteristics.geometricallyStandardTwistedCubic_of_algebraicClosure_groundPresentation hbar)

end PfaffianDescent.QuarticNet
