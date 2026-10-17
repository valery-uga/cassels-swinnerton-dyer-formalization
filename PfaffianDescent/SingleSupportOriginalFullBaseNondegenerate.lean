import PfaffianDescent.ActualQuarticOriginalTensorFullBaseAlternative
import PfaffianDescent.IntrinsicFullBaseAlternativeSourceIso
import PfaffianDescent.SingleSupportActualTensorAmbientSquare
import PfaffianDescent.SingleSupportIntrinsicSkewTangent

/-! Actual supplied-Z extraction with the exact original field-base-change
embedding. The full-base classification is exported for its nondegenerate
coordinate branch. The remaining zero-entry cases and universal geometric
four-component parametrization are not claimed by this declaration. -/

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial Module
open AllCharacteristics.HomogeneousProjective
open scoped TensorProduct
universe u
variable {k : Type u} [Field k] [PerfectField k]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- All coordinate, dual-algebra, and embedding comparisons are derived
from the originally supplied closed scheme. Nondegeneracy is a condition on
the extracted actual tangents in the conclusion, not a supplied comparison
certificate or an assertion that every skew matrix has full support. -/
theorem singleSupport_original_fullBase_nondegenerate_branch
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) k))
    {Z : Scheme.{u}} (i : Z ⟶ scheme I) [IsClosedImmersion i]
    [IsFinite (i ≫ toBase I)] (P : closedPoints (scheme I))
    (hSupport : Set.range i = {P.1})
    (hP : (toBase I).residueDegree P.1 = 4)
    (hGeom : ProjectiveGeometricGeneralPosition I ((scheme I).fromSpecResidueField P.1))
    (hdim : 3 ≤ finrank k (intrinsicFullQuadraticSystem (i ≫ quotientProjMap I))) :
    letI : IsAffine Z := isAffine_of_isAffineHom (i ≫ toBase I)
    letI := finiteSchemeCoefficientAlgebra (i ≫ toBase I)
    letI := AllCharacteristics.pointAlgebra (toBase I) P.1
    letI := AllCharacteristics.closedPoint_moduleFinite (toBase I) P
    (AllCharacteristics.finiteSchemeRank (i ≫ toBase I) = 8) →
    ∃ (j : Fin 4) (x : Fin 4 → Γ(Z, ⊤)) (hxj : x j = 1)
      (eA : Γ(Z, ⊤) ≃ₐ[k] DualNumber ((scheme I).residueField P.1))
      (b : Basis (Fin 4) k ((scheme I).residueField P.1))
      (v : Fin 4 → (scheme I).residueField P.1) (pi : Equiv.Perm (Fin 4))
      (full : Fin 4 ≃ ((scheme I).residueField P.1 →ₐ[k] AlgebraicClosure k))
      (l : Fin 4 → AlgebraicClosure k),
      pi 0 = j ∧ b 0 = 1 ∧ v 0 = 0 ∧ (∀ r, l r ≠ 0) ∧
      (∀ r, eA (x (pi r)) = TrivSqZeroExt.inl (b r) + TrivSqZeroExt.inr (v r)) ∧
      let U := QuarticNet.conjugateTangentMatrix full b v
        (QuarticNet.conjugate_basis_span b full)
      let e := finiteSchemeActualFieldBaseChangeIso (K := AlgebraicClosure k) (i ≫ toBase I)
      let q := ambientNormalizedCoordinateChartPoint (F := AlgebraicClosure k)
        (fun r => (1 : AlgebraicClosure k) ⊗ₜ[k] x r) j (tensor_coordinate_eq_one x j hxj)
      (∀ r s, l r * U r s = -(l s * U s r)) ∧
      (e.hom ≫ q) ≫ ambientCoefficientMap (algebraMap k (AlgebraicClosure k)) =
        pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))
          (i ≫ toBase I) ≫ i ≫ quotientProjMap I ∧
      (e.hom ≫ q) ≫ ambientToBase (R := AlgebraicClosure k) =
        pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))
          (i ≫ toBase I) ∧
      ((∀ r s, r ≠ s → U r s ≠ 0) →
        QuarticNet.IntrinsicFullBaseEmbeddedAlternative (e.hom ≫ q)) := by
  letI : IsAffine Z := isAffine_of_isAffineHom (i ≫ toBase I)
  letI := finiteSchemeCoefficientAlgebra (i ≫ toBase I)
  letI := AllCharacteristics.pointAlgebra (toBase I) P.1
  intro hZ
  letI := finiteSchemeCoefficient_finite (i ≫ toBase I)
  letI := AllCharacteristics.closedPoint_moduleFinite (toBase I) P
  obtain ⟨j, g, x, eA, b, v, pi, full, hxj, hgen, hgb, hb, hv, hvne, hpi,
    hcoords, hpoint, hx, hspan, hactual, hgroundKernel, hnrows, l, hl,
    hskew, hrescaledKernel⟩ :=
    singleSupport_intrinsic_quadratics_actual_skew_tangents
      I i P hSupport hP hGeom hdim hZ
  let U := QuarticNet.conjugateTangentMatrix full b v
    (QuarticNet.conjugate_basis_span b full)
  let e := finiteSchemeActualFieldBaseChangeIso (K := AlgebraicClosure k) (i ≫ toBase I)
  let q := ambientNormalizedCoordinateChartPoint (F := AlgebraicClosure k)
    (fun r => (1 : AlgebraicClosure k) ⊗ₜ[k] x r) j (tensor_coordinate_eq_one x j hxj)
  have hqA : ambientNormalizedCoordinateChartPoint x j hxj =
      Z.isoSpec.inv ≫ i ≫ quotientProjMap I := by
    have h := ambientNormalizedCoordinateChartPoint_eq_original_chart I j g hgb
    have hcoordsEq : (fun r => g (chartCoordinate I j r)) = x :=
      funext (fun r => (hcoords r).symm)
    rw [hcoordsEq] at h
    rw [h, ← Category.assoc, hpoint, Category.assoc]
  refine ⟨j, x, hxj, eA, b, v, pi, full, l, hpi, hb, hv, hl, hx, hskew, ?_, ?_, ?_⟩
  · calc
      (e.hom ≫ q) ≫ ambientCoefficientMap (algebraMap k (AlgebraicClosure k)) =
          e.hom ≫ Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.includeRight : Γ(Z, ⊤) →ₐ[k]
              AlgebraicClosure k ⊗[k] Γ(Z, ⊤)).toRingHom) ≫
            ambientNormalizedCoordinateChartPoint x j hxj := by
        rw [Category.assoc]
        exact congrArg (fun f => e.hom ≫ f)
          (ambientNormalizedCoordinateChartPoint_tensor_coefficients
            (K := AlgebraicClosure k) x j hxj)
      _ = (e.hom ≫ Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.includeRight : Γ(Z, ⊤) →ₐ[k]
              AlgebraicClosure k ⊗[k] Γ(Z, ⊤)).toRingHom) ≫ Z.isoSpec.inv) ≫
          i ≫ quotientProjMap I := by rw [hqA]; simp only [Category.assoc]
      _ = _ := by rw [finiteSchemeActualFieldBaseChangeIso_hom_toOriginal]
  · rw [Category.assoc, ambientNormalizedCoordinateChartPoint_toBase]
    exact finiteSchemeActualFieldBaseChangeIso_hom_toField
      (K := AlgebraicClosure k) (i ≫ toBase I)
  · intro hnonzero
    exact QuarticNet.intrinsicFullBase_embedded_alternative_precomp_iso e q
      (QuarticNet.actualQuarticOriginalTensor_fullBase_embedded_alternative
        eA x hgen j hxj pi hpi b v hx hb hv full l hl hskew hnonzero)

end PfaffianDescent
