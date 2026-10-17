import PfaffianDescent.ActualTensorCanonicalFactorAmbientSquare
import PfaffianDescent.ActualTensorCoordinateFiniteEmbedding

/-! SOURCE ONLY, UNVERIFIED. Restrict the true eA/tensor splitting to actual
supplied components, rather than choosing unrelated canonical components.
The global Spec iso, closed immersion, base square and canonical component
ambient squares are derived here; none is a comparison premise. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial Module TrivSqZeroExt
open AllCharacteristics.HomogeneousProjective
open scoped TensorProduct
universe u
variable {k L K A : Type u} [Field k] [Field L] [Field K] [CommRing A]
  [Algebra k L] [Algebra k K] [Algebra k A]
  [IsAlgClosed K] [FiniteDimensional k L] [Algebra.IsSeparable k L]
  [FiniteDimensional k A]
attribute [local instance] MvPolynomial.gradedAlgebra

def actualTensorOriginalToBase : Spec (.of (K ⊗[k] A)) ⟶ Spec (.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K (K ⊗[k] A)))

instance : IsFinite (actualTensorOriginalToBase (k := k) (K := K) (A := A)) := by
  unfold actualTensorOriginalToBase
  exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)

theorem actualTensor_supplied_components_canonical_presentations
    (eA : A ≃ₐ[k] DualNumber L) (x : Fin 4 → A)
    (hgen : Function.Surjective (aeval (R := k) x))
    (b : Basis (Fin 4) k L) (v : Fin 4 → L)
    (hx : ∀ m, eA (x m) = inl (b m) + inr (v m))
    (full : Fin 4 ≃ (L →ₐ[k] K)) (j : Fin 4) (hxj : x j = 1)
    (Y : Fin 4 → Scheme.{u})
    (c : ∀ i, Y i ⟶ Spec (.of (K ⊗[k] A))) [∀ i, IsClosedImmersion (c i)]
    (rho : Equiv.Perm (Fin 4))
    (hSupport : ∀ i, Set.range (c i ≫ ambientNormalizedCoordinateChartPoint (F := K)
        (fun m => (1 : K) ⊗ₜ[k] x m) j (tensor_coordinate_eq_one x j hxj)) =
      {ambientNormalizedCoordinateChartPoint (F := K)
        (QuarticNet.conjugateBasis full b (QuarticNet.conjugate_basis_span b full) (rho i)) j
        (QuarticNet.actualDual_normalized_chart_conjugate_basis_one eA x b v hx full j hxj (rho i))
        (IsLocalRing.closedPoint K)})
    (hRank : ∀ i, AllCharacteristics.finiteSchemeRank
      (c i ≫ actualTensorOriginalToBase (k := k) (K := K) (A := A)) = 2) :
    ∃ e : ∀ i, Y i ≅ Spec (.of (DualNumber K)),
      ∀ i, (e i).hom ≫
        ambientNormalizedCoordinateChartPoint (F := K)
          (QuarticNet.tangentDualPoint
            (QuarticNet.conjugateTangentMatrix full b v (QuarticNet.conjugate_basis_span b full))
            (rho i)) (rho i)
          (by simp [QuarticNet.tangentDualPoint, QuarticNet.conjugateTangentMatrix_diagonal]) ≫
        (linearCoordinateChangeAmbientIso
          (QuarticNet.basisCoordinateMatrix
            (QuarticNet.conjugateBasis full b (QuarticNet.conjugate_basis_span b full)))
          (QuarticNet.basisCoordinateMatrix_isUnit _)).inv =
        c i ≫ ambientNormalizedCoordinateChartPoint (F := K)
          (fun m => (1 : K) ⊗ₜ[k] x m) j (tensor_coordinate_eq_one x j hxj) := by
  let theta := QuarticNet.actualQuarticDualTensorEquiv eA b full
  let eWhole := Scheme.Spec.mapIso theta.toRingEquiv.toCommRingCatIso.symm.op
  let qt := ambientNormalizedCoordinateChartPoint (F := K)
    (fun m => (1 : K) ⊗ₜ[k] x m) j (tensor_coordinate_eq_one x j hxj)
  let qp := QuarticNet.actualTensorProductDualOriginalAmbient eA x b full j hxj
  letI : IsClosedImmersion qt := ambientNormalizedCoordinateChartPoint_isClosedImmersion _ _ _
    (tensorCoordinates_aeval_surjective x hgen)
  have hqp : qp = eWhole.inv ≫ qt :=
    ambientNormalizedCoordinateChartPoint_algHom theta.toAlgHom _ _ _
  letI : IsClosedImmersion qp := by rw [hqp]; infer_instance
  have hWhole : eWhole.hom ≫ qp = qt := by
    rw [hqp, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  letI : ∀ i, IsFinite ((c i ≫ qt) ≫ ambientToBase) := by
    intro i
    rw [Category.assoc, ambientNormalizedCoordinateChartPoint_toBase]
    letI : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap K (K ⊗[k] A)))) :=
      (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
    infer_instance
  have hRank' : ∀ i, AllCharacteristics.finiteSchemeRank ((c i ≫ qt) ≫ ambientToBase) = 2 := by
    intro i
    have hMap : (c i ≫ qt) ≫ ambientToBase = c i ≫ actualTensorOriginalToBase := by
      rw [Category.assoc, ambientNormalizedCoordinateChartPoint_toBase]
      rfl
    simpa only [hMap] using hRank i
  obtain ⟨e, he, hq⟩ := actualProductDual_original_component_presentations
    eWhole qt qp hWhole
    (QuarticNet.actualTensorProductDualOriginalAmbient_toBase eA x b full j hxj)
    Y c rho
    (fun r => ambientNormalizedCoordinateChartPoint (F := K)
      (QuarticNet.conjugateBasis full b (QuarticNet.conjugate_basis_span b full) r) j
      (QuarticNet.actualDual_normalized_chart_conjugate_basis_one eA x b v hx full j hxj r)
      (IsLocalRing.closedPoint K))
    (QuarticNet.actualTensorProductDual_factor_actual_support_point eA x b v hx full j hxj)
    hSupport hRank'
  refine ⟨e, ?_⟩
  intro i
  rw [← QuarticNet.actualTensorProductDual_factor_original_ambient_square eA x b v hx full j hxj]
  exact hq i

end PfaffianDescent
