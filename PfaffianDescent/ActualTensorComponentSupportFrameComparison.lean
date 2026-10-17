import PfaffianDescent.ActualTensorSuppliedComponentRestriction
import PfaffianDescent.ActualComponentEpsilonCoproductSquare

/-! SOURCE ONLY, UNVERIFIED. Derive the support labeling and canonical
presentations on SAME actual components before comparing an independently
supplied epsilon presentation. No rho, canonical source iso, canonical
ambient square, matrix equality or epsilon comparison is an input. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial Module TrivSqZeroExt
open AllCharacteristics.HomogeneousProjective
open scoped TensorProduct
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem actual_scaled_relabeled_frame_vertex_square
    (b supplied : Basis (Fin 4) K (Fin 4 → K)) (j : Fin 4)
    (hb : ∀ r, b r j = 1) (rho : Equiv.Perm (Fin 4))
    (hc : ∀ i, supplied i j ≠ 0)
    (hBasis : supplied = QuarticNet.scaledRelabeledFrame b rho
      (fun i => Units.mk0 (supplied i j) (hc i))) (i : Fin 4) :
    (coordinateVertexMap (K := K) i ≫ quotientProjMap ⊥) ≫
      (linearCoordinateChangeAmbientIso (QuarticNet.basisCoordinateMatrix supplied)
        (QuarticNet.basisCoordinateMatrix_isUnit supplied)).inv =
      ambientNormalizedCoordinateChartPoint (F := K) (b (rho i)) j (hb (rho i)) := by
  have hColumn (s : Fin 4) : supplied i s = supplied i j * b (rho i) s := by
    calc
      _ = QuarticNet.scaledRelabeledFrame b rho
          (fun r => Units.mk0 (supplied r j) (hc r)) i s :=
        congrArg (fun e : Basis (Fin 4) K (Fin 4 → K) => e i s) hBasis
      _ = _ := by rw [QuarticNet.scaledRelabeledFrame_column]; rfl
  have hNormalized : (fun s => supplied i s / supplied i j) = b (rho i) := by
    funext s
    rw [hColumn s]
    field_simp [hc i]
  have h := actual_frame_vertex_column_square (QuarticNet.basisCoordinateMatrix supplied)
    (QuarticNet.basisCoordinateMatrix_isUnit supplied) i j (hc i)
  change _ = ambientNormalizedCoordinateChartPoint (F := K)
    (fun s => supplied i s / supplied i j) j _ at h
  have hPointCongr (a b : Fin 4 → K) (ha : a j = 1) (hb : b j = 1)
      (hab : a = b) : ambientNormalizedCoordinateChartPoint (F := K) a j ha =
        ambientNormalizedCoordinateChartPoint (F := K) b j hb := by
    subst b
    rfl
  exact h.trans (hPointCongr _ _ _ _ hNormalized)

section Tensor
variable {k L A : Type u} [Field k] [Field L] [CommRing A]
  [Algebra k L] [Algebra k K] [Algebra k A]
  [IsAlgClosed K] [FiniteDimensional k L] [Algebra.IsSeparable k L]
  [FiniteDimensional k A]

theorem actualTensor_original_supplied_component_frame_comparison
    (eA : A ≃ₐ[k] DualNumber L) (x : Fin 4 → A)
    (hgen : Function.Surjective (aeval (R := k) x))
    (b : Basis (Fin 4) k L) (v : Fin 4 → L)
    (hx : ∀ m, eA (x m) = inl (b m) + inr (v m))
    (full : Fin 4 ≃ (L →ₐ[k] K)) (j : Fin 4) (hxj : x j = 1)
    (supplied : Basis (Fin 4) K (Fin 4 → K))
    (hFrameSupport : Set.range (fun i =>
      (linearCoordinateChangeAmbientIso (QuarticNet.basisCoordinateMatrix supplied)
        (QuarticNet.basisCoordinateMatrix_isUnit supplied)).inv
          (actualVertexAmbientPoint (K := K) i)) =
      Set.range (fun r => ambientNormalizedCoordinateChartPoint (F := K)
        (QuarticNet.conjugateBasis full b (QuarticNet.conjugate_basis_span b full) r) j
        (QuarticNet.actualDual_normalized_chart_conjugate_basis_one eA x b v hx full j hxj r)
        (IsLocalRing.closedPoint K)))
    (Y : Fin 4 → Scheme.{u})
    (c : ∀ i, Y i ⟶ Spec (.of (K ⊗[k] A))) [∀ i, IsClosedImmersion (c i)]
    (hComponentSupport : ∀ i, Set.range (c i ≫ ambientNormalizedCoordinateChartPoint (F := K)
      (fun m => (1 : K) ⊗ₜ[k] x m) j (tensor_coordinate_eq_one x j hxj)) =
      {(linearCoordinateChangeAmbientIso (QuarticNet.basisCoordinateMatrix supplied)
        (QuarticNet.basisCoordinateMatrix_isUnit supplied)).inv
          (actualVertexAmbientPoint (K := K) i)})
    (hRank : ∀ i, AllCharacteristics.finiteSchemeRank
      (c i ≫ actualTensorOriginalToBase (k := k) (K := K) (A := A)) = 2) :
    let cb := QuarticNet.conjugateBasis full b (QuarticNet.conjugate_basis_span b full)
    let U := QuarticNet.conjugateTangentMatrix full b v (QuarticNet.conjugate_basis_span b full)
    let qt := ambientNormalizedCoordinateChartPoint (F := K)
      (fun m => (1 : K) ⊗ₜ[k] x m) j (tensor_coordinate_eq_one x j hxj)
    ∃ (rho : Equiv.Perm (Fin 4)) (hc : ∀ i, supplied i j ≠ 0)
      (canonicalE : ∀ i, Y i ≅ Spec (.of (DualNumber K))),
      (∀ i, (canonicalE i).hom ≫ ambientNormalizedCoordinateChartPoint (F := K)
        (QuarticNet.tangentDualPoint U (rho i)) (rho i)
        (by simp [U, QuarticNet.tangentDualPoint, QuarticNet.conjugateTangentMatrix_diagonal]) ≫
        (linearCoordinateChangeAmbientIso (QuarticNet.basisCoordinateMatrix cb)
          (QuarticNet.basisCoordinateMatrix_isUnit cb)).inv = c i ≫ qt) ∧
      ∀ (V : Fin 4 → Fin 4 → K) (hV : ∀ i, V i i = 0)
        (suppliedE : ∀ i, Y i ≅ Spec (.of (DualNumber K))),
      (∀ i, (suppliedE i).hom ≫ ambientNormalizedCoordinateChartPoint (F := K)
        (QuarticNet.tangentDualPoint V i) i (by simp [QuarticNet.tangentDualPoint, hV]) ≫
        (linearCoordinateChangeAmbientIso (QuarticNet.basisCoordinateMatrix supplied)
          (QuarticNet.basisCoordinateMatrix_isUnit supplied)).inv = c i ≫ qt) →
      ∃ (epsilon : Fin 4 → K) (hepsilon : ∀ i, epsilon i ≠ 0),
        V = QuarticNet.suppliedFrameTangent U rho (fun i => supplied i j) epsilon ∧
        (∀ i, (suppliedE i).hom ≫ Spec.map (CommRingCat.ofHom
          (QuarticNet.dualNumberRescaleEquiv (epsilon i) (hepsilon i)).toRingHom) =
          (canonicalE i).hom) ∧
        (actualComponentProductDualIso Y suppliedE).hom ≫
          Spec.map (CommRingCat.ofHom
            (QuarticNet.fourTangentDualRescaleEquiv epsilon hepsilon).toRingHom) =
          (actualComponentProductDualIso Y canonicalE).hom ∧
        ((∀ i s, V i s = -V s i) → (∃ i s, i ≠ s ∧ V i s = 0) →
          ∃ l : Fin 4 → K, (∀ r, l r ≠ 0) ∧
            (∀ r s, QuarticNet.rescaleTangentDirections l U r s =
              -QuarticNet.rescaleTangentDirections l U s r) ∧
            (∃ r s, r ≠ s ∧ U r s = 0)) := by
  let cb := QuarticNet.conjugateBasis full b (QuarticNet.conjugate_basis_span b full)
  let U := QuarticNet.conjugateTangentMatrix full b v (QuarticNet.conjugate_basis_span b full)
  let qt := ambientNormalizedCoordinateChartPoint (F := K)
    (fun m => (1 : K) ⊗ₜ[k] x m) j (tensor_coordinate_eq_one x j hxj)
  have hb : ∀ r, cb r j = 1 :=
    QuarticNet.actualDual_normalized_chart_conjugate_basis_one eA x b v hx full j hxj
  obtain ⟨rho, hc, hBasis⟩ := actual_supplied_frame_support_labeling_and_basis_comparison
    cb supplied j hb hFrameSupport
  have hSupport : ∀ i, Set.range (c i ≫ qt) =
      {ambientNormalizedCoordinateChartPoint (F := K) (cb (rho i)) j (hb (rho i))
        (IsLocalRing.closedPoint K)} := by
    intro i
    rw [hComponentSupport i]
    apply congrArg (fun p => ({p} : Set (Proj (homogeneousSubmodule (Fin 4) K))))
    exact congrArg (fun f => f (IsLocalRing.closedPoint K))
      (actual_scaled_relabeled_frame_vertex_square cb supplied j hb rho hc hBasis i)
  obtain ⟨canonicalE, hCanonical⟩ := actualTensor_supplied_components_canonical_presentations
    eA x hgen b v hx full j hxj Y c rho hSupport hRank
  refine ⟨rho, hc, canonicalE, hCanonical, ?_⟩
  intro V hV suppliedE hSupplied
  obtain ⟨epsilon, hepsilon, hEq, hSquares⟩ := actual_same_component_frame_epsilon_transfer
    cb supplied j hb rho hc hBasis Y (fun i => c i ≫ qt) U V
    (QuarticNet.conjugateTangentMatrix_diagonal full b v (QuarticNet.conjugate_basis_span b full))
    hV canonicalE suppliedE hCanonical hSupplied
  refine ⟨epsilon, hepsilon, hEq, hSquares,
    actual_component_epsilon_coproduct_square Y canonicalE suppliedE epsilon hepsilon hSquares, ?_⟩
  intro hSkew hMissing
  exact QuarticNet.suppliedFrameTangent_skew_missing_to_canonical U V rho
    (fun i => supplied i j) epsilon hc hepsilon hEq hSkew hMissing

end Tensor
end PfaffianDescent
