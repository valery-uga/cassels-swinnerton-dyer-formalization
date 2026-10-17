import PfaffianDescent.SuppliedMatchingFrameLineIdealTransport
import PfaffianDescent.ActualTensorComponentSupportFrameComparison
import PfaffianDescent.OriginalDualCoordinatesAnyChartZeroEntryQuadraticGeometry

/-! SOURCE ONLY / UNVERIFIED. Supplied component/frame n=1 geometry gives
ONE actual quadratic E and its two exchanged skew lines, identified by exact
ideals with the GIVEN frame's matching lines. No frame, graph, field, line,
projector or descent comparison is an input. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial Module TrivSqZeroExt
open AllCharacteristics.HomogeneousProjective
open scoped TensorProduct
universe u
variable {k L A : Type u} [Field k] [PerfectField k] [Field L] [CommRing A]
  [Algebra k L] [Algebra k A] [FiniteDimensional k L] [FiniteDimensional k A]
  [Algebra.IsSeparable k L]
attribute [local instance] MvPolynomial.gradedAlgebra

private theorem supplied_matching_unique_neighbor_missing
    {K : Type u} [Field K] (V : Fin 4 → Fin 4 → K)
    (hOne : ∀ r, ∃! s, V r s ≠ 0) :
    ∃ r s, r ≠ s ∧ V r s = 0 := by
  classical
  by_cases h01 : V 0 1 = 0
  · exact ⟨0, 1, by decide, h01⟩
  · have h02 : V 0 2 = 0 := by
      by_contra h02
      obtain ⟨s, hs, hUnique⟩ := hOne 0
      have he : (1 : Fin 4) = 2 := (hUnique 1 h01).trans (hUnique 2 h02).symm
      exact (by decide : (1 : Fin 4) ≠ 2) he
    exact ⟨0, 2, by decide, h02⟩

/-- Ordinary literal algebra/frame/component data. For an original Z caller,
A is Gamma(Z), x is its GIVEN original affine chart tuple, eA is its residue
 dual presentation and c its actual geometric component inclusions into the
true field base change. The hypotheses assert those concrete presentations,
not any desired quadratic-line or comparison conclusion. The original
ambient map is qt throughout, with the SAME ambient coordinate order. -/
theorem actualTensor_original_supplied_matching_quadratic_line_pair
    (eA : A ≃ₐ[k] DualNumber L) (x : Fin 4 → A)
    (hgen : Function.Surjective (aeval (R := k) x))
    (b : Basis (Fin 4) k L) (v : Fin 4 → L)
    (hx : ∀ m, eA (x m) = inl (b m) + inr (v m))
    (full : Fin 4 ≃ (L →ₐ[k] AlgebraicClosure k)) (j : Fin 4) (hxj : x j = 1)
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (hFx : aeval (R := k) x F = 0)
    (supplied : Basis (Fin 4) (AlgebraicClosure k) (Fin 4 → AlgebraicClosure k))
    (hFrameSupport : Set.range (fun r =>
      (linearCoordinateChangeAmbientIso (QuarticNet.basisCoordinateMatrix supplied)
        (QuarticNet.basisCoordinateMatrix_isUnit supplied)).inv
          (actualVertexAmbientPoint (K := AlgebraicClosure k) r)) =
      Set.range (fun r => ambientNormalizedCoordinateChartPoint (F := AlgebraicClosure k)
        (QuarticNet.conjugateBasis full b (QuarticNet.conjugate_basis_span b full) r) j
        (QuarticNet.actualDual_normalized_chart_conjugate_basis_one eA x b v hx full j hxj r)
        (IsLocalRing.closedPoint (AlgebraicClosure k))))
    (Y : Fin 4 → Scheme.{u})
    (c : ∀ r, Y r ⟶ Spec (.of (AlgebraicClosure k ⊗[k] A)))
    [∀ r, IsClosedImmersion (c r)]
    (hComponentSupport : ∀ r, Set.range (c r ≫
      ambientNormalizedCoordinateChartPoint (F := AlgebraicClosure k)
        (fun m => (1 : AlgebraicClosure k) ⊗ₜ[k] x m) j (tensor_coordinate_eq_one x j hxj)) =
      {(linearCoordinateChangeAmbientIso (QuarticNet.basisCoordinateMatrix supplied)
        (QuarticNet.basisCoordinateMatrix_isUnit supplied)).inv
          (actualVertexAmbientPoint (K := AlgebraicClosure k) r)})
    (hRank : ∀ r, AllCharacteristics.finiteSchemeRank
      (c r ≫ actualTensorOriginalToBase (k := k) (K := AlgebraicClosure k) (A := A)) = 2)
    (V : Fin 4 → Fin 4 → AlgebraicClosure k) (hV : ∀ r, V r r = 0)
    (suppliedE : ∀ r, Y r ≅ Spec (.of (DualNumber (AlgebraicClosure k))))
    (hSupplied : ∀ r, (suppliedE r).hom ≫
      ambientNormalizedCoordinateChartPoint (F := AlgebraicClosure k)
        (QuarticNet.tangentDualPoint V r) r (by simp [QuarticNet.tangentDualPoint, hV]) ≫
      (linearCoordinateChangeAmbientIso (QuarticNet.basisCoordinateMatrix supplied)
        (QuarticNet.basisCoordinateMatrix_isUnit supplied)).inv =
      c r ≫ ambientNormalizedCoordinateChartPoint (F := AlgebraicClosure k)
        (fun m => (1 : AlgebraicClosure k) ⊗ₜ[k] x m) j (tensor_coordinate_eq_one x j hxj))
    (hSkew : ∀ r s, V r s = -V s r) (hOne : ∀ r, ∃! s, V r s ≠ 0) :
    OriginalMatchingQuadraticLinePairOnSuppliedFrame F hF supplied V := by
  classical
  let K := AlgebraicClosure k
  let cb := QuarticNet.conjugateBasis full b (QuarticNet.conjugate_basis_span b full)
  let U := QuarticNet.conjugateTangentMatrix full b v (QuarticNet.conjugate_basis_span b full)
  let qt := ambientNormalizedCoordinateChartPoint (F := K)
    (fun m => (1 : K) ⊗ₜ[k] x m) j (tensor_coordinate_eq_one x j hxj)
  have hb : ∀ r, cb r j = 1 :=
    QuarticNet.actualDual_normalized_chart_conjugate_basis_one eA x b v hx full j hxj
  obtain ⟨rho, hc, hBasis⟩ := actual_supplied_frame_support_labeling_and_basis_comparison
    cb supplied j hb hFrameSupport
  have hSupport : ∀ r, Set.range (c r ≫ qt) =
      {ambientNormalizedCoordinateChartPoint (F := K) (cb (rho r)) j (hb (rho r))
        (IsLocalRing.closedPoint K)} := by
    intro r
    rw [hComponentSupport r]
    apply congrArg (fun z => ({z} : Set (Proj (homogeneousSubmodule (Fin 4) K))))
    exact congrArg (fun f => f (IsLocalRing.closedPoint K))
      (actual_scaled_relabeled_frame_vertex_square cb supplied j hb rho hc hBasis r)
  obtain ⟨canonicalE, hCanonical⟩ := actualTensor_supplied_components_canonical_presentations
    eA x hgen b v hx full j hxj Y c rho hSupport hRank
  obtain ⟨epsilon, hepsilon, hEq, hSquares⟩ := actual_same_component_frame_epsilon_transfer
    cb supplied j hb rho hc hBasis Y (fun r => c r ≫ qt) U V
    (QuarticNet.conjugateTangentMatrix_diagonal full b v (QuarticNet.conjugate_basis_span b full))
    hV canonicalE suppliedE hCanonical hSupplied
  obtain ⟨l, hl, hCanonicalSkew, hCanonicalMissing⟩ :=
    QuarticNet.suppliedFrameTangent_skew_missing_to_canonical U V rho
      (fun r => supplied r j) epsilon hc hepsilon hEq hSkew
      (supplied_matching_unique_neighbor_missing V hOne)
  have hOneCanonical := QuarticNet.suppliedFrameTangent_unique_neighbor_to_rescaled_canonical
    U V rho (fun r => supplied r j) epsilon l hc hepsilon hl hEq hOne
  have hMissingScaled : ∃ r s, r ≠ s ∧ QuarticNet.rescaleTangentDirections l U r s = 0 := by
    obtain ⟨r, s, hrs, hz⟩ := hCanonicalMissing
    exact ⟨r, s, hrs, by simp only [QuarticNet.rescaleTangentDirections, hz, mul_zero]⟩
  have hbj : b j = 1 := by
    have h := congrArg TrivSqZeroExt.fst (hx j)
    simpa only [hxj, map_one, fst_one, fst_add, fst_inl, fst_inr, add_zero] using h.symm
  have hvj : v j = 0 := by
    have h := congrArg TrivSqZeroExt.snd (hx j)
    simpa only [hxj, map_one, snd_one, snd_add, snd_inl, snd_inr, zero_add] using h.symm
  have hv : v ≠ 0 := by
    intro hz
    have hsnd (r : Fin 4) : (eA (x r)).snd = 0 := by rw [hx r]; simp [hz]
    have hconst : eA.toAlgHom.comp (aeval x) =
        (inlAlgHom k _ _).comp (aeval (fun r => (eA (x r)).fst)) := by
      apply MvPolynomial.algHom_ext
      intro r
      change eA (aeval x (X r)) = inl (aeval (fun s => (eA (x s)).fst) (X r))
      rw [aeval_X, aeval_X]
      apply TrivSqZeroExt.ext
      · rfl
      · exact hsnd r
    obtain ⟨q, hq⟩ := (eA.surjective.comp hgen) (inr (1 : L))
    change (eA.toAlgHom.comp (aeval x)) q = _ at hq
    rw [hconst] at hq
    have h := congrArg TrivSqZeroExt.snd hq
    change (0 : L) = 1 at h
    exact zero_ne_one h
  have hGeometry := QuarticNet.originalDualCoordinates_any_chart_matching_quadratic_line_geometry
    eA x j hxj b v hx hbj hvj hv full F hF hFx
    l hl hCanonicalSkew hMissingScaled hOneCanonical
  exact QuarticNet.originalMatching_pair_on_supplied_frame_of_actual_comparison
    F hF cb supplied U V rho (fun r => Units.mk0 (supplied r j) (hc r))
    epsilon hepsilon hBasis hEq l hl hGeometry

end PfaffianDescent
