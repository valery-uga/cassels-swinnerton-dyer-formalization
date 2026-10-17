import PfaffianDescent.SingleSupportOriginalOrderH0SkewTangent
import PfaffianDescent.ActualOriginalOrderTensorSkewComponentSquare
import PfaffianDescent.ActualSuppliedChartTensorEmbedding
import PfaffianDescent.ActualTensorCoordinateFiniteEmbedding
import PfaffianDescent.ActualComponentEpsilonCoproductSquare
import PfaffianDescent.OriginalDualCoordinatesAnyChartZeroEntryQuadraticGeometry
import PfaffianDescent.IntrinsicFullBaseAlternativeSourceIso

/-! SOURCE ONLY, UNVERIFIED. Primitive original-Z / genuine H0 caller for
the manuscript's n=1 branch. The actual residue basis, geometric frame,
components, ranks, ambient embedding, skew weights, graph and Galois data
are derived internally. The one-neighbor case is a condition on the derived
actual graph IN THE CONCLUSION, never a supplied matching certificate.
General position alone does not imply n=1 or the skew H0 hypothesis. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial Module TrivSqZeroExt
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
open QuarticNet
open scoped TensorProduct
universe u
variable {k : Type u} [Field k] [PerfectField k]
attribute [local instance] MvPolynomial.gradedAlgebra

private theorem uniqueNeighbor_missing_entry
    {K : Type u} [Field K] (U : Fin 4 → Fin 4 → K)
    (hOne : ∀ r, ∃! s, U r s ≠ 0) :
    ∃ r s, r ≠ s ∧ U r s = 0 := by
  classical
  by_cases h01 : U 0 1 = 0
  · exact ⟨0, 1, by decide, h01⟩
  · have h02 : U 0 2 = 0 := by
      by_contra h02
      obtain ⟨s, hs, hUnique⟩ := hOne 0
      have he : (1 : Fin 4) = 2 := (hUnique 1 h01).trans (hUnique 2 h02).symm
      exact (by decide : (1 : Fin 4) ≠ 2) he
    exact ⟨0, 2, by decide, h02⟩

/-- The SAME original rank-eight jet supplies actual four dual components
and its original-order skew graph. In its literal n=1 branch the SINGLE
quadratic field and BOTH exchanged skew lines are derived by the internally
proved matching/projector/descent construction, with the original cubic
and conjugate frame retained. The C4 alternative is not suppressed. -/
theorem singleSupport_originalZ_actual_H0_quadratic_line_pair_geometry
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3)
    {Z : Scheme.{u}} (i : Z ⟶ scheme (equationIdeal p hp)) [IsClosedImmersion i]
    [IsFinite (i ≫ toBase (equationIdeal p hp))]
    (P : closedPoints (scheme (equationIdeal p hp)))
    (hSupport : Set.range i = {P.1})
    (hP : (toBase (equationIdeal p hp)).residueDegree P.1 = 4)
    (hGeom : ProjectiveGeometricGeneralPosition (equationIdeal p hp)
      ((scheme (equationIdeal p hp)).fromSpecResidueField P.1))
    (hdim : 3 ≤ finrank k (ActualP3IdealQuadraticHZero
      (i ≫ quotientProjMap (equationIdeal p hp)))) :
    letI : IsAffine Z := isAffine_of_isAffineHom (i ≫ toBase (equationIdeal p hp))
    letI := finiteSchemeCoefficientAlgebra (i ≫ toBase (equationIdeal p hp))
    letI := finiteSchemeCoefficient_finite (i ≫ toBase (equationIdeal p hp))
    letI := AllCharacteristics.pointAlgebra (toBase (equationIdeal p hp)) P.1
    letI := AllCharacteristics.closedPoint_moduleFinite (toBase (equationIdeal p hp)) P
    (AllCharacteristics.finiteSchemeRank (i ≫ toBase (equationIdeal p hp)) = 8) →
    ∃ (j : Fin 4) (x : Fin 4 → Γ(Z, ⊤)) (hxj : x j = 1)
      (eA : Γ(Z, ⊤) ≃ₐ[k] DualNumber ((scheme (equationIdeal p hp)).residueField P.1))
      (b : Basis (Fin 4) k ((scheme (equationIdeal p hp)).residueField P.1))
      (v : Fin 4 → (scheme (equationIdeal p hp)).residueField P.1)
      (full : Fin 4 ≃ ((scheme (equationIdeal p hp)).residueField P.1 →ₐ[k] AlgebraicClosure k))
      (l : Fin 4 → AlgebraicClosure k) (hl : ∀ r, l r ≠ 0),
      let K := AlgebraicClosure k
      let B := conjugateBasis full b (conjugate_basis_span b full)
      let U := rescaleTangentDirections l
        (conjugateTangentMatrix full b v (conjugate_basis_span b full))
      let S := actualOriginalOrderQuarticSchemeIso (i ≫ toBase (equationIdeal p hp)) eA b full
      let Q := (finiteSchemeActualFieldBaseChangeIso (K := K)
        (i ≫ toBase (equationIdeal p hp))).hom ≫
        ambientNormalizedCoordinateChartPoint (F := K)
          (fun r => (1 : K) ⊗ₜ[k] x r) j (tensor_coordinate_eq_one x j hxj)
      let tQ := pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k K)))
        (i ≫ toBase (equationIdeal p hp))
      let c := fun r : Fin 4 => actualProductDualFactor (K := K) r ≫ S.inv
      letI : ∀ r, IsClosedImmersion (c r) := fun r => by dsimp only [c]; infer_instance
      letI : ∀ r, IsFinite (c r ≫ tQ) := fun r => by dsimp only [tQ]; infer_instance
      b j = 1 ∧ v j = 0 ∧ v ≠ 0 ∧
      Function.Surjective (aeval (R := k) x) ∧
      (∀ r, eA (x r) = inl (b r) + inr (v r)) ∧
      ambientNormalizedCoordinateChartPoint (F := k) x j hxj =
        Z.isoSpec.inv ≫ i ≫ quotientProjMap (equationIdeal p hp) ∧
      aeval (R := k) x p = 0 ∧
      (∀ r, U r r = 0) ∧ (∀ r s, U r s = -U s r) ∧
      (∀ r, ∃ s, U r s ≠ 0) ∧
      Q ≫ ambientCoefficientMap (algebraMap k K) =
        pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k K)))
          (i ≫ toBase (equationIdeal p hp)) ≫ i ≫ quotientProjMap (equationIdeal p hp) ∧
      Q ≫ ambientToBase (R := K) = tQ ∧
      (∀ r, c r ≫ tQ = actualDualToBase) ∧
      (∀ r, AllCharacteristics.finiteSchemeRank (c r ≫ tQ) = 2) ∧
      (∀ r, ∃ hB : B r j = 1,
        Set.range (c r ≫ Q) =
          {ambientNormalizedCoordinateChartPoint (F := K) (B r) j hB (IsLocalRing.closedPoint K)}) ∧
      (Pairwise fun r s => Disjoint (Set.range (c r)) (Set.range (c s))) ∧
      IsIso (Sigma.desc c) ∧
      (∀ r, Spec.map (CommRingCat.ofHom (dualNumberRescaleEquiv (l r) (hl r)).toRingHom) ≫
        c r ≫ Q =
        ambientNormalizedCoordinateChartPoint (F := K) (tangentDualPoint U r) r
          (by simp [U, tangentDualPoint, rescaleTangentDirections, conjugateTangentMatrix_diagonal]) ≫
        (linearCoordinateChangeAmbientIso (basisCoordinateMatrix B)
          (basisCoordinateMatrix_isUnit B)).inv) ∧
      ((∃ r s, r ≠ s ∧ U r s = 0) →
        ZeroEntryTangentSupportClassification U) ∧
      ((∀ r, ∃! s, U r s ≠ 0) → OriginalMatchingQuadraticLineGeometryAt p hp B U) ∧
      ((∃ r s, r ≠ s ∧ U r s = 0) →
        OriginalEmbeddedZeroEntryQuadraticGeometry p hp
          (i ≫ quotientProjMap (equationIdeal p hp))) := by
  classical
  let I := equationIdeal p hp
  letI : IsAffine Z := isAffine_of_isAffineHom (i ≫ toBase I)
  letI := finiteSchemeCoefficientAlgebra (i ≫ toBase I)
  letI := finiteSchemeCoefficient_finite (i ≫ toBase I)
  letI := AllCharacteristics.pointAlgebra (toBase I) P.1
  letI := AllCharacteristics.closedPoint_moduleFinite (toBase I) P
  intro hZ
  obtain ⟨j, g, x, eA, b, v, full, l, hxj, hgen, hbase, hb, hvj, hv,
    hxg, hpoint, hx, hl, hrow, hskew⟩ :=
    singleSupport_actual_H0_original_order_skew_tangents I i P hSupport hP hGeom hdim hZ
  let K := AlgebraicClosure k
  let B := conjugateBasis full b (conjugate_basis_span b full)
  let U0 := conjugateTangentMatrix full b v (conjugate_basis_span b full)
  let U := rescaleTangentDirections l U0
  let S := actualOriginalOrderQuarticSchemeIso (i ≫ toBase I) eA b full
  let Q := (finiteSchemeActualFieldBaseChangeIso (K := K) (i ≫ toBase I)).hom ≫
    ambientNormalizedCoordinateChartPoint (F := K)
      (fun r => (1 : K) ⊗ₜ[k] x r) j (tensor_coordinate_eq_one x j hxj)
  let tQ := pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k K))) (i ≫ toBase I)
  let c := fun r : Fin 4 => actualProductDualFactor (K := K) r ≫ S.inv
  letI : ∀ r, IsClosedImmersion (c r) := fun r => by dsimp only [c]; infer_instance
  letI : ∀ r, IsFinite (c r ≫ tQ) := fun r => by dsimp only [tQ]; infer_instance
  have hOriginal : ambientNormalizedCoordinateChartPoint (F := k) x j hxj =
      Z.isoSpec.inv ≫ i ≫ quotientProjMap I := by
    have h := ambientNormalizedCoordinateChartPoint_eq_original_chart I j g hbase
    have hCoordinates : (fun r => g (chartCoordinate I j r)) = x :=
      funext (fun r => (hxg r).symm)
    rw [hCoordinates] at h
    rw [h, ← Category.assoc, hpoint, Category.assoc]
  have hFx : aeval (R := k) x p = 0 := by
    have h := congrArg g (eval₂_chartCoordinate_eq_zero_of_mem I j p
      (show p ∈ I.toIdeal from Ideal.subset_span (Set.mem_singleton _)))
    have hCoordinates : (fun r => g (chartCoordinate I j r)) = x :=
      funext (fun r => (hxg r).symm)
    rw [hom_eval₂, hbase, hCoordinates, map_zero] at h
    exact h
  have hdiag : ∀ r, U r r = 0 := by
    intro r
    simp [U, U0, rescaleTangentDirections, conjugateTangentMatrix_diagonal]
  have hskewU : ∀ r s, U r s = -U s r := hskew
  have hnonzero : ∀ r, ∃ s, U r s ≠ 0 := by
    intro r
    obtain ⟨s, hs⟩ := hrow r
    exact ⟨s, (rescaleTangentDirections_nonzero U0 l hl r s).mpr hs⟩
  obtain ⟨hOriginalSquare, hField⟩ := actualSuppliedChart_tensor_ambient_squares
    (K := K) I i j g hbase hpoint x hxg hxj
  have hWhole : S.inv ≫ Q = actualTensorProductDualOriginalAmbient eA x b full j hxj :=
    actualOriginalOrderQuarticSchemeIso_original_ambient_square (i ≫ toBase I) eA x j hxj b full
  have hWholeBase : S.inv ≫ tQ = actualProductDualToBase := by
    calc
      S.inv ≫ tQ = S.inv ≫ Q ≫ ambientToBase := by rw [← hField]
      _ = actualTensorProductDualOriginalAmbient eA x b full j hxj ≫ ambientToBase := by
        simpa only [Category.assoc] using congrArg (fun f => f ≫ ambientToBase) hWhole
      _ = actualProductDualToBase := actualTensorProductDualOriginalAmbient_toBase eA x b full j hxj
  have hComponentsBase : ∀ r, c r ≫ tQ = actualDualToBase := by
    intro r
    dsimp only [c]
    rw [Category.assoc, hWholeBase, actualProductDualFactor_toBase]
  have hComponentsRank : ∀ r, AllCharacteristics.finiteSchemeRank (c r ≫ tQ) = 2 := by
    intro r
    rw [hComponentsBase r]
    exact actualDualToBase_rank_two
  have hComponentsSupport : ∀ r, ∃ hB : B r j = 1,
      Set.range (c r ≫ Q) =
        {ambientNormalizedCoordinateChartPoint (F := K) (B r) j hB (IsLocalRing.closedPoint K)} := by
    intro r
    let hB : B r j = 1 := actualDual_normalized_chart_conjugate_basis_one eA x b v hx full j hxj r
    let red := Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom)
    have hEvery (z : Spec (.of (DualNumber K))) : z = red (IsLocalRing.closedPoint K) := by
      obtain ⟨w, hw⟩ := dualNumber_fst_spec_surjective z
      exact hw.symm.trans (congrArg red (Subsingleton.elim w (IsLocalRing.closedPoint K)))
    have hMap : c r ≫ Q = actualProductDualFactor r ≫
        actualTensorProductDualOriginalAmbient eA x b full j hxj := by
      dsimp only [c]
      rw [Category.assoc, hWhole]
    have hEval : (c r ≫ Q) (red (IsLocalRing.closedPoint K)) =
        ambientNormalizedCoordinateChartPoint (F := K) (B r) j hB (IsLocalRing.closedPoint K) := by
      rw [hMap]
      exact actualTensorProductDual_factor_actual_support_point eA x b v hx full j hxj r
    refine ⟨hB, ?_⟩
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      apply Set.mem_singleton_iff.mpr
      exact (congrArg (fun y => (c r ≫ Q) y) (hEvery y)).trans hEval
    · intro hz
      exact ⟨red (IsLocalRing.closedPoint K), hEval.trans (Set.mem_singleton_iff.mp hz).symm⟩
  let Y := fun _ : Fin 4 => Spec (.of (DualNumber K))
  let ePi := actualComponentProductDualIso Y (fun _ => Iso.refl _)
  let W := ePi ≪≫ S.symm
  have hComponent (r : Fin 4) : Sigma.ι Y r ≫ W.hom = c r := by
    simp only [W, Iso.trans_hom, Iso.symm_hom, ← Category.assoc]
    rw [actualComponentProductDualIso_component]
    simp only [Iso.refl_hom, Category.id_comp]
    rfl
  have hDisjoint : Pairwise fun r s => Disjoint (Set.range (c r)) (Set.range (c s)) := by
    intro r s hrs
    apply Set.disjoint_left.mpr
    rintro z ⟨xr, hxr⟩ ⟨ys, hys⟩
    have hr : W.hom (Sigma.ι Y r xr) = c r xr := by
      simpa only [Scheme.Hom.comp_apply] using congrArg (fun f => f xr) (hComponent r)
    have hs : W.hom (Sigma.ι Y s ys) = c s ys := by
      simpa only [Scheme.Hom.comp_apply] using congrArg (fun f => f ys) (hComponent s)
    have he : Sigma.ι Y r xr = Sigma.ι Y s ys :=
      W.hom.isClosedEmbedding.injective (hr.trans (hxr.trans (hys.symm.trans hs.symm)))
    exact hrs (congrArg Sigma.fst ((sigmaι_eq_iff Y r s xr ys).mp he))
  have hDesc : Sigma.desc c = W.hom := by
    apply Sigma.hom_ext
    intro r
    rw [Sigma.ι_desc]
    exact (hComponent r).symm
  have hWholeIso : IsIso (Sigma.desc c) := by rw [hDesc]; infer_instance
  refine ⟨j, x, hxj, eA, b, v, full, l, hl, hb, hvj, hv, hgen, hx,
    hOriginal, hFx, hdiag, hskewU, hnonzero, hOriginalSquare, hField,
    hComponentsBase, hComponentsRank, hComponentsSupport, hDisjoint, hWholeIso, ?_, ?_, ?_, ?_⟩
  · exact actualOriginalOrderQuarticSchemeIso_rescaled_component_frame_square
      (i ≫ toBase I) eA x j hxj b v hx full l hl
  · intro hMissing
    exact conjugateQuartic_any_chart_zero_entry_support_graph full b v
      (conjugate_basis_span b full) j hb hvj hv l hl hskewU hMissing
  · intro hOne
    exact originalDualCoordinates_any_chart_matching_quadratic_line_geometry
      eA x j hxj b v hx hb hvj hv full p hp hFx l hl hskewU
      (uniqueNeighbor_missing_entry U hOne) hOne
  · intro hMissing
    have hGeometry := originalDualCoordinates_any_chart_zero_entry_quadratic_geometry
      eA x j hxj b v hx hb hvj hv full p hp hFx l hl hskewU hMissing
    rcases hGeometry with hMatching | hFinite
    · exact Or.inl hMatching
    · have hBase : intrinsicFullQuadraticBaseIdeal
          (ambientNormalizedCoordinateChartPoint (F := k) x j hxj) =
          intrinsicFullQuadraticBaseIdeal (i ≫ quotientProjMap I) := by
        rw [hOriginal]
        exact intrinsicFullQuadraticBaseIdeal_comp_iso Z.isoSpec.symm (i ≫ quotientProjMap I)
      rw [hBase] at hFinite
      exact Or.inr hFinite

end PfaffianDescent
