import PfaffianDescent.SingleSupportOriginalOrderDualChartData
import PfaffianDescent.ActualTensorComponentSupportFrameComparison
import PfaffianDescent.SingleSupportActualTensorAmbientSquare
import PfaffianDescent.ActualClosedComponentsCoproductIso
import PfaffianDescent.OriginalDualCoordinatesAnyChartZeroEntryMethodGeometry
import PfaffianDescent.IntrinsicFullBaseAlternativeSourceIso

/-! SOURCE ONLY, UNVERIFIED. Public SAME-original-i/P/Z supplied-frame
zero-entry consumer. ONE derived Gamma/dual/chart extraction supplies the
actual component factory, independent epsilon comparison, graph, Galois
matching and C4 full-base descent. Canonical Iso/ambient square/graph/base
alternatives are conclusions, never newly assumed certificates. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial Module TrivSqZeroExt
open AllCharacteristics.HomogeneousProjective
open scoped TensorProduct
universe u
variable {k : Type u} [Field k] [PerfectField k]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem singleSupport_originalZ_supplied_frame_epsilon_zero_entry_method_geometry
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3)
    {Z : Scheme.{u}} (i : Z ⟶ scheme (equationIdeal p hp)) [IsClosedImmersion i]
    [IsFinite (i ≫ toBase (equationIdeal p hp))] (P : closedPoints (scheme (equationIdeal p hp)))
    (hSupport : Set.range i = {P.1})
    (hP : (toBase (equationIdeal p hp)).residueDegree P.1 = 4)
    (hGeom : ProjectiveGeometricGeneralPosition (equationIdeal p hp) ((scheme (equationIdeal p hp)).fromSpecResidueField P.1)) :
    letI : IsAffine Z := isAffine_of_isAffineHom (i ≫ toBase (equationIdeal p hp))
    letI := finiteSchemeCoefficientAlgebra (i ≫ toBase (equationIdeal p hp))
    letI := finiteSchemeCoefficient_finite (i ≫ toBase (equationIdeal p hp))
    letI := AllCharacteristics.pointAlgebra (toBase (equationIdeal p hp)) P.1
    letI := AllCharacteristics.closedPoint_moduleFinite (toBase (equationIdeal p hp)) P
    (AllCharacteristics.finiteSchemeRank (i ≫ toBase (equationIdeal p hp)) = 8) →
    ∃ (j : Fin 4) (x : Fin 4 → Γ(Z, ⊤)) (hxj : x j = 1)
      (eA : Γ(Z, ⊤) ≃ₐ[k] DualNumber ((scheme (equationIdeal p hp)).residueField P.1))
      (b : Basis (Fin 4) k ((scheme (equationIdeal p hp)).residueField P.1))
      (hbj : b j = 1)
      (v : Fin 4 → (scheme (equationIdeal p hp)).residueField P.1)
      (full : Fin 4 ≃ ((scheme (equationIdeal p hp)).residueField P.1 →ₐ[k] AlgebraicClosure k)),
      let K := AlgebraicClosure k
      let Q := pullback (Spec.map (CommRingCat.ofHom (algebraMap k K))) (i ≫ toBase (equationIdeal p hp))
      let eTensor := finiteSchemeActualFieldBaseChangeIso (K := K) (i ≫ toBase (equationIdeal p hp))
      let qt := ambientNormalizedCoordinateChartPoint (F := K)
        (fun m => (1 : K) ⊗ₜ[k] x m) j (tensor_coordinate_eq_one x j hxj)
      let qOriginal := eTensor.hom ≫ qt
      let cb := QuarticNet.conjugateBasis full b (QuarticNet.conjugate_basis_span b full)
      let U := QuarticNet.conjugateTangentMatrix full b v (QuarticNet.conjugate_basis_span b full)
      (v j = 0) ∧ (v ≠ 0) ∧
      (ambientNormalizedCoordinateChartPoint (F := k) x j hxj =
        Z.isoSpec.inv ≫ i ≫ quotientProjMap (equationIdeal p hp)) ∧
      (aeval (R := k) x p = 0) ∧
      (Function.Surjective (aeval (R := k) x)) ∧
      (∀ r, eA (x r) = inl (b r) + inr (v r)) ∧
      (qOriginal ≫ ambientCoefficientMap (algebraMap k K) =
        pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k K))) (i ≫ toBase (equationIdeal p hp)) ≫
          i ≫ quotientProjMap (equationIdeal p hp)) ∧
      ∀ (supplied : Basis (Fin 4) K (Fin 4 → K))
        (hFrameSupport : Set.range (fun r =>
          (linearCoordinateChangeAmbientIso (QuarticNet.basisCoordinateMatrix supplied)
            (QuarticNet.basisCoordinateMatrix_isUnit supplied)).inv
              (actualVertexAmbientPoint (K := K) r)) =
          Set.range (fun r => ambientNormalizedCoordinateChartPoint (F := K)
            (cb r) j (by
              rw [QuarticNet.conjugateBasis_apply, hbj, map_one])
            (IsLocalRing.closedPoint K))),
      ∀ (Y : Fin 4 → Scheme.{u}) (c : ∀ r, Y r ⟶ Q) [∀ r, IsClosedImmersion (c r)],
      (Pairwise fun r s => Disjoint (Set.range (c r)) (Set.range (c s))) →
      (∀ r, Set.range (c r ≫ qOriginal) =
        {(linearCoordinateChangeAmbientIso (QuarticNet.basisCoordinateMatrix supplied)
          (QuarticNet.basisCoordinateMatrix_isUnit supplied)).inv
            (actualVertexAmbientPoint (K := K) r)}) →
      (∀ r, AllCharacteristics.finiteSchemeRank
        (c r ≫ pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k K))) (i ≫ toBase (equationIdeal p hp))) = 2) →
      ∃ (rho : Equiv.Perm (Fin 4)) (hc : ∀ r, supplied r j ≠ 0)
        (canonicalE : ∀ r, Y r ≅ Spec (.of (DualNumber K)))
        (hWholeIso : IsIso (Sigma.desc c)),
        (∀ r, (canonicalE r).hom ≫ ambientNormalizedCoordinateChartPoint (F := K)
          (QuarticNet.tangentDualPoint U (rho r)) (rho r)
          (by simp [U, QuarticNet.tangentDualPoint, QuarticNet.conjugateTangentMatrix_diagonal]) ≫
          (linearCoordinateChangeAmbientIso (QuarticNet.basisCoordinateMatrix cb)
            (QuarticNet.basisCoordinateMatrix_isUnit cb)).inv = c r ≫ qOriginal) ∧
        ∀ (V : Fin 4 → Fin 4 → K) (hV : ∀ r, V r r = 0)
          (suppliedE : ∀ r, Y r ≅ Spec (.of (DualNumber K))),
        (∀ r, (suppliedE r).hom ≫ ambientNormalizedCoordinateChartPoint (F := K)
          (QuarticNet.tangentDualPoint V r) r (by simp [QuarticNet.tangentDualPoint, hV]) ≫
          (linearCoordinateChangeAmbientIso (QuarticNet.basisCoordinateMatrix supplied)
            (QuarticNet.basisCoordinateMatrix_isUnit supplied)).inv = c r ≫ qOriginal) →
        ∃ (epsilon : Fin 4 → K) (hepsilon : ∀ r, epsilon r ≠ 0),
          V = QuarticNet.suppliedFrameTangent U rho (fun r => supplied r j) epsilon ∧
          (∀ r, (suppliedE r).hom ≫ Spec.map (CommRingCat.ofHom
            (QuarticNet.dualNumberRescaleEquiv (epsilon r) (hepsilon r)).toRingHom) =
            (canonicalE r).hom) ∧
          (actualComponentProductDualIso Y suppliedE).hom ≫
            Spec.map (CommRingCat.ofHom
              (QuarticNet.fourTangentDualRescaleEquiv epsilon hepsilon).toRingHom) =
            (actualComponentProductDualIso Y canonicalE).hom ∧
          (letI := hWholeIso
            (((asIso (Sigma.desc c)).symm ≪≫ actualComponentProductDualIso Y suppliedE).hom) ≫
              Spec.map (CommRingCat.ofHom
                (QuarticNet.fourTangentDualRescaleEquiv epsilon hepsilon).toRingHom) =
              ((asIso (Sigma.desc c)).symm ≪≫ actualComponentProductDualIso Y canonicalE).hom) ∧
          ((∀ r s, V r s = -V s r) → (∃ r s, r ≠ s ∧ V r s = 0) →
            ∃ l : Fin 4 → K, (∀ r, l r ≠ 0) ∧
              (∀ r s, QuarticNet.rescaleTangentDirections l U r s =
                -QuarticNet.rescaleTangentDirections l U s r) ∧
              (∃ r s, r ≠ s ∧ U r s = 0) ∧
              OriginalEmbeddedZeroEntryMethodGeometry p hp
                (i ≫ quotientProjMap (equationIdeal p hp))) := by
  let I := equationIdeal p hp
  classical
  letI : IsAffine Z := isAffine_of_isAffineHom (i ≫ toBase I)
  letI := finiteSchemeCoefficientAlgebra (i ≫ toBase I)
  letI := finiteSchemeCoefficient_finite (i ≫ toBase I)
  letI := AllCharacteristics.pointAlgebra (toBase I) P.1
  letI := AllCharacteristics.closedPoint_moduleFinite (toBase I) P
  intro hZ
  obtain ⟨j, g, x, eA, b, v, full, hxj, hgen, hbase, hbj, hvj, hv,
    hxg, hpoint, hcoords⟩ := singleSupport_actual_original_order_dual_chart_data
      I i P hSupport hP hGeom hZ
  let K := AlgebraicClosure k
  let eTensor := finiteSchemeActualFieldBaseChangeIso (K := K) (i ≫ toBase I)
  let qt := ambientNormalizedCoordinateChartPoint (F := K)
    (fun m => (1 : K) ⊗ₜ[k] x m) j (tensor_coordinate_eq_one x j hxj)
  have hxActual : x = fun m => g (chartCoordinate I j m) := funext hxg
  have hOriginal : ambientNormalizedCoordinateChartPoint (F := k) x j hxj =
      Z.isoSpec.inv ≫ i ≫ quotientProjMap I := by
    rw [hxActual, ambientNormalizedCoordinateChartPoint_eq_original_chart I j g hbase]
    rw [← Category.assoc, hpoint, Category.assoc]
  have hOriginalSquare : (eTensor.hom ≫ qt) ≫ ambientCoefficientMap (algebraMap k K) =
      pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k K))) (i ≫ toBase I) ≫
        i ≫ quotientProjMap I := by
    let inc := Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : Γ(Z, ⊤) →ₐ[k] K ⊗[k] Γ(Z, ⊤)).toRingHom)
    calc
      _ = eTensor.hom ≫ inc ≫ ambientNormalizedCoordinateChartPoint (F := k) x j hxj := by
        rw [Category.assoc]
        exact congrArg (fun f => eTensor.hom ≫ f)
          (ambientNormalizedCoordinateChartPoint_tensor_coefficients (K := K) x j hxj)
      _ = (eTensor.hom ≫ inc ≫ Z.isoSpec.inv) ≫ i ≫ quotientProjMap I := by
        rw [hOriginal]
        simp only [Category.assoc]
      _ = _ := by rw [finiteSchemeActualFieldBaseChangeIso_hom_toOriginal]
  have hFx : aeval (R := k) x p = 0 := by
    have h := congrArg g (eval₂_chartCoordinate_eq_zero_of_mem I j p
      (show p ∈ I.toIdeal from Ideal.subset_span (Set.mem_singleton _)))
    have hcoordsEq : (fun r => g (chartCoordinate I j r)) = x :=
      funext (fun r => (hxg r).symm)
    rw [hom_eval₂, hbase, hcoordsEq, map_zero] at h
    exact h
  refine ⟨j, x, hxj, eA, b, hbj, v, full, hvj, hv, hOriginal, hFx,
    hgen, hcoords, hOriginalSquare, ?_⟩
  intro supplied hFrameSupport Y c hClosed hDisjoint hComponentSupport hComponents
  letI : ∀ r, IsClosedImmersion (c r) := hClosed
  let cTensor := fun r => c r ≫ eTensor.hom
  letI : ∀ r, IsClosedImmersion (cTensor r) := fun r => by
    dsimp only [cTensor]
    infer_instance
  have hTensorSupport : ∀ r, Set.range (cTensor r ≫ qt) =
      {(linearCoordinateChangeAmbientIso (QuarticNet.basisCoordinateMatrix supplied)
        (QuarticNet.basisCoordinateMatrix_isUnit supplied)).inv
          (actualVertexAmbientPoint (K := K) r)} := by
    intro r
    simpa only [cTensor, Category.assoc] using hComponentSupport r
  have hTensorRank : ∀ r, AllCharacteristics.finiteSchemeRank
      (cTensor r ≫ actualTensorOriginalToBase (k := k) (K := K) (A := Γ(Z, ⊤))) = 2 := by
    intro r
    have hMap : cTensor r ≫ actualTensorOriginalToBase =
        c r ≫ pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k K))) (i ≫ toBase I) := by
      dsimp only [cTensor, actualTensorOriginalToBase]
      rw [Category.assoc, finiteSchemeActualFieldBaseChangeIso_hom_toField]
    rw [hMap]
    exact hComponents r
  obtain ⟨rho, hc, canonicalE, hCanonical, hComparison⟩ :=
    actualTensor_original_supplied_component_frame_comparison eA x hgen b v hcoords full j hxj
      supplied hFrameSupport Y cTensor hTensorSupport hTensorRank
  let tQ := pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k K))) (i ≫ toBase I)
  have hOriginalBase : (eTensor.hom ≫ qt) ≫ ambientToBase = tQ := by
    rw [Category.assoc, ambientNormalizedCoordinateChartPoint_toBase]
    exact finiteSchemeActualFieldBaseChangeIso_hom_toField (K := K) (i ≫ toBase I)
  have hCanonicalBase : ∀ r, (canonicalE r).hom ≫ actualDualToBase = c r ≫ tQ := by
    intro r
    let qp := QuarticNet.actualTensorProductDualOriginalAmbient eA x b full j hxj
    have hFactor : (canonicalE r).hom ≫ actualProductDualFactor (rho r) ≫ qp =
        c r ≫ eTensor.hom ≫ qt := by
      rw [QuarticNet.actualTensorProductDual_factor_original_ambient_square eA x b v hcoords full j hxj]
      simpa only [cTensor, Category.assoc] using hCanonical r
    calc
      _ = (canonicalE r).hom ≫ actualProductDualFactor (rho r) ≫ qp ≫ ambientToBase := by
        rw [QuarticNet.actualTensorProductDualOriginalAmbient_toBase,
          actualProductDualFactor_toBase]
      _ = c r ≫ eTensor.hom ≫ qt ≫ ambientToBase := by
        simpa only [Category.assoc] using congrArg (fun f => f ≫ ambientToBase) hFactor
      _ = _ := by
        simpa only [Category.assoc] using congrArg (fun f => c r ≫ f) hOriginalBase
  have hWholeRank : AllCharacteristics.finiteSchemeRank tQ = 8 := by
    rw [AllCharacteristics.finiteSchemeRank_eq_finrank,
      Scheme.Hom.finrank_pullback_fst]
    have hFieldPoint : Spec.map (CommRingCat.ofHom (algebraMap k K))
        (IsLocalRing.closedPoint K) = IsLocalRing.closedPoint k := Subsingleton.elim _ _
    rw [hFieldPoint]
    exact (AllCharacteristics.finiteSchemeRank_eq_finrank (i ≫ toBase I)).symm.trans hZ
  have hWholeIso : IsIso (Sigma.desc c) := actual_closed_components_canonicalCoproduct_isIso
    tQ Y c hDisjoint canonicalE hCanonicalBase hWholeRank
  refine ⟨rho, hc, canonicalE, hWholeIso, ?_, ?_⟩
  · intro r
    simpa only [cTensor, Category.assoc] using hCanonical r
  · intro V hV suppliedE hSupplied
    have hSuppliedTensor : ∀ r, (suppliedE r).hom ≫ ambientNormalizedCoordinateChartPoint (F := K)
        (QuarticNet.tangentDualPoint V r) r (by simp [QuarticNet.tangentDualPoint, hV]) ≫
        (linearCoordinateChangeAmbientIso (QuarticNet.basisCoordinateMatrix supplied)
          (QuarticNet.basisCoordinateMatrix_isUnit supplied)).inv = cTensor r ≫ qt := by
      intro r
      simpa only [cTensor, Category.assoc] using hSupplied r
    obtain ⟨epsilon, hepsilon, hEq, hSquares, hPi, hSkew⟩ :=
      hComparison V hV suppliedE hSuppliedTensor
    refine ⟨epsilon, hepsilon, hEq, hSquares, hPi, ?_, ?_⟩
    · letI := hWholeIso
      exact actual_component_epsilon_original_whole_source_square Y (asIso (Sigma.desc c))
        canonicalE suppliedE epsilon hepsilon hSquares
    · intro hSuppliedSkew hSuppliedMissing
      obtain ⟨l, hl, hCanonicalSkew, hCanonicalMissing⟩ :=
        hSkew hSuppliedSkew hSuppliedMissing
      have hMissingScaled : ∃ r s, r ≠ s ∧
          QuarticNet.rescaleTangentDirections l U r s = 0 := by
        obtain ⟨r, s, hrs, hzero⟩ := hCanonicalMissing
        exact ⟨r, s, hrs, by simp only [QuarticNet.rescaleTangentDirections, hzero, mul_zero]⟩
      have hGeometry := QuarticNet.originalDualCoordinates_any_chart_zero_entry_method_geometry
        eA x j hxj b v hcoords hbj hvj hv full p hp hFx
        l hl hCanonicalSkew hMissingScaled
      have hOriginalGeometry : OriginalEmbeddedZeroEntryMethodGeometry p hp
          (i ≫ quotientProjMap I) := by
        rcases hGeometry with hMatching | hFinite
        · exact Or.inl hMatching
        · have hBase : intrinsicFullQuadraticBaseIdeal
              (ambientNormalizedCoordinateChartPoint x j hxj) =
              intrinsicFullQuadraticBaseIdeal (i ≫ quotientProjMap I) := by
            rw [hOriginal]
            exact QuarticNet.intrinsicFullQuadraticBaseIdeal_comp_iso Z.isoSpec.symm
              (i ≫ quotientProjMap I)
          rw [hBase] at hFinite
          exact Or.inr hFinite
      exact ⟨l, hl, hCanonicalSkew, hCanonicalMissing, hOriginalGeometry⟩

end PfaffianDescent
