import PfaffianDescent.SingleSupportOriginalSuppliedFrameZeroEntryGeometry
import PfaffianDescent.ActualTensorOriginalSuppliedMatchingLinePair

/-! SOURCE ONLY / UNVERIFIED. SAME original Z/i/P and given supplied frame.
All original affine/dual/chart data are extracted internally. The literal
supplied component/rank/support/ambient-square data describe the manuscript
presentation; n=1 is its case condition. The ONE quadratic field, exchange,
skewness and EXACT supplied matching line ideals are conclusions. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial Module TrivSqZeroExt
open AllCharacteristics.HomogeneousProjective
open scoped TensorProduct
universe u
variable {k : Type u} [Field k] [PerfectField k]
attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false in
theorem singleSupport_originalZ_supplied_matching_line_ideals
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
      ∀ (V : Fin 4 → Fin 4 → K) (hV : ∀ r, V r r = 0)
        (suppliedE : ∀ r, Y r ≅ Spec (.of (DualNumber K))),
        (∀ r, (suppliedE r).hom ≫ ambientNormalizedCoordinateChartPoint (F := K)
          (QuarticNet.tangentDualPoint V r) r (by simp [QuarticNet.tangentDualPoint, hV]) ≫
          (linearCoordinateChangeAmbientIso (QuarticNet.basisCoordinateMatrix supplied)
            (QuarticNet.basisCoordinateMatrix_isUnit supplied)).inv = c r ≫ qOriginal) →
        (∀ r s, V r s = -V s r) → (∀ r, ∃! s, V r s ≠ 0) →
        OriginalMatchingQuadraticLinePairOnSuppliedFrame p hp supplied V := by
  classical
  let I := equationIdeal p hp
  letI : IsAffine Z := isAffine_of_isAffineHom (i ≫ toBase I)
  letI := finiteSchemeCoefficientAlgebra (i ≫ toBase I)
  letI := finiteSchemeCoefficient_finite (i ≫ toBase I)
  letI := AllCharacteristics.pointAlgebra (toBase I) P.1
  letI := AllCharacteristics.closedPoint_moduleFinite (toBase I) P
  intro hZ
  obtain ⟨j, x, hxj, eA, b, hbj, v, full, hvj, hv, hOriginal,
    hFx, hgen, hcoords, hOriginalSquare, hFactory⟩ :=
    singleSupport_originalZ_supplied_frame_epsilon_zero_entry_geometry
      p hp i P hSupport hP hGeom hZ
  refine ⟨j, x, hxj, eA, b, hbj, v, full, hvj, hv, hOriginal,
    hFx, hgen, hcoords, hOriginalSquare, ?_⟩
  intro supplied hFrameSupport Y c hClosed hDisjoint hComponentSupport hRank
    V hV suppliedE hSupplied hSkew hOne
  let K := AlgebraicClosure k
  let eTensor := finiteSchemeActualFieldBaseChangeIso (K := K) (i ≫ toBase I)
  let qt := ambientNormalizedCoordinateChartPoint (F := K)
    (fun m => (1 : K) ⊗ₜ[k] x m) j (tensor_coordinate_eq_one x j hxj)
  let cTensor := fun r => c r ≫ eTensor.hom
  letI : ∀ r, IsClosedImmersion (c r) := hClosed
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
    rw [AllCharacteristics.finiteSchemeRank_eq_finrank, hMap,
      ← AllCharacteristics.finiteSchemeRank_eq_finrank]
    exact hRank r
  have hSuppliedTensor : ∀ r, (suppliedE r).hom ≫
      ambientNormalizedCoordinateChartPoint (F := K) (QuarticNet.tangentDualPoint V r)
        r (by simp [QuarticNet.tangentDualPoint, hV]) ≫
      (linearCoordinateChangeAmbientIso (QuarticNet.basisCoordinateMatrix supplied)
        (QuarticNet.basisCoordinateMatrix_isUnit supplied)).inv = cTensor r ≫ qt := by
    intro r
    simpa only [cTensor, Category.assoc] using hSupplied r
  exact actualTensor_original_supplied_matching_quadratic_line_pair
    eA x hgen b v hcoords full j hxj p hp hFx supplied hFrameSupport Y cTensor
    hTensorSupport hTensorRank V hV suppliedE hSuppliedTensor hSkew hOne

end PfaffianDescent
