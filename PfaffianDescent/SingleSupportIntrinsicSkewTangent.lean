import PfaffianDescent.SingleSupportIntrinsicQuadraticRestriction
import PfaffianDescent.PerfectFieldQuarticPointChartBasis
import PfaffianDescent.QuarticJetNet
import PfaffianDescent.QuarticConjugateSpan
import PfaffianDescent.ActualDualAlgebraConjugateTangentCoordinates
import PfaffianDescent.QuarticTangentRescalingExactKernel

/-! Literal arbitrary-supplied-Z skew normalization. Every algebra, chart,
residue coordinate, ground tangent and Galois action is obtained from the
GIVEN closed length-eight scheme, not from a separate constructed jet. -/

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial Module TrivSqZeroExt
open AllCharacteristics.HomogeneousProjective
universe u
variable {k : Type u} [Field k] [PerfectField k]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

/-- The literal supplied-Z hypotheses imply skew tangent representatives.
The conclusion retains the actual Gamma(Z) dual equivalence and original
ambient chart, so the skew matrix describes that same subscheme. -/
theorem singleSupport_intrinsic_quadratics_actual_skew_tangents
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
    (AllCharacteristics.finiteSchemeRank (i ≫ toBase I) = 8) →
    ∃ j : Fin 4, ∃ (g : ChartRing I j →+* Γ(Z, ⊤))
      (x : Fin 4 → Γ(Z, ⊤))
      (e : Γ(Z, ⊤) ≃ₐ[k] DualNumber ((scheme I).residueField P.1))
      (b : Basis (Fin 4) k ((scheme I).residueField P.1))
      (v : Fin 4 → (scheme I).residueField P.1) (pi : Equiv.Perm (Fin 4))
      (full : Fin 4 ≃ ((scheme I).residueField P.1 →ₐ[k] AlgebraicClosure k)),
      x j = 1 ∧ Function.Surjective (aeval (R := k) x) ∧
      g.comp (chartBaseMap I j) = algebraMap k Γ(Z, ⊤) ∧
      b 0 = 1 ∧ v 0 = 0 ∧ v ≠ 0 ∧ pi 0 = j ∧
      (∀ r, x r = g (chartCoordinate I j r)) ∧
      Spec.map (CommRingCat.ofHom g) ≫ chartι I j = Z.isoSpec.inv ≫ i ∧
      (∀ r, e (x (pi r)) = TrivSqZeroExt.inl (b r) + TrivSqZeroExt.inr (v r)) ∧
      ∃ hspan : Submodule.span (AlgebraicClosure k)
        (Set.range (fun sigma : (scheme I).residueField P.1 →ₐ[k] AlgebraicClosure k =>
          fun r => sigma (b r))) = ⊤,
        (∀ row m, ∑ r, algebraMap (AlgebraicClosure k) (DualNumber (AlgebraicClosure k))
            (QuarticNet.basisCoordinateMatrix (QuarticNet.conjugateBasis full b hspan) m r) *
          QuarticNet.tangentDualPoint (QuarticNet.conjugateTangentMatrix full b v hspan) row r =
          (1 + TrivSqZeroExt.inr
            (-QuarticNet.conjugateTangentRow full b v hspan row row) :
              DualNumber (AlgebraicClosure k)) *
          QuarticNet.dualNumberEmbedding (full row) (e (x (pi m)))) ∧
        (∀ (F : MvPolynomial (Fin 4) k) (n : ℕ), F.IsHomogeneous n → ∀ row,
          aeval (QuarticNet.tangentDualPoint (QuarticNet.conjugateTangentMatrix full b v hspan) row)
            (linearSubstitution
              (QuarticNet.basisCoordinateMatrix (QuarticNet.conjugateBasis full b hspan))
              (map (algebraMap k (AlgebraicClosure k)) F)) = 0 ↔
            aeval (fun r => x (pi r)) F = 0) ∧
        (∀ r, ∃ s, QuarticNet.conjugateTangentMatrix full b v hspan r s ≠ 0) ∧
        ∃ l : Fin 4 → AlgebraicClosure k, (∀ r, l r ≠ 0) ∧
        (∀ r s, l r * QuarticNet.conjugateTangentMatrix full b v hspan r s =
            -(l s * QuarticNet.conjugateTangentMatrix full b v hspan s r)) ∧
        (∀ (F : MvPolynomial (Fin 4) k) (n : ℕ), F.IsHomogeneous n → ∀ row,
          aeval (QuarticNet.tangentDualPoint
            (QuarticNet.rescaleTangentDirections l
              (QuarticNet.conjugateTangentMatrix full b v hspan)) row)
            (linearSubstitution
              (QuarticNet.basisCoordinateMatrix (QuarticNet.conjugateBasis full b hspan))
              (map (algebraMap k (AlgebraicClosure k)) F)) = 0 ↔
            aeval (fun r => x (pi r)) F = 0) := by
  classical
  letI : IsAffine Z := isAffine_of_isAffineHom (i ≫ toBase I)
  letI := finiteSchemeCoefficientAlgebra (i ≫ toBase I)
  letI := AllCharacteristics.pointAlgebra (toBase I) P.1
  intro hZ
  letI := finiteSchemeCoefficient_finite (i ≫ toBase I)
  letI := AllCharacteristics.closedPoint_moduleFinite (toBase I) P
  letI : IsLocalRing Γ(Z, ⊤) := singleSupport_globalSections_isLocalRing i P.1 hSupport
  let L := (scheme I).residueField P.1
  let rho := singleClosedSupportResidueAlgHom i (toBase I) P hSupport
  have hrho : Function.Surjective rho :=
    singleClosedSupportResidueAlgHom_surjective i (toBase I) P hSupport
  have hL : finrank k L = 4 :=
    (AllCharacteristics.closedPoint_finrank_eq_residueDegree (toBase I) P).trans hP
  have hA : finrank k Γ(Z, ⊤) = 8 :=
    (finiteSchemeCoefficient_finrank (i ≫ toBase I)).trans hZ
  obtain ⟨e0, he0⟩ := lengthEightLocal_quarticResidue_dual_equiv_with_residue rho hrho hL hA
  let e := e0.symm
  obtain ⟨j, g, x, hxj, hxs, hgb, hxg, hW, hpoint⟩ :=
    singleSupport_intrinsic_quadratics_actual_restriction I i P hSupport
  let gL : ChartRing I j →+* L := rho.toRingHom.comp g
  let qP := (scheme I).fromSpecResidueField P.1
  let qZ := singleClosedSupportResidueLift i P hSupport
  have hqBase : qZ ≫ (i ≫ toBase I) =
      Spec.map (CommRingCat.ofHom (algebraMap k L)) := by
    rw [← Category.assoc, singleClosedSupportResidueLift_comp,
      AllCharacteristics.pointAlgebra_spec]
  have hrhoSpec : Spec.map (CommRingCat.ofHom rho.toRingHom) = qZ ≫ Z.isoSpec.hom :=
    finiteSchemePointAlgHom_spec (i ≫ toBase I) qZ (algebraMap k L) hqBase
  have hgLBase : gL.comp (chartBaseMap I j) = algebraMap k L := by
    ext c
    change rho (g (chartBaseMap I j c)) = algebraMap k L c
    rw [show g (chartBaseMap I j c) = algebraMap k Γ(Z, ⊤) c from
      DFunLike.congr_fun hgb c]
    exact rho.commutes c
  have hgLPoint : Spec.map (CommRingCat.ofHom gL) ≫ chartι I j = qP := by
    change Spec.map (CommRingCat.ofHom g ≫ CommRingCat.ofHom rho.toRingHom) ≫ chartι I j = _
    rw [Spec.map_comp, Category.assoc, hpoint, hrhoSpec]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    exact singleClosedSupportResidueLift_comp i P hSupport
  have hLI : LinearIndependent k (fun r => rho (x r)) := by
    have h := perfectField_quartic_fieldPoint_chart_coordinates_independent (K := k) (L := L) I qP
      (AllCharacteristics.pointAlgebra_spec (toBase I) P.1).symm hL hGeom j gL hgLBase hgLPoint
    change LinearIndependent k (fun r => rho (g (chartCoordinate I j r))) at h
    simpa only [← hxg] using h
  have hcard : Fintype.card (Fin 4) = finrank k L := by rw [Fintype.card_fin, hL]
  let b : Basis (Fin 4) k L := basisOfLinearIndependentOfCardEqFinrank hLI hcard
  have hb (r : Fin 4) : b r = rho (x r) :=
    congrFun (coe_basisOfLinearIndependentOfCardEqFinrank hLI hcard) r
  have hfst (r : Fin 4) : (e (x r)).fst = rho (x r) := by
    have h := he0 (e (x r))
    simpa [e] using h.symm
  let v0 : Fin 4 → L := fun r => (e (x r)).snd
  have hv0 : v0 ≠ 0 := by
    intro hvzero
    have hsnd (r : Fin 4) : (e (x r)).snd = 0 := congrFun hvzero r
    have hconst : e.toAlgHom.comp (aeval x) =
        (TrivSqZeroExt.inlAlgHom k L L).comp (aeval (fun r => (e (x r)).fst)) := by
      apply MvPolynomial.algHom_ext
      intro r
      change e (aeval x (X r)) =
        TrivSqZeroExt.inl (aeval (fun s => (e (x s)).fst) (X r))
      rw [aeval_X, aeval_X]
      apply TrivSqZeroExt.ext
      · rfl
      · exact hsnd r
    obtain ⟨q, hq⟩ := (e.surjective.comp hxs) (TrivSqZeroExt.inr (1 : L))
    change (e.toAlgHom.comp (aeval x)) q = _ at hq
    rw [hconst] at hq
    change TrivSqZeroExt.inl (aeval (fun r => (e (x r)).fst) q) =
      TrivSqZeroExt.inr (1 : L) at hq
    have hcontra := congrArg TrivSqZeroExt.snd hq
    change (0 : L) = 1 at hcontra
    exact zero_ne_one hcontra
  let pi : Equiv.Perm (Fin 4) := Equiv.swap 0 j
  let b' := b.reindex pi
  let v : Fin 4 → L := fun r => v0 (pi r)
  have hb'0 : b' 0 = 1 := by simp [b', Basis.reindex_apply, pi, hb, hxj]
  have hv'0 : v 0 = 0 := by simp [v, pi, v0, hxj]
  have hv : v ≠ 0 := by
    intro hz
    apply hv0
    funext r
    have h := congrFun hz (pi r)
    simpa [v, pi] using h
  have hcoord (r : Fin 4) : e (x (pi r)) =
      TrivSqZeroExt.inl (b' r) + TrivSqZeroExt.inr (v r) := by
    apply TrivSqZeroExt.ext
    · simpa [b', Basis.reindex_apply, pi, hb] using hfst (pi r)
    · simp [v, v0]
  let W := intrinsicFullQuadraticSystem (i ≫ quotientProjMap I)
  obtain ⟨Q, hQI⟩ := exists_linearIndependent_of_le_finrank (R := k) (M := W) hdim
  let QR : Fin 3 → MvPolynomial (Fin 4) k := fun r => (Q r).val
  have hQRI : LinearIndependent k QR := hQI.map_injOn W.subtype Subtype.val_injective.injOn
  let changeVariables := MvPolynomial.renameEquiv k pi
  let Q' : Fin 3 → MvPolynomial (Fin 4) k := fun r => changeVariables (QR r)
  have hQ'I : LinearIndependent k Q' :=
    hQRI.map' changeVariables.toLinearEquiv.toLinearMap
      (LinearMap.ker_eq_bot.mpr changeVariables.injective)
  have hQhom (r : Fin 3) : (Q' r).IsHomogeneous 2 := by
    change (rename pi (QR r)).IsHomogeneous 2
    exact (Q r).property.1.rename_isHomogeneous
  have hQvan (r : Fin 3) : aeval
      (fun s => TrivSqZeroExt.inl (b' s) + TrivSqZeroExt.inr (v s)) (Q' r) = 0 := by
    have hbasezero : aeval x (QR r) = 0 :=
      ((mem_homogeneousVanishingPolynomialSubmodule_iff x 2 (QR r)).mp
        (hW (Q r).property)).2
    have hdualzero : aeval (fun s => e (x s)) (QR r) = 0 := by
      calc
        aeval (fun s => e (x s)) (QR r) = e (aeval x (QR r)) :=
          (comp_aeval_apply x e.toAlgHom (QR r)).symm
        _ = 0 := by rw [hbasezero]; exact e.map_zero
    change aeval (fun s => TrivSqZeroExt.inl (b' s) + TrivSqZeroExt.inr (v s))
      (rename pi (QR r)) = 0
    rw [aeval_rename]
    have hcoordinates : (fun s => TrivSqZeroExt.inl (b' s) + TrivSqZeroExt.inr (v s)) ∘ pi =
        fun s => e (x s) := by
      funext s
      have h := hcoord (pi s)
      simpa [pi] using h.symm
    rw [hcoordinates]
    exact hdualzero
  let full : Fin 4 ≃ (L →ₐ[k] AlgebraicClosure k) :=
    (Fintype.equivFinOfCardEq ((AlgHom.card k L (AlgebraicClosure k)).trans hL)).symm
  have hspan : Submodule.span (AlgebraicClosure k)
      (Set.range (fun sigma : L →ₐ[k] AlgebraicClosure k => fun r => sigma (b' r))) = ⊤ :=
    QuarticNet.conjugate_basis_span b' full
  obtain ⟨l, hl, hskew⟩ := QuarticNet.skew_normalization_of_transitive_covariance
    (QuarticNet.conjugateTangentMatrix full b' v hspan)
    (QuarticNet.conjugateTangentMatrix_diagonal full b' v hspan)
    (QuarticNet.independent_conjugate_quadrics full b' v hspan Q' hQ'I hQhom hQvan)
    (QuarticNet.conjugateTangentMatrix_transitive_covariance full b' v hspan)
  have hrow : ∀ r, ∃ s, QuarticNet.conjugateTangentMatrix full b' v hspan r s ≠ 0 :=
    QuarticNet.conjugateTangentMatrix_row_nonzero full b' v hspan hb'0 hv'0 hv
  refine ⟨j, g, x, e, b', v, pi, full, hxj, hxs, hgb, hb'0, hv'0, hv, by simp [pi],
    hxg, hpoint, hcoord, hspan,
    actualDual_conjugate_tangent_coordinates e (fun r => x (pi r)) b' v hcoord full hspan,
    fun F n hF row => actualDual_conjugate_tangent_equation_iff
      e (fun r => x (pi r)) b' v hcoord full hspan F n hF row,
    hrow, l, hl, hskew, ?_⟩
  intro F n hF row
  rw [QuarticNet.rescaleTangentDirections_equation_iff _ l hl]
  exact actualDual_conjugate_tangent_equation_iff
    e (fun r => x (pi r)) b' v hcoord full hspan F n hF row

end PfaffianDescent
