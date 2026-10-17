import PfaffianDescent.FourTangentDualComponentAmbientSquare
import PfaffianDescent.FourTangentIntrinsicWeightedRelations
import PfaffianDescent.IntrinsicFullBaseAlternativeSourceIso
import PfaffianDescent.ActualLengthTwoDualPresentationRescaling
import AllCharacteristics.FiniteSigmaSpec

/-! SOURCE-ONLY UNVERIFIED draft. The matrix below belongs to the SUPPLIED
epsilon presentation, not an independently chosen canonical presentation.
The presentation squares encode [e_r + epsilon v_r] as scheme morphisms.
Zero entries and individual zero relation weights are allowed in the IFF.
Only the base-locus theorem assumes the literal nonzero off-diagonal entries.
-/

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial Module
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Assemble the four SUPPLIED epsilon presentations, preserving their
given component inclusions. No new tangent directions are chosen. -/
theorem fourCoordinateVertex_supplied_presentation_square
    (Z : Fin 4 → Scheme.{u})
    (i : ∀ r, Z r ⟶ scheme (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)))
    (U : Fin 4 → Fin 4 → K) (hdiag : ∀ r, U r r = 0)
    (eRow : ∀ r, Z r ≅ Spec (.of (DualNumber K)))
    (hpoint : ∀ r, (eRow r).hom ≫
      ambientNormalizedCoordinateChartPoint (F := K)
        (fun s => TrivSqZeroExt.inl (coordinateVertexCoordinates (K := K) r s) +
          TrivSqZeroExt.inr (U r s)) r
        (by simp [coordinateVertexCoordinates, hdiag]) = i r ≫ quotientProjMap ⊥) :
    ∃ e : (∐ Z) ≅ Spec (.of (QuarticNet.FourTangentDualAlgebra K)),
      e.hom ≫ (QuarticNet.fourTangentDualToProjective U ≫ quotientProjMap ⊥) =
        Sigma.desc (fun r => i r ≫ quotientProjMap ⊥) := by
  letI : IsIso (sigmaSpec (fun _ : Fin 4 => CommRingCat.of (DualNumber K))) :=
    AllCharacteristics.isIso_sigmaSpec_const_finite (Fin 4) (DualNumber K)
  let e := Sigma.mapIso eRow ≪≫
    asIso (sigmaSpec (fun _ : Fin 4 => CommRingCat.of (DualNumber K)))
  refine ⟨e, ?_⟩
  apply Sigma.hom_ext
  intro r
  calc
    Sigma.ι Z r ≫ e.hom ≫
        (QuarticNet.fourTangentDualToProjective U ≫ quotientProjMap ⊥) =
      (eRow r).hom ≫ Spec.map (CommRingCat.ofHom
        (Pi.evalRingHom (fun _ : Fin 4 => DualNumber K) r)) ≫
          QuarticNet.fourTangentDualToProjective U ≫ quotientProjMap ⊥ := by
      simp only [e, Iso.trans_hom, asIso_hom, Category.assoc]
      rw [← Category.assoc (Sigma.ι Z r), Sigma.ι_mapIso_hom]
      simp only [Category.assoc]
      rw [← Category.assoc
        (Sigma.ι (fun _ : Fin 4 => Spec (.of (DualNumber K))) r), ι_sigmaSpec]
    _ = (eRow r).hom ≫ ambientNormalizedCoordinateChartPoint (F := K)
        (fun s => TrivSqZeroExt.inl (coordinateVertexCoordinates (K := K) r s) +
          TrivSqZeroExt.inr (U r s)) r
        (by simp [coordinateVertexCoordinates, hdiag]) := by
      rw [QuarticNet.fourTangentDual_component_actual_ambient_square U hdiag r]
    _ = i r ≫ quotientProjMap ⊥ := hpoint r
    _ = Sigma.ι Z r ≫ Sigma.desc (fun r => i r ≫ quotientProjMap ⊥) := by
      rw [Sigma.ι_desc]

/-- Lemma `lem:uij-skew-symmetric` in the supplied representation, with arbitrary zero entries
and arbitrary individual zero weights. The intrinsic space belongs to q. -/
theorem suppliedFourTangent_intrinsic_weighted_iff
    {Z : Scheme.{u}}
    (q : Z ⟶ Proj (homogeneousSubmodule (Fin 4) K))
    (U : Fin 4 → Fin 4 → K) (hdiag : ∀ r, U r r = 0)
    (e : Z ≅ Spec (.of (QuarticNet.FourTangentDualAlgebra K)))
    (hpoint : e.hom ≫
      (QuarticNet.fourTangentDualToProjective U ≫ quotientProjMap ⊥) = q) :
    3 ≤ finrank K (intrinsicFullQuadraticSystem q) ↔
      ∃ w : Fin 4 → K, w ≠ 0 ∧
        ∀ r s, r < s → w r * U r s = -(w s * U s r) := by
  rw [← hpoint, intrinsicFullQuadraticSystem_comp_isIso]
  exact QuarticNet.fourTangent_intrinsicQuadraticSystem_finrank_ge_three_iff U hdiag

/-- Literal base-locus lemma for the matrix of the SUPPLIED presentation.
No condition on a separately chosen canonical tangent matrix appears. -/
theorem suppliedFourTangent_intrinsic_fullBase_alternative
    [IsAlgClosed K] {Z : Scheme.{u}}
    (q : Z ⟶ Proj (homogeneousSubmodule (Fin 4) K))
    (U : Fin 4 → Fin 4 → K) (hdiag : ∀ r, U r r = 0)
    (e : Z ≅ Spec (.of (QuarticNet.FourTangentDualAlgebra K)))
    (hpoint : e.hom ≫
      (QuarticNet.fourTangentDualToProjective U ≫ quotientProjMap ⊥) = q)
    (hskew : ∀ r s, U r s = -U s r)
    (hnonzero : ∀ r s, r ≠ s → U r s ≠ 0) :
    QuarticNet.IntrinsicFullBaseEmbeddedAlternative q := by
  have hU : U = QuarticNet.skewTangentDirections (U 0 1) (U 0 2) (U 0 3)
      (U 1 2) (U 1 3) (U 2 3) :=
    QuarticNet.skew_matrix_eq_parameters U hdiag hskew
  let qU := QuarticNet.fourTangentDualToProjective U ≫ quotientProjMap
    (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
  have hAlternative : QuarticNet.IntrinsicFullBaseEmbeddedAlternative qU := by
    have h := QuarticNet.fourTangent_intrinsicFullQuadraticBase_embedded_alternative
      (U 0 1) (U 0 2) (U 0 3) (U 1 2) (U 1 3) (U 2 3)
      (hnonzero 0 1 (by decide)) (hnonzero 0 2 (by decide))
      (hnonzero 0 3 (by decide)) (hnonzero 1 2 (by decide))
      (hnonzero 1 3 (by decide)) (hnonzero 2 3 (by decide))
    change QuarticNet.IntrinsicFullBaseEmbeddedAlternative
      (QuarticNet.fourTangentDualToProjective
        (QuarticNet.skewTangentDirections (U 0 1) (U 0 2) (U 0 3)
          (U 1 2) (U 1 3) (U 2 3)) ≫ quotientProjMap ⊥) at h
    simpa only [← hU] using h
  have h := QuarticNet.intrinsicFullBase_embedded_alternative_precomp_iso e qU hAlternative
  change QuarticNet.IntrinsicFullBaseEmbeddedAlternative
    (e.hom ≫ (QuarticNet.fourTangentDualToProjective U ≫ quotientProjMap ⊥)) at h
  simpa only [hpoint] using h

/-- A genuine epsilon-generator change on the supplied source. The exact
ambient embedding and therefore its full intrinsic ideal are preserved.
The changed matrix need not be skew, even when U is skew. -/
theorem suppliedFourTangent_rescale_same_embedding
    {Z : Scheme.{u}}
    (q : Z ⟶ Proj (homogeneousSubmodule (Fin 4) K))
    (U : Fin 4 → Fin 4 → K)
    (e : Z ≅ Spec (.of (QuarticNet.FourTangentDualAlgebra K)))
    (hpoint : e.hom ≫
      (QuarticNet.fourTangentDualToProjective U ≫ quotientProjMap ⊥) = q)
    (l : Fin 4 → K) (hl : ∀ r, l r ≠ 0) :
    ∃ eNew : Z ≅ Spec (.of (QuarticNet.FourTangentDualAlgebra K)),
      eNew.hom ≫
        (QuarticNet.fourTangentDualToProjective
          (QuarticNet.rescaleTangentDirections l U) ≫ quotientProjMap ⊥) = q ∧
      intrinsicFullQuadraticBaseIdeal
        (QuarticNet.fourTangentDualToProjective
          (QuarticNet.rescaleTangentDirections l U) ≫ quotientProjMap ⊥) =
        intrinsicFullQuadraticBaseIdeal q := by
  let delta := QuarticNet.fourTangentDualRescaleEquiv l hl
  let eDelta := Scheme.Spec.mapIso delta.toRingEquiv.toCommRingCatIso.symm.op
  let eNew := e ≪≫ eDelta
  have hCancel : eDelta.hom ≫ Spec.map (CommRingCat.ofHom delta.toRingHom) = 𝟙 _ := by
    change eDelta.hom ≫ eDelta.inv = 𝟙 _
    exact eDelta.hom_inv_id
  have hNew : eNew.hom ≫
      (QuarticNet.fourTangentDualToProjective
        (QuarticNet.rescaleTangentDirections l U) ≫ quotientProjMap ⊥) = q := by
    rw [show eNew.hom = e.hom ≫ eDelta.hom from rfl,
      QuarticNet.fourTangentDualToProjective_rescale U l hl]
    simp only [Category.assoc]
    rw [← Category.assoc eDelta.hom, hCancel, Category.id_comp]
    exact hpoint
  refine ⟨eNew, hNew, ?_⟩
  rw [← hNew, QuarticNet.intrinsicFullQuadraticBaseIdeal_comp_iso]

/-- The weighted relation statement is independent of every nonzero row
rescaling. No division by a relation weight is used: weights may be zero. -/
theorem suppliedFourTangent_weighted_relation_rescale_iff
    (U : Fin 4 → Fin 4 → K) (hdiag : ∀ r, U r r = 0)
    (l : Fin 4 → K) (hl : ∀ r, l r ≠ 0) :
    (∃ w : Fin 4 → K, w ≠ 0 ∧
      ∀ r s, r < s → w r * U r s = -(w s * U s r)) ↔
    (∃ w : Fin 4 → K, w ≠ 0 ∧
      ∀ r s, r < s →
        w r * QuarticNet.rescaleTangentDirections l U r s =
          -(w s * QuarticNet.rescaleTangentDirections l U s r)) := by
  let q := QuarticNet.fourTangentDualToProjective U ≫ quotientProjMap
    (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
  obtain ⟨eNew, hNew, hIdeal⟩ := suppliedFourTangent_rescale_same_embedding
    q U (Iso.refl _) (by simp [q]) l hl
  have hdiagNew : ∀ r, QuarticNet.rescaleTangentDirections l U r r = 0 := by
    intro r
    simp [QuarticNet.rescaleTangentDirections, hdiag]
  exact (QuarticNet.fourTangent_intrinsicQuadraticSystem_finrank_ge_three_iff
    U hdiag).symm.trans (suppliedFourTangent_intrinsic_weighted_iff
      q (QuarticNet.rescaleTangentDirections l U) hdiagNew eNew hNew)

/-- Start with the manuscript's supplied skew/full-support presentation,
then change its epsilon generators arbitrarily. The changed matrix need
not be skew. Its weighted IFF and the same original-Z base classification
are derived, using the actual rescaled source/ambient square. -/
theorem suppliedFourTangent_rescaled_presentation_literal
    [IsAlgClosed K] {Z : Scheme.{u}}
    (q : Z ⟶ Proj (homogeneousSubmodule (Fin 4) K))
    (U : Fin 4 → Fin 4 → K) (hdiag : ∀ r, U r r = 0)
    (e : Z ≅ Spec (.of (QuarticNet.FourTangentDualAlgebra K)))
    (hpoint : e.hom ≫
      (QuarticNet.fourTangentDualToProjective U ≫ quotientProjMap ⊥) = q)
    (hskew : ∀ r s, U r s = -U s r)
    (hnonzero : ∀ r s, r ≠ s → U r s ≠ 0)
    (l : Fin 4 → K) (hl : ∀ r, l r ≠ 0) :
    ∃ eNew : Z ≅ Spec (.of (QuarticNet.FourTangentDualAlgebra K)),
      eNew.hom ≫
        (QuarticNet.fourTangentDualToProjective
          (QuarticNet.rescaleTangentDirections l U) ≫ quotientProjMap ⊥) = q ∧
      (3 ≤ finrank K (intrinsicFullQuadraticSystem q) ↔
        ∃ w : Fin 4 → K, w ≠ 0 ∧ ∀ r s, r < s →
          w r * QuarticNet.rescaleTangentDirections l U r s =
            -(w s * QuarticNet.rescaleTangentDirections l U s r)) ∧
      QuarticNet.IntrinsicFullBaseEmbeddedAlternative q := by
  obtain ⟨eNew, hNew, hIdeal⟩ :=
    suppliedFourTangent_rescale_same_embedding q U e hpoint l hl
  have hdiagNew : ∀ r, QuarticNet.rescaleTangentDirections l U r r = 0 := by
    intro r
    simp [QuarticNet.rescaleTangentDirections, hdiag]
  exact ⟨eNew, hNew,
    suppliedFourTangent_intrinsic_weighted_iff _ _ hdiagNew eNew hNew,
    suppliedFourTangent_intrinsic_fullBase_alternative q U hdiag e hpoint hskew hnonzero⟩

/-- Two independently chosen K-algebra epsilon presentations of the SAME
four component algebras differ by actual nonzero row rescaling on every
element, hence on the actual coordinate tuple x. This primitive has no
weighted-relation or skewness hypothesis. -/
theorem suppliedLengthTwoFamilies_actual_coordinate_rescaling
    (A : Fin 4 → Type u) [∀ r, CommRing (A r)] [∀ r, Algebra K (A r)]
    (eOne eTwo : ∀ r, A r ≃ₐ[K] DualNumber K)
    (x : ∀ r, Fin 4 → A r) :
    ∃ (l : Fin 4 → K) (hl : ∀ r, l r ≠ 0),
      (∀ r a, eTwo r a = QuarticNet.dualNumberRescaleEquiv (l r) (hl r) (eOne r a)) ∧
      (fun r s => (eTwo r (x r s)).snd) =
        QuarticNet.rescaleTangentDirections l (fun r s => (eOne r (x r s)).snd) := by
  classical
  have hEach (r : Fin 4) :=
    QuarticNet.actualLengthTwoDualPresentations_rescale (eOne r) (eTwo r)
  choose l hl hChange using hEach
  refine ⟨l, hl, hChange, ?_⟩
  funext r s
  rw [hChange]
  change (QuarticNet.dualNumberRescale (l r) (eOne r (x r s))).snd = _
  simp [QuarticNet.dualNumberRescale, QuarticNet.rescaleTangentDirections,
    TrivSqZeroExt.snd_map, LinearMap.mulLeft_apply]

end PfaffianDescent
