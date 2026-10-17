import PfaffianDescent.FourCoordinateVertexIntrinsicFullBaseAlternative
import PfaffianDescent.FullSupportGeometricSkewNormalization
import PfaffianDescent.FourTangentDualRescaleScheme

/-! The actual four-component full-base theorem with skewness DERIVED from
intrinsic dimension >=3 and full support. The true original embedding is
retained through the actual nonzero product-dual row rescaling. -/

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial Module
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K] [IsAlgClosed K]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem fourCoordinateVertex_intrinsicDimension_fullBase_alternative
    (Z : Fin 4 → Scheme.{u})
    (i : ∀ r, Z r ⟶ scheme (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)))
    [∀ r, IsClosedImmersion (i r)] [∀ r, IsFinite (i r ≫ toBase ⊥)]
    (hSupport : ∀ r, Set.range (i r) = {coordinateVertex (K := K) r})
    (hZ : ∀ r, AllCharacteristics.finiteSchemeRank (i r ≫ toBase ⊥) = 2)
    (hdim : 3 ≤ finrank K
      (intrinsicFullQuadraticSystem (Sigma.desc (fun r => i r ≫ quotientProjMap ⊥))))
    (hnonzero : ∀ r s, r ≠ s →
      fourCoordinateVertexActualTangentMatrix Z i hSupport hZ r s ≠ 0) :
    QuarticNet.IntrinsicFullBaseEmbeddedAlternative
      (Sigma.desc (fun r => i r ≫ quotientProjMap ⊥)) := by
  let U := fourCoordinateVertexActualTangentMatrix Z i hSupport hZ
  obtain ⟨e, hdiag, hrows, hfac⟩ :=
    Classical.choose_spec (fourCoordinateVertex_actual_scheme_presentation Z i hSupport hZ)
  let q := QuarticNet.fourTangentDualToProjective U ≫ quotientProjMap
    (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
  have hdimU : 3 ≤ finrank K (QuarticNet.homogeneousTangentQuadrics U) := by
    rw [← hfac, intrinsicFullQuadraticSystem_comp_isIso,
      QuarticNet.fourTangent_intrinsicQuadraticSystem_eq_tangentKernel U hdiag] at hdim
    exact hdim
  have hdimKer := QuarticNet.three_le_tangentQuadric_kernel_of_homogeneous U hdiag hdimU
  obtain ⟨l, hl, hskew⟩ :=
    QuarticNet.fullSupport_exists_actual_skew_rescaling U hdiag hdimKer hnonzero
  let V := QuarticNet.rescaleTangentDirections l U
  have hVdiag : ∀ r, V r r = 0 := by
    intro r
    simp [V, QuarticNet.rescaleTangentDirections, hdiag]
  have hV : V = QuarticNet.skewTangentDirections (V 0 1) (V 0 2) (V 0 3)
      (V 1 2) (V 1 3) (V 2 3) :=
    QuarticNet.skew_matrix_eq_parameters V hVdiag hskew
  have hVne : ∀ r s, r ≠ s → V r s ≠ 0 := by
    intro r s hrs
    exact mul_ne_zero (hl r) (hnonzero r s hrs)
  let delta := QuarticNet.fourTangentDualRescaleEquiv l hl
  let eDelta := Scheme.Spec.mapIso delta.toRingEquiv.toCommRingCatIso.symm.op
  let eNew := e ≪≫ eDelta
  let qNew := QuarticNet.fourTangentDualToProjective V ≫ quotientProjMap
    (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
  have hCancel : eDelta.hom ≫ Spec.map (CommRingCat.ofHom delta.toRingHom) = 𝟙 _ := by
    change eDelta.hom ≫ eDelta.inv = 𝟙 _
    exact eDelta.hom_inv_id
  have hOriginal : eNew.hom ≫ qNew =
      Sigma.desc (fun r => i r ≫ quotientProjMap ⊥) := by
    change (e ≪≫ eDelta).hom ≫
      (QuarticNet.fourTangentDualToProjective V ≫ quotientProjMap ⊥) = _
    rw [Iso.trans_hom, QuarticNet.fourTangentDualToProjective_rescale U l hl]
    simp only [Category.assoc]
    rw [← Category.assoc eDelta.hom, hCancel, Category.id_comp]
    exact hfac
  have hAlternative : QuarticNet.IntrinsicFullBaseEmbeddedAlternative qNew := by
    have h := QuarticNet.fourTangent_intrinsicFullQuadraticBase_embedded_alternative
      (V 0 1) (V 0 2) (V 0 3) (V 1 2) (V 1 3) (V 2 3)
      (hVne 0 1 (by decide)) (hVne 0 2 (by decide)) (hVne 0 3 (by decide))
      (hVne 1 2 (by decide)) (hVne 1 3 (by decide)) (hVne 2 3 (by decide))
    change QuarticNet.IntrinsicFullBaseEmbeddedAlternative
      (QuarticNet.fourTangentDualToProjective
        (QuarticNet.skewTangentDirections (V 0 1) (V 0 2) (V 0 3)
          (V 1 2) (V 1 3) (V 2 3)) ≫ quotientProjMap ⊥) at h
    simpa only [← hV] using h
  have h := QuarticNet.intrinsicFullBase_embedded_alternative_precomp_iso eNew qNew hAlternative
  change QuarticNet.IntrinsicFullBaseEmbeddedAlternative (eNew.hom ≫ qNew) at h
  simpa only [hOriginal] using h

end PfaffianDescent
