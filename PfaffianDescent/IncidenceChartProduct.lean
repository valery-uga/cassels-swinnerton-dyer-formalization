import PfaffianDescent.IncidenceGrassmannianProjection
import Mathlib.Algebra.MvPolynomial.Equiv

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u
section
variable (K : Type u) [CommRing K]

/-- The thirty-six independent form coordinates over a Grassmannian graph chart. -/
abbrev IncidenceFiberIndex := Fin 3 × IncidenceKernelIndex

lemma incidenceFiberIndex_card : Fintype.card IncidenceFiberIndex = 36 := by
  rw [Fintype.card_prod, incidenceKernelIndex_card]
  norm_num

/-- Separate the graph coordinates from the free coordinates of the three forms. -/
noncomputable def incidenceChartProductAlgEquiv :
    IncidenceGraphRing K ≃ₐ[K] MvPolynomial IncidenceFiberIndex (GrassmannianChartRing K 3 3) :=
  (MvPolynomial.renameEquiv K (Equiv.sumComm (Fin 3 × Fin 3) IncidenceFiberIndex)).trans
    (MvPolynomial.sumAlgEquiv K IncidenceFiberIndex (Fin 3 × Fin 3))

lemma incidenceChartProductAlgEquiv_inl (j : Fin 3 × Fin 3) :
    incidenceChartProductAlgEquiv K (MvPolynomial.X (Sum.inl j)) =
      MvPolynomial.C (MvPolynomial.X j) := by
  simp [incidenceChartProductAlgEquiv]

lemma incidenceChartProductAlgEquiv_inr (j : IncidenceFiberIndex) :
    incidenceChartProductAlgEquiv K (MvPolynomial.X (Sum.inr j)) = MvPolynomial.X j := by
  simp [incidenceChartProductAlgEquiv]

lemma incidenceChartProductAlgEquiv_comp_rename :
    (incidenceChartProductAlgEquiv K).toRingHom.comp
      (MvPolynomial.rename (R := K) (Sum.inl : Fin 3 × Fin 3 → IncidenceGraphIndex)).toRingHom =
        MvPolynomial.C := by
  apply MvPolynomial.ringHom_ext
  · intro k
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      MvPolynomial.rename_C]
    exact (incidenceChartProductAlgEquiv K).commutes k
  · intro j
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      MvPolynomial.rename_X]
    exact incidenceChartProductAlgEquiv_inl K j

lemma incidenceChartProductAlgEquiv_symm_comp_C :
    (incidenceChartProductAlgEquiv K).symm.toRingHom.comp MvPolynomial.C =
      (MvPolynomial.rename (R := K) (Sum.inl : Fin 3 × Fin 3 → IncidenceGraphIndex)).toRingHom := by
  apply RingHom.ext
  intro p
  apply (incidenceChartProductAlgEquiv K).injective
  change incidenceChartProductAlgEquiv K ((incidenceChartProductAlgEquiv K).symm (MvPolynomial.C p)) = _
  rw [AlgEquiv.apply_symm_apply]
  exact (RingHom.congr_fun (incidenceChartProductAlgEquiv_comp_rename K) p).symm

/-- The incidence chart is affine thirty-six-space over the Grassmannian chart. -/
noncomputable def incidenceChartProductIso :
    incidenceGraphScheme K ≅ Spec (.of (MvPolynomial IncidenceFiberIndex (GrassmannianChartRing K 3 3))) :=
  Scheme.Spec.mapIso (incidenceChartProductAlgEquiv K).symm.toRingEquiv.toCommRingCatIso.op

lemma incidenceChartProductIso_toGrassmannian :
    (incidenceChartProductIso K).hom ≫ Spec.map (CommRingCat.ofHom
      (algebraMap (GrassmannianChartRing K 3 3) (MvPolynomial IncidenceFiberIndex (GrassmannianChartRing K 3 3)))) =
        incidenceGraphToGrassmannianChart K := by
  change Spec.map (CommRingCat.ofHom (incidenceChartProductAlgEquiv K).symm.toRingHom) ≫
    Spec.map (CommRingCat.ofHom MvPolynomial.C) = _
  rw [← Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) (incidenceChartProductAlgEquiv_symm_comp_C K)

instance incidenceGraphToGrassmannianChart_smooth : Smooth (incidenceGraphToGrassmannianChart K) := by
  apply (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
  change (MvPolynomial.rename (R := K) (Sum.inl : Fin 3 × Fin 3 → IncidenceGraphIndex)).toRingHom.Smooth
  rw [← incidenceChartProductAlgEquiv_symm_comp_C]
  have hp : (algebraMap (GrassmannianChartRing K 3 3)
      (MvPolynomial IncidenceFiberIndex (GrassmannianChartRing K 3 3))).Smooth := by
    apply RingHom.smooth_algebraMap.mpr
    exact ⟨inferInstance, inferInstance⟩
  exact hp.comp (RingHom.Smooth.of_bijective (incidenceChartProductAlgEquiv K).symm.bijective)

/-- The projection to the Grassmannian is smooth, as verified on the affine chart cover. -/
instance incidenceToGrassmannian_smooth : Smooth (incidenceToGrassmannian K) := by
  let 𝒰 := (incidenceGlueData K).openCover
  letI : IsZariskiLocalAtSource (@Smooth.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Smooth)
  apply IsZariskiLocalAtSource.of_openCover (P := @Smooth.{u}) 𝒰
  intro i
  have hs : Smooth (𝒰.f i ≫ incidenceToGrassmannian K) := by
    change Smooth (incidenceChartι K i.down ≫ incidenceToGrassmannian K)
    rw [incidenceChartι_toGrassmannian]
    infer_instance
  exact hs

end
end PfaffianDescent
