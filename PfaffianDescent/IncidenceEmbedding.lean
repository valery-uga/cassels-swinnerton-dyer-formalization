import PfaffianDescent.IncidenceClosedChart
import PfaffianDescent.IncidenceTripleProjection
import PfaffianDescent.IncidenceProjectionCartesian

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

lemma pullback_congrHom_fst {X Y Z : Scheme.{u}} {f₁ f₂ : X ⟶ Z} {g₁ g₂ : Y ⟶ Z}
    (h₁ : f₁ = f₂) (h₂ : g₁ = g₂) :
    (pullback.congrHom h₁ h₂).hom ≫ pullback.fst f₂ g₂ = pullback.fst f₁ g₁ := by
  subst f₂
  subst g₂
  simp [pullback.congrHom, pullback.map]

lemma pullback_congrHom_snd {X Y Z : Scheme.{u}} {f₁ f₂ : X ⟶ Z} {g₁ g₂ : Y ⟶ Z}
    (h₁ : f₁ = f₂) (h₂ : g₁ = g₂) :
    (pullback.congrHom h₁ h₂).hom ≫ pullback.snd f₂ g₂ = pullback.snd f₁ g₁ := by
  subst f₂
  subst g₂
  simp [pullback.congrHom, pullback.map]

section
variable (K : Type u) [CommRing K]

/-- The product of the Grassmannian and the affine triple space over the coefficient base. -/
noncomputable abbrev incidenceAmbientScheme : Scheme.{u} :=
  pullback (grassmannianToBase K 3 3) (alternatingTripleToBase K)

/-- Retain both the subspace and the original ambient triple. -/
noncomputable def incidenceEmbedding : incidenceScheme K ⟶ incidenceAmbientScheme K :=
  pullback.lift (incidenceToGrassmannian K) (incidenceToTriples K)
    ((incidenceToGrassmannian_toBase K).trans (incidenceToTriples_toBase K).symm)

@[reassoc]
lemma incidenceEmbedding_fst : incidenceEmbedding K ≫ pullback.fst _ _ = incidenceToGrassmannian K :=
  pullback.lift_fst _ _ _

@[reassoc]
lemma incidenceEmbedding_snd : incidenceEmbedding K ≫ pullback.snd _ _ = incidenceToTriples K :=
  pullback.lift_snd _ _ _

noncomputable abbrev incidenceAmbientGlobalChart (i : Equiv.Perm (Fin 3 ⊕ Fin 3)) : Scheme.{u} :=
  pullback (grassmannianChartι K i ≫ grassmannianToBase K 3 3) (alternatingTripleToBase K)

noncomputable def incidenceAmbientGlobalChartι (i : Equiv.Perm (Fin 3 ⊕ Fin 3)) :
    incidenceAmbientGlobalChart K i ⟶ incidenceAmbientScheme K :=
  pullback.map _ _ _ _ (grassmannianChartι K i) (𝟙 _) (𝟙 _) (by simp) (by simp)

@[reassoc]
lemma incidenceAmbientGlobalChartι_fst (i : Equiv.Perm (Fin 3 ⊕ Fin 3)) :
    incidenceAmbientGlobalChartι K i ≫ pullback.fst _ _ = pullback.fst _ _ ≫ grassmannianChartι K i := by
  unfold incidenceAmbientGlobalChartι pullback.map
  exact pullback.lift_fst _ _ _

@[reassoc]
lemma incidenceAmbientGlobalChartι_snd (i : Equiv.Perm (Fin 3 ⊕ Fin 3)) :
    incidenceAmbientGlobalChartι K i ≫ pullback.snd _ _ = pullback.snd _ _ := by
  unfold incidenceAmbientGlobalChartι pullback.map
  exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)

noncomputable def incidenceEmbeddingOnChart (i : Equiv.Perm (Fin 3 ⊕ Fin 3)) :
    incidenceGraphScheme K ⟶ incidenceAmbientGlobalChart K i :=
  incidenceChartEmbedding K i ≫ (pullback.congrHom (grassmannianChartι_toBase K i).symm rfl).hom

instance incidenceEmbeddingOnChart_isClosedImmersion (i : Equiv.Perm (Fin 3 ⊕ Fin 3)) :
    IsClosedImmersion (incidenceEmbeddingOnChart K i) := by
  unfold incidenceEmbeddingOnChart
  infer_instance

@[reassoc]
lemma incidenceEmbeddingOnChart_fst (i : Equiv.Perm (Fin 3 ⊕ Fin 3)) :
    incidenceEmbeddingOnChart K i ≫ pullback.fst _ _ = incidenceGraphToGrassmannianChart K := by
  rw [incidenceEmbeddingOnChart, Category.assoc]
  exact (congrArg (fun f => incidenceChartEmbedding K i ≫ f)
    (pullback_congrHom_fst (grassmannianChartι_toBase K i).symm rfl)).trans
      (incidenceChartEmbedding_fst K i)

@[reassoc]
lemma incidenceEmbeddingOnChart_snd (i : Equiv.Perm (Fin 3 ⊕ Fin 3)) :
    incidenceEmbeddingOnChart K i ≫ pullback.snd _ _ = incidenceChartToTriples K i := by
  rw [incidenceEmbeddingOnChart, Category.assoc]
  exact (congrArg (fun f => incidenceChartEmbedding K i ≫ f)
    (pullback_congrHom_snd (grassmannianChartι_toBase K i).symm rfl)).trans
      (incidenceChartEmbedding_snd K i)

lemma incidenceEmbeddingOnChart_fac (i : Equiv.Perm (Fin 3 ⊕ Fin 3)) :
    incidenceEmbeddingOnChart K i ≫ incidenceAmbientGlobalChartι K i =
      incidenceChartι K i ≫ incidenceEmbedding K := by
  apply pullback.hom_ext
  · simp only [Category.assoc, incidenceAmbientGlobalChartι_fst, incidenceEmbedding_fst,
      incidenceEmbeddingOnChart_fst_assoc, incidenceChartι_toGrassmannian]
  · simp only [Category.assoc, incidenceAmbientGlobalChartι_snd, incidenceEmbedding_snd,
      incidenceEmbeddingOnChart_snd, incidenceChartι_toTriples]

lemma incidenceAmbientGlobalChart_isPullback (i : Equiv.Perm (Fin 3 ⊕ Fin 3)) :
    IsPullback (pullback.fst _ _) (incidenceAmbientGlobalChartι K i)
      (grassmannianChartι K i) (pullback.fst (grassmannianToBase K 3 3) (alternatingTripleToBase K)) := by
  apply IsPullback.of_bot (v₂₁ := pullback.snd _ _) (v₂₂ := grassmannianToBase K 3 3)
  · rw [incidenceAmbientGlobalChartι_snd]
    exact IsPullback.of_hasPullback _ _
  · exact (incidenceAmbientGlobalChartι_fst K i).symm
  · exact IsPullback.of_hasPullback _ _

/-- The local closed embedding is the actual restriction of the global embedding. -/
theorem incidenceEmbeddingChart_isPullback (i : Equiv.Perm (Fin 3 ⊕ Fin 3)) :
    IsPullback (incidenceEmbeddingOnChart K i) (incidenceChartι K i)
      (incidenceAmbientGlobalChartι K i) (incidenceEmbedding K) := by
  apply IsPullback.of_right (h₁₂ := pullback.fst _ _) (h₂₂ := pullback.fst _ _)
  · rw [incidenceEmbeddingOnChart_fst, incidenceEmbedding_fst]
    exact incidenceGrassmannianChart_isPullback K i
  · exact incidenceEmbeddingOnChart_fac K i
  · exact incidenceAmbientGlobalChart_isPullback K i

/-- Common-isotropic incidence is a closed subscheme of the Grassmannian times the triple space. -/
instance incidenceEmbedding_isClosedImmersion : IsClosedImmersion (incidenceEmbedding K) := by
  let 𝒰 := Scheme.Pullback.openCoverOfLeft (grassmannianGlueData K 3 3).openCover
    (grassmannianToBase K 3 3) (alternatingTripleToBase K)
  apply IsZariskiLocalAtTarget.of_openCover (P := @IsClosedImmersion.{u}) 𝒰
  intro i
  change IsClosedImmersion (pullback.snd (incidenceEmbedding K) (incidenceAmbientGlobalChartι K i.down))
  rw [← (incidenceEmbeddingChart_isPullback K i.down).flip.isoPullback_inv_snd]
  infer_instance

end
end PfaffianDescent
