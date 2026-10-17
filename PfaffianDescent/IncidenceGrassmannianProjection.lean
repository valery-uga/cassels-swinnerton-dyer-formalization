import PfaffianDescent.IncidenceGrassmannianChart
import PfaffianDescent.IncidenceSmooth
import PfaffianDescent.GrassmannianSmooth

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
section
variable (K : Type u) [CommRing K]

lemma incidenceGrassmannianChart_glue (i j : Equiv.Perm (Fin 3 ⊕ Fin 3)) :
    incidenceAtlasι K i j ≫ incidenceGraphToGrassmannianChart K ≫ grassmannianChartι K i =
      incidenceAtlasTransition K i j ≫ incidenceAtlasι K j i ≫
        incidenceGraphToGrassmannianChart K ≫ grassmannianChartι K j := by
  obtain ⟨a, ha, hb⟩ := incidenceGraphToGrassmannianChart_overlap K
    (grassmannianChartChange i j) (𝟙 _)
  simp only [Category.id_comp] at ha hb
  have hg := congrArg (fun f => a ≫ f) (grassmannianChartι_glue K i j)
  change a ≫ (grassmannianAtlasTransition K i j ≫ grassmannianAtlasι K j i ≫
    grassmannianChartι K j) = a ≫ (grassmannianAtlasι K i j ≫ grassmannianChartι K i) at hg
  rw [← Category.assoc (grassmannianAtlasTransition K i j), grassmannianAtlasTransition_ι] at hg
  change a ≫ (grassmannianOverlapOtherι K (grassmannianChartChange i j) ≫ grassmannianChartι K j) =
    a ≫ (grassmannianOverlapι K (grassmannianChartChange i j) ≫ grassmannianChartι K i) at hg
  rw [← Category.assoc, hb, ← Category.assoc, ha] at hg
  rw [← Category.assoc (incidenceAtlasTransition K i j), incidenceAtlasTransition_ι]
  change incidenceOverlapι K (grassmannianChartChange i j) ≫
    incidenceGraphToGrassmannianChart K ≫ grassmannianChartι K i = _
  simpa only [Category.assoc] using hg.symm

/-- The global projection which forgets the three forms and retains the isotropic subspace. -/
noncomputable def incidenceToGrassmannian : incidenceScheme K ⟶ grassmannianScheme K 3 3 :=
  Multicoequalizer.desc (incidenceGlueData K).toGlueData.diagram _
    (fun i => incidenceGraphToGrassmannianChart K ≫ grassmannianChartι K i.down) (by
      rintro ⟨i, j⟩
      change incidenceAtlasι K i.down j.down ≫
        (incidenceGraphToGrassmannianChart K ≫ grassmannianChartι K i.down) =
        (incidenceAtlasTransition K i.down j.down ≫ incidenceAtlasι K j.down i.down) ≫
          (incidenceGraphToGrassmannianChart K ≫ grassmannianChartι K j.down)
      simpa only [Category.assoc] using incidenceGrassmannianChart_glue K i.down j.down)

lemma incidenceChartι_toGrassmannian (i : Equiv.Perm (Fin 3 ⊕ Fin 3)) :
    incidenceChartι K i ≫ incidenceToGrassmannian K =
      incidenceGraphToGrassmannianChart K ≫ grassmannianChartι K i := by
  unfold incidenceToGrassmannian
  exact Multicoequalizer.π_desc (incidenceGlueData K).toGlueData.diagram _ _ _ (ULift.up i)

lemma incidenceToGrassmannian_toBase :
    incidenceToGrassmannian K ≫ grassmannianToBase K 3 3 = incidenceToBase K := by
  apply Multicoequalizer.hom_ext (incidenceGlueData K).toGlueData.diagram
  intro i
  change incidenceChartι K i.down ≫ (incidenceToGrassmannian K ≫ grassmannianToBase K 3 3) =
    incidenceChartι K i.down ≫ incidenceToBase K
  rw [← Category.assoc, incidenceChartι_toGrassmannian, Category.assoc,
    grassmannianChartι_toBase, incidenceGraphToGrassmannianChart_toBase, incidenceChartι_toBase]

end
end PfaffianDescent
