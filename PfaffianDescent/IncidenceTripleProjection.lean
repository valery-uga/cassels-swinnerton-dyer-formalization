import PfaffianDescent.IncidenceTripleChart
import PfaffianDescent.IncidenceSmooth

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
section
variable (K : Type u) [CommRing K]

lemma incidenceTripleChart_glue (i j : Equiv.Perm (Fin 3 ⊕ Fin 3)) :
    incidenceAtlasι K i j ≫ incidenceChartToTriples K i =
      (incidenceAtlasTransition K i j ≫ incidenceAtlasι K j i) ≫ incidenceChartToTriples K j := by
  rw [incidenceAtlasTransition_ι]
  change incidenceOverlapι K (grassmannianChartChange i j) ≫ incidenceChartToTriples K i = _
  simpa only [Category.id_comp] using incidenceChartToTriples_overlap K i j (𝟙 _)

/-- The global incidence projection to triples of alternating forms in the original ambient coordinates. -/
noncomputable def incidenceToTriples : incidenceScheme K ⟶ alternatingTripleScheme K :=
  Multicoequalizer.desc (incidenceGlueData K).toGlueData.diagram _
    (fun i => incidenceChartToTriples K i.down) (by
      rintro ⟨i, j⟩
      change incidenceAtlasι K i.down j.down ≫ incidenceChartToTriples K i.down =
        (incidenceAtlasTransition K i.down j.down ≫ incidenceAtlasι K j.down i.down) ≫
          incidenceChartToTriples K j.down
      exact incidenceTripleChart_glue K i.down j.down)

lemma incidenceChartι_toTriples (i : Equiv.Perm (Fin 3 ⊕ Fin 3)) :
    incidenceChartι K i ≫ incidenceToTriples K = incidenceChartToTriples K i := by
  unfold incidenceToTriples
  exact Multicoequalizer.π_desc (incidenceGlueData K).toGlueData.diagram _ _ _ (ULift.up i)

lemma incidenceToTriples_toBase :
    incidenceToTriples K ≫ alternatingTripleToBase K = incidenceToBase K := by
  apply Multicoequalizer.hom_ext (incidenceGlueData K).toGlueData.diagram
  intro i
  change incidenceChartι K i.down ≫ (incidenceToTriples K ≫ alternatingTripleToBase K) =
    incidenceChartι K i.down ≫ incidenceToBase K
  rw [← Category.assoc, incidenceChartι_toTriples, incidenceChartToTriples_toBase, incidenceChartι_toBase]

/-- On the identity chart the global projection is the original universal graph projection. -/
lemma incidenceChartToTriples_refl :
    incidenceChartToTriples K (Equiv.refl _) = incidenceGraphProjection K := by
  change Spec.map (CommRingCat.ofHom
      (MvPolynomial.aeval (R := K) (incidenceOriginalCoefficients (Equiv.refl _) (incidenceGraphUniversal K))).toRingHom) =
    Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := K) (incidenceGraphTripleCoefficients K)).toRingHom)
  congr 3

end
end PfaffianDescent
