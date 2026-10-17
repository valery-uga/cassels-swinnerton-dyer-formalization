import PfaffianDescent.IncidenceGrassmannianProjection

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

/-- The inverse image of another gluing chart is exactly the prescribed overlap. -/
lemma schemeGlueData_chart_preimage (D : Scheme.GlueData.{u}) (i j : D.J) :
    (D.ι i) ⁻¹ᵁ (D.ι j).opensRange = (D.f i j).opensRange := by
  ext x
  change (∃ y, D.ι j y = D.ι i x) ↔ ∃ z, D.f i j z = x
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨z, hz, _⟩ := (Scheme.GlueData.ι_eq_iff D i j x y).mp hy.symm
    exact ⟨z, hz⟩
  · rintro ⟨z, hz⟩
    refine ⟨(D.t i j ≫ D.f j i) z, ?_⟩
    exact ((Scheme.GlueData.ι_eq_iff D i j x _).mpr ⟨z, hz, rfl⟩).symm

section
variable (K : Type u) [CommRing K]

lemma incidenceChartι_preimage (i j : Equiv.Perm (Fin 3 ⊕ Fin 3)) :
    incidenceChartι K i ⁻¹ᵁ (incidenceChartι K j).opensRange = (incidenceAtlasι K i j).opensRange :=
  schemeGlueData_chart_preimage (incidenceGlueData K) (ULift.up i) (ULift.up j)

lemma grassmannianChartι_preimage (i j : Equiv.Perm (Fin 3 ⊕ Fin 3)) :
    grassmannianChartι K i ⁻¹ᵁ (grassmannianChartι K j).opensRange = (grassmannianAtlasι K i j).opensRange :=
  schemeGlueData_chart_preimage (grassmannianGlueData K 3 3) (ULift.up i) (ULift.up j)

lemma incidenceGraphToGrassmannianChart_preimage (σ : Equiv.Perm (Fin 3 ⊕ Fin 3)) :
    incidenceGraphToGrassmannianChart K ⁻¹ᵁ (grassmannianOverlapι K σ).opensRange =
      (incidenceOverlapι K σ).opensRange := by
  rw [grassmannianOverlapι_opensRange, incidenceOverlapι_opensRange]
  ext p
  rfl

/-- The inverse image of a Grassmannian chart is the corresponding full incidence chart. -/
lemma incidenceToGrassmannian_preimage (i : Equiv.Perm (Fin 3 ⊕ Fin 3)) :
    incidenceToGrassmannian K ⁻¹ᵁ (grassmannianChartι K i).opensRange =
      (incidenceChartι K i).opensRange := by
  ext x
  obtain ⟨j, y, rfl⟩ := incidenceChartι_jointly_surjective K x
  have h : incidenceChartι K j ⁻¹ᵁ
      (incidenceToGrassmannian K ⁻¹ᵁ (grassmannianChartι K i).opensRange) =
        incidenceChartι K j ⁻¹ᵁ (incidenceChartι K i).opensRange := by
    rw [← Scheme.Hom.comp_preimage, incidenceChartι_toGrassmannian,
      Scheme.Hom.comp_preimage, grassmannianChartι_preimage, incidenceChartι_preimage]
    change incidenceGraphToGrassmannianChart K ⁻¹ᵁ
      (grassmannianOverlapι K (grassmannianChartChange j i)).opensRange =
        (incidenceOverlapι K (grassmannianChartChange j i)).opensRange
    exact incidenceGraphToGrassmannianChart_preimage K _
  exact SetLike.ext_iff.mp h y

/-- Each affine-space trivialization lies over the whole corresponding Grassmannian chart. -/
theorem incidenceGrassmannianChart_isPullback (i : Equiv.Perm (Fin 3 ⊕ Fin 3)) :
    IsPullback (incidenceGraphToGrassmannianChart K) (incidenceChartι K i)
      (grassmannianChartι K i) (incidenceToGrassmannian K) :=
  IsOpenImmersion.isPullback _ _ _ _ (incidenceChartι_toGrassmannian K i)
    (incidenceToGrassmannian_preimage K i)

end
end PfaffianDescent
