import PfaffianDescent.IncidenceScheme

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
section
variable (K : Type u) [CommRing K]

/-- The structure morphism of the global incidence scheme. -/
noncomputable def incidenceToBase : incidenceScheme K ⟶ Spec (.of K) :=
  Multicoequalizer.desc (incidenceGlueData K).toGlueData.diagram _
    (fun _ => incidenceGraphToBase K) (by
      rintro ⟨i, j⟩
      change incidenceAtlasι K i.down j.down ≫ incidenceGraphToBase K =
        (incidenceAtlasTransition K i.down j.down ≫ incidenceAtlasι K j.down i.down) ≫ incidenceGraphToBase K
      rw [incidenceAtlasTransition_ι]
      exact (incidenceOverlapOtherι_toBase K _).symm)

lemma incidenceChartι_toBase (i : Equiv.Perm (Fin 3 ⊕ Fin 3)) :
    incidenceChartι K i ≫ incidenceToBase K = incidenceGraphToBase K := by
  unfold incidenceToBase
  exact Multicoequalizer.π_desc (incidenceGlueData K).toGlueData.diagram _ _ _ (ULift.up i)

/-- The global incidence scheme is smooth over the coefficient base. -/
instance incidenceToBase_smooth : Smooth (incidenceToBase K) := by
  let 𝒰 := (incidenceGlueData K).openCover
  letI (i : 𝒰.I₀) : IsAffine (𝒰.X i) := inferInstanceAs (IsAffine (Spec (.of (IncidenceGraphRing K))))
  apply HasRingHomProperty.of_source_openCover (P := @Smooth.{u}) 𝒰
  intro i
  have hs : Smooth (𝒰.f i ≫ incidenceToBase K) := by
    change Smooth (incidenceChartι K i.down ≫ incidenceToBase K)
    rw [incidenceChartι_toBase]
    infer_instance
  exact HasRingHomProperty.appTop @Smooth _ hs

end
end PfaffianDescent
