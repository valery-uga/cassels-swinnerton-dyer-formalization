import PfaffianDescent.IncidenceProjectionCartesian
import PfaffianDescent.IncidenceChartProduct

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
section
variable (K : Type u) [CommRing K]

/-- The actual pullback of the global incidence projection is affine thirty-six-space over the chart. -/
noncomputable def incidenceLocalTrivialization (i : Equiv.Perm (Fin 3 ⊕ Fin 3)) :
    pullback (grassmannianChartι K i) (incidenceToGrassmannian K) ≅
      Spec (.of (MvPolynomial IncidenceFiberIndex (GrassmannianChartRing K 3 3))) :=
  (incidenceGrassmannianChart_isPullback K i).isoPullback.symm ≪≫ incidenceChartProductIso K

lemma incidenceLocalTrivialization_toChart (i : Equiv.Perm (Fin 3 ⊕ Fin 3)) :
    (incidenceLocalTrivialization K i).hom ≫ Spec.map (CommRingCat.ofHom
      (algebraMap (GrassmannianChartRing K 3 3) (MvPolynomial IncidenceFiberIndex (GrassmannianChartRing K 3 3)))) =
        pullback.fst (grassmannianChartι K i) (incidenceToGrassmannian K) := by
  change ((incidenceGrassmannianChart_isPullback K i).isoPullback.inv ≫
    (incidenceChartProductIso K).hom) ≫ _ = _
  rw [Category.assoc, incidenceChartProductIso_toGrassmannian]
  exact (incidenceGrassmannianChart_isPullback K i).isoPullback_inv_fst

/-- The rank in these local trivializations is exactly thirty-six. -/
theorem incidence_projection_locally_affine_thirty_six :
    Fintype.card IncidenceFiberIndex = 36 ∧
      ∀ i : Equiv.Perm (Fin 3 ⊕ Fin 3), Nonempty
        (pullback (grassmannianChartι K i) (incidenceToGrassmannian K) ≅
          Spec (.of (MvPolynomial IncidenceFiberIndex (GrassmannianChartRing K 3 3)))) :=
  ⟨incidenceFiberIndex_card, fun i => ⟨incidenceLocalTrivialization K i⟩⟩

end
end PfaffianDescent
