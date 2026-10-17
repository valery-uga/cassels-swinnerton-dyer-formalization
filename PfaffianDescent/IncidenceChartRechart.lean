import PfaffianDescent.IncidenceAlgebraPoints

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u
section
variable (K : Type u) [CommRing K] {A : Type u} [CommRing A] [Algebra K A]

lemma incidenceChartEvaluation_overlap_factor
    (σ : Equiv.Perm (Fin 3 ⊕ Fin 3)) (p : IncidenceGraphPoints A)
    (hp : Function.Bijective (graphTransitionFirst (graphCoordinatePermutation A σ) p.1)) :
    ∃ a : Spec (.of A) ⟶ incidenceOverlapScheme K σ,
      a ≫ incidenceOverlapι K σ = incidenceChartEvaluation K p := by
  let φ := incidenceOverlapLift K σ p hp
  refine ⟨Spec.map (CommRingCat.ofHom φ.toRingHom), ?_⟩
  change Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap _ _)) = _
  rw [← Spec.map_comp]
  apply congrArg (fun f => Spec.map (CommRingCat.ofHom f))
  apply RingHom.ext
  intro q
  exact incidenceOverlapLift_apply K σ p hp q

lemma incidenceOverlap_chart_glue (i j : Equiv.Perm (Fin 3 ⊕ Fin 3)) :
    incidenceOverlapOtherι K (grassmannianChartChange i j) ≫ incidenceChartι K j =
      incidenceOverlapι K (grassmannianChartChange i j) ≫ incidenceChartι K i := by
  have h := incidenceChartι_glue K i j
  rw [← Category.assoc (incidenceAtlasTransition K i j), incidenceAtlasTransition_ι] at h
  exact h

/-- An actual algebra-valued graph point in an overlap factors through the other global chart. -/
theorem incidenceChartEvaluation_rechart (i j : Equiv.Perm (Fin 3 ⊕ Fin 3))
    (p : IncidenceGraphPoints A)
    (hp : Function.Bijective (graphTransitionFirst
      (graphCoordinatePermutation A (grassmannianChartChange i j)) p.1)) :
    ∃ g : Spec (.of A) ⟶ incidenceGraphScheme K,
      g ≫ incidenceChartι K j = incidenceChartEvaluation K p ≫ incidenceChartι K i := by
  obtain ⟨a, ha⟩ := incidenceChartEvaluation_overlap_factor K (grassmannianChartChange i j) p hp
  refine ⟨a ≫ incidenceOverlapOtherι K (grassmannianChartChange i j), ?_⟩
  calc
    (a ≫ incidenceOverlapOtherι K (grassmannianChartChange i j)) ≫ incidenceChartι K j =
        a ≫ (incidenceOverlapOtherι K (grassmannianChartChange i j) ≫ incidenceChartι K j) :=
      Category.assoc _ _ _
    _ = a ≫ (incidenceOverlapι K (grassmannianChartChange i j) ≫ incidenceChartι K i) :=
      congrArg (fun f => a ≫ f) (incidenceOverlap_chart_glue K i j)
    _ = (a ≫ incidenceOverlapι K (grassmannianChartChange i j)) ≫ incidenceChartι K i :=
      (Category.assoc _ _ _).symm
    _ = incidenceChartEvaluation K p ≫ incidenceChartι K i :=
      congrArg (fun f => f ≫ incidenceChartι K i) ha

end
end PfaffianDescent
