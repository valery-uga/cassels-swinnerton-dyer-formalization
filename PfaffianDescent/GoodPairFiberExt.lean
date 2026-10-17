import PfaffianDescent.GoodPairLineChartMaps

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
section
variable (K : Type u) [CommRing K]

lemma goodPairFiberToGrassmannian_toBase :
    goodPairFiberToGrassmannian K ≫ grassmannianToBase K 3 3 = goodPairIncidenceFiberToBase K := by
  change (pullback.fst (incidenceToTriples K) (goodPairTripleSection K) ≫ incidenceToGrassmannian K) ≫
    grassmannianToBase K 3 3 = pullback.snd _ _
  rw [Category.assoc, incidenceToGrassmannian_toBase, ← incidenceToTriples_toBase,
    ← Category.assoc, pullback.condition, Category.assoc, goodPairTripleSection_toBase,
    Category.comp_id]

/-- A point of the fixed-pair incidence scheme is determined by its underlying Grassmannian point. -/
lemma goodPairFiber_hom_ext {X : Scheme.{u}} (f g : X ⟶ goodPairIncidenceFiber K)
    (h : f ≫ goodPairFiberToGrassmannian K = g ≫ goodPairFiberToGrassmannian K) : f = g := by
  have hb : f ≫ goodPairIncidenceFiberToBase K = g ≫ goodPairIncidenceFiberToBase K := by
    rw [← goodPairFiberToGrassmannian_toBase K, ← Category.assoc, ← Category.assoc, h]
  change X ⟶ pullback (incidenceToTriples K) (goodPairTripleSection K) at f g
  change f ≫ (pullback.fst _ _ ≫ incidenceToGrassmannian K) =
    g ≫ (pullback.fst _ _ ≫ incidenceToGrassmannian K) at h
  change f ≫ pullback.snd _ _ = g ≫ pullback.snd _ _ at hb
  apply pullback.hom_ext
  · apply (cancel_mono (incidenceEmbedding K)).mp
    apply pullback.hom_ext
    · simpa only [Category.assoc, incidenceEmbedding_fst] using h
    · simp only [Category.assoc, incidenceEmbedding_snd]
      simp only [Category.assoc, pullback.condition]
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (fun q => q ≫ goodPairTripleSection K) hb).trans (Category.assoc _ _ _))
  · exact hb

instance goodPairFiberToGrassmannian_mono : Mono (goodPairFiberToGrassmannian K) where
  right_cancellation := fun _ _ h => goodPairFiber_hom_ext K _ _ h

variable {A : Type u} [CommRing A] [Algebra K A]

/-- Conversely, equality of the three line images determines the actual incidence chart point. -/
lemma goodMixedPairEvaluation_eq_of_lines (ε δ : Fin 3 → Bool) (u v : Fin 3 → A)
    (h : ∀ i, polynomialSchemeEvaluation K (Fin 3) u ≫ goodMixedPairToLine K ε i =
      polynomialSchemeEvaluation K (Fin 3) v ≫ goodMixedPairToLine K δ i) :
    polynomialSchemeEvaluation K (Fin 3) u ≫ goodMixedPairToGlobalFiber K ε =
      polynomialSchemeEvaluation K (Fin 3) v ≫ goodMixedPairToGlobalFiber K δ := by
  apply goodPairFiber_hom_ext K
  rw [goodMixedPairEvaluation_toGrassmannian, goodMixedPairEvaluation_toGrassmannian]
  apply (grassmannianChartEvaluation_eq_iff_submodule K _ _ _ _).mpr
  apply goodMixedChartSubmodule_eq_of_components A ε δ u v
  intro i
  apply (grassmannianChartEvaluation_eq_iff_submodule K _ _ _ _).mp
  exact (goodMixedPairEvaluation_toLine K ε u i).symm.trans
    ((h i).trans (goodMixedPairEvaluation_toLine K δ v i))

end
end PfaffianDescent
