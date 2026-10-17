import PfaffianDescent.IncidenceClosedChartAlgebra
import PfaffianDescent.IncidenceGrassmannianChart
import PfaffianDescent.PolynomialSumPushout
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
section
variable (K : Type u) [CommRing K]

noncomputable def incidenceAmbientChartScheme : Scheme.{u} := Spec (.of (IncidenceAmbientChartRing K))

noncomputable def incidenceAmbientChartToGraph : incidenceAmbientChartScheme K ⟶ grassmannianChartScheme K 3 3 :=
  Spec.map (CommRingCat.ofHom (MvPolynomial.rename (R := K)
    (Sum.inl : Fin 3 × Fin 3 → (Fin 3 × Fin 3) ⊕ AlternatingTripleIndex)).toRingHom)

noncomputable def incidenceAmbientChartToTriples : incidenceAmbientChartScheme K ⟶ alternatingTripleScheme K :=
  Spec.map (CommRingCat.ofHom (MvPolynomial.rename (R := K)
    (Sum.inr : AlternatingTripleIndex → (Fin 3 × Fin 3) ⊕ AlternatingTripleIndex)).toRingHom)

/-- Insert an incidence point into the ambient graph-and-form parameter space. -/
noncomputable def incidenceClosedChartι (i : Equiv.Perm (Fin 3 ⊕ Fin 3)) :
    incidenceGraphScheme K ⟶ incidenceAmbientChartScheme K :=
  Spec.map (CommRingCat.ofHom (incidenceClosedChartAlgHom K i).toRingHom)

instance incidenceClosedChartι_isClosedImmersion (i : Equiv.Perm (Fin 3 ⊕ Fin 3)) :
    IsClosedImmersion (incidenceClosedChartι K i) :=
  IsClosedImmersion.spec_of_surjective _ (incidenceClosedChartAlgHom_surjective K i)

lemma incidenceClosedChartι_graph (i : Equiv.Perm (Fin 3 ⊕ Fin 3)) :
    incidenceClosedChartι K i ≫ incidenceAmbientChartToGraph K = incidenceGraphToGrassmannianChart K := by
  change Spec.map (CommRingCat.ofHom (incidenceClosedChartAlgHom K i).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (MvPolynomial.rename (R := K) Sum.inl).toRingHom) = _
  rw [← Spec.map_comp]
  apply congrArg (fun f => Spec.map (CommRingCat.ofHom f))
  apply MvPolynomial.ringHom_ext
  · intro k
    change incidenceClosedChartAlgHom K i ((MvPolynomial.rename Sum.inl) (MvPolynomial.C k)) =
      (MvPolynomial.rename Sum.inl) (MvPolynomial.C k)
    rw [MvPolynomial.rename_C, MvPolynomial.rename_C]
    exact (incidenceClosedChartAlgHom K i).commutes k
  · intro j
    exact (congrArg (incidenceClosedChartAlgHom K i) (MvPolynomial.rename_X Sum.inl j)).trans
      ((incidenceClosedChartAlgHom_inl K i j).trans (MvPolynomial.rename_X Sum.inl j).symm)

lemma incidenceClosedChartι_triples (i : Equiv.Perm (Fin 3 ⊕ Fin 3)) :
    incidenceClosedChartι K i ≫ incidenceAmbientChartToTriples K = incidenceChartToTriples K i := by
  change Spec.map (CommRingCat.ofHom (incidenceClosedChartAlgHom K i).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (MvPolynomial.rename (R := K) Sum.inr).toRingHom) = _
  rw [← Spec.map_comp]
  apply congrArg (fun f => Spec.map (CommRingCat.ofHom f))
  apply MvPolynomial.ringHom_ext
  · intro k
    change incidenceClosedChartAlgHom K i ((MvPolynomial.rename Sum.inr) (MvPolynomial.C k)) =
      MvPolynomial.aeval (R := K) (incidenceOriginalCoefficients i (incidenceGraphUniversal K)) (MvPolynomial.C k)
    rw [MvPolynomial.rename_C, MvPolynomial.aeval_C]
    exact (incidenceClosedChartAlgHom K i).commutes k
  · intro j
    exact (congrArg (incidenceClosedChartAlgHom K i) (MvPolynomial.rename_X Sum.inr j)).trans
      ((incidenceClosedChartAlgHom_inr K i j).trans (MvPolynomial.aeval_X _ j).symm)

/-- The ambient chart scheme is the actual product of graph and triple spaces over the coefficient base. -/
theorem incidenceAmbientChart_isPullback :
    IsPullback (incidenceAmbientChartToGraph K) (incidenceAmbientChartToTriples K)
      (grassmannianChartToBase K 3 3) (alternatingTripleToBase K) :=
  isPullback_SpecMap_of_isPushout _ _ _ _ (polynomialSum_isPushout K (Fin 3 × Fin 3) AlternatingTripleIndex)

noncomputable def incidenceChartEmbedding (i : Equiv.Perm (Fin 3 ⊕ Fin 3)) :
    incidenceGraphScheme K ⟶ pullback (grassmannianChartToBase K 3 3) (alternatingTripleToBase K) :=
  incidenceClosedChartι K i ≫ (incidenceAmbientChart_isPullback K).isoPullback.hom

instance incidenceChartEmbedding_isClosedImmersion (i : Equiv.Perm (Fin 3 ⊕ Fin 3)) :
    IsClosedImmersion (incidenceChartEmbedding K i) := by
  unfold incidenceChartEmbedding
  infer_instance

lemma incidenceChartEmbedding_fst (i : Equiv.Perm (Fin 3 ⊕ Fin 3)) :
    incidenceChartEmbedding K i ≫ pullback.fst _ _ = incidenceGraphToGrassmannianChart K := by
  rw [incidenceChartEmbedding, Category.assoc, IsPullback.isoPullback_hom_fst, incidenceClosedChartι_graph]

lemma incidenceChartEmbedding_snd (i : Equiv.Perm (Fin 3 ⊕ Fin 3)) :
    incidenceChartEmbedding K i ≫ pullback.snd _ _ = incidenceChartToTriples K i := by
  rw [incidenceChartEmbedding, Category.assoc, IsPullback.isoPullback_hom_snd, incidenceClosedChartι_triples]

end
end PfaffianDescent
