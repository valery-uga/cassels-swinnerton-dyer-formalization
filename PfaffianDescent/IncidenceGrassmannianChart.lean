import PfaffianDescent.IncidenceSchemeCocycle
import PfaffianDescent.GrassmannianSchemeCocycle

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u
section
variable (K : Type u) [CommRing K]

/-- Forget the forms and retain the graph in a standard Grassmannian chart. -/
noncomputable def incidenceGraphToGrassmannianChart :
    incidenceGraphScheme K ⟶ grassmannianChartScheme K 3 3 :=
  Spec.map (CommRingCat.ofHom (MvPolynomial.rename (R := K)
    (Sum.inl : Fin 3 × Fin 3 → IncidenceGraphIndex)).toRingHom)

lemma incidenceGraphToGrassmannianChart_toBase :
    incidenceGraphToGrassmannianChart K ≫ grassmannianChartToBase K 3 3 = incidenceGraphToBase K := by
  change Spec.map (CommRingCat.ofHom (MvPolynomial.rename (R := K) Sum.inl).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap K (GrassmannianChartRing K 3 3))) = _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact (MvPolynomial.rename (R := K) (Sum.inl : Fin 3 × Fin 3 → IncidenceGraphIndex)).comp_algebraMap

lemma incidenceGraphToGrassmannianChart_matrix {X : Scheme.{u}} (f : X ⟶ incidenceGraphScheme K) :
    grassmannianChartMatrix K (f ≫ incidenceGraphToGrassmannianChart K) =
      LinearMap.toMatrix' (incidenceChartPoint K f).1 := by
  ext i j
  have h := RingHom.congr_fun (affineFunctionHom_comp_Spec f
    (MvPolynomial.rename (R := K) (Sum.inl : Fin 3 × Fin 3 → IncidenceGraphIndex)).toRingHom)
    (MvPolynomial.X (i, j))
  have hc := congrFun (incidenceChartPoint_coordinates K f) (Sum.inl (i, j))
  change LinearMap.toMatrix' (incidenceChartPoint K f).1 i j =
    affineFunctionHom f (MvPolynomial.X (Sum.inl (i, j))) at hc
  exact h.trans ((congrArg (affineFunctionHom f) (MvPolynomial.rename_X Sum.inl (i, j))).trans hc.symm)

end
section
variable {R : Type*} [CommRing R]

lemma graphTransitionMatrix_toMatrix (σ : Equiv.Perm (Fin 3 ⊕ Fin 3))
    (f : (Fin 3 → R) →ₗ[R] (Fin 3 → R))
    (h : Function.Bijective (graphTransitionFirst (graphCoordinatePermutation R σ) (Matrix.toLin' (LinearMap.toMatrix' f))))
    (hf : Function.Bijective (graphTransitionFirst (graphCoordinatePermutation R σ) f)) :
    graphTransitionMatrix σ (LinearMap.toMatrix' f) h =
      LinearMap.toMatrix' (graphTransition (graphCoordinatePermutation R σ) f hf) := by
  simp only [graphTransitionMatrix, Matrix.toLin'_toMatrix']

end
section
variable (K : Type u) [CommRing K]

/-- Forgetting the forms is compatible with both sides of every incidence overlap. -/
theorem incidenceGraphToGrassmannianChart_overlap {X : Scheme.{u}}
    (σ : Equiv.Perm (Fin 3 ⊕ Fin 3)) (g : X ⟶ incidenceOverlapScheme K σ) :
    ∃ a : X ⟶ grassmannianOverlapScheme K σ,
      a ≫ grassmannianOverlapι K σ = (g ≫ incidenceOverlapι K σ) ≫ incidenceGraphToGrassmannianChart K ∧
      a ≫ grassmannianOverlapOtherι K σ = (g ≫ incidenceOverlapOtherι K σ) ≫ incidenceGraphToGrassmannianChart K := by
  let f := g ≫ incidenceOverlapι K σ
  have hi := (incidenceChart_factor_iff K f σ).mp ⟨g, rfl⟩
  have hM : Function.Bijective (graphTransitionFirst (graphCoordinatePermutation Γ(X, ⊤) σ)
      (Matrix.toLin' (LinearMap.toMatrix' (incidenceChartPoint K f).1))) := by
    rw [Matrix.toLin'_toMatrix']
    exact hi
  have hG : Function.Bijective (graphTransitionFirst (graphCoordinatePermutation Γ(X, ⊤) σ)
      (Matrix.toLin' (grassmannianChartMatrix K (f ≫ incidenceGraphToGrassmannianChart K)))) := by
    rw [incidenceGraphToGrassmannianChart_matrix]
    exact hM
  let a := grassmannianChartLift K (f ≫ incidenceGraphToGrassmannianChart K) σ hG
  have ha : a ≫ grassmannianOverlapι K σ = f ≫ incidenceGraphToGrassmannianChart K :=
    grassmannianChartLift_fac K _ σ hG
  refine ⟨a, ha, grassmannianChart_morphism_ext K _ _ ?_ ?_⟩
  · calc
      (a ≫ grassmannianOverlapOtherι K σ) ≫ grassmannianChartToBase K 3 3 =
          (a ≫ grassmannianOverlapι K σ) ≫ grassmannianChartToBase K 3 3 := by
            simp only [Category.assoc, grassmannianOverlapOtherι_toBase]
      _ = f ≫ incidenceGraphToBase K := by rw [ha, Category.assoc, incidenceGraphToGrassmannianChart_toBase]
      _ = (g ≫ incidenceOverlapOtherι K σ) ≫ incidenceGraphToBase K := by
            simp only [f, Category.assoc, incidenceOverlapOtherι_toBase]
      _ = ((g ≫ incidenceOverlapOtherι K σ) ≫ incidenceGraphToGrassmannianChart K) ≫
          grassmannianChartToBase K 3 3 := by simp only [Category.assoc, incidenceGraphToGrassmannianChart_toBase]
  · have ha' := (grassmannianChart_factor_iff K (a ≫ grassmannianOverlapι K σ) σ).mp ⟨a, rfl⟩
    have he : grassmannianChartMatrix K (a ≫ grassmannianOverlapι K σ) =
        LinearMap.toMatrix' (incidenceChartPoint K f).1 := by
      rw [ha, incidenceGraphToGrassmannianChart_matrix]
    calc
      grassmannianChartMatrix K (a ≫ grassmannianOverlapOtherι K σ) =
          graphTransitionMatrix σ (grassmannianChartMatrix K (a ≫ grassmannianOverlapι K σ)) ha' :=
            grassmannianChartMatrix_transition K σ a ha'
      _ = graphTransitionMatrix σ (LinearMap.toMatrix' (incidenceChartPoint K f).1) hM :=
            graphTransitionMatrix_congr σ he ha' hM
      _ = LinearMap.toMatrix' (graphTransition (graphCoordinatePermutation Γ(X, ⊤) σ) (incidenceChartPoint K f).1 hi) :=
            graphTransitionMatrix_toMatrix σ (incidenceChartPoint K f).1 hM hi
      _ = LinearMap.toMatrix' (incidenceChartPoint K (g ≫ incidenceOverlapOtherι K σ)).1 :=
            congrArg (fun p : IncidenceGraphPoints Γ(X, ⊤) => LinearMap.toMatrix' p.1)
              (incidenceChartPoint_transition K σ g hi).symm
      _ = grassmannianChartMatrix K ((g ≫ incidenceOverlapOtherι K σ) ≫ incidenceGraphToGrassmannianChart K) :=
            (incidenceGraphToGrassmannianChart_matrix K _).symm

end
end PfaffianDescent
