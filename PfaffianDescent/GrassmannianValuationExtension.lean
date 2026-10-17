import PfaffianDescent.GrassmannianAlgebraPoints
import PfaffianDescent.GrassmannianMinorRatios

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u
section
variable (K : Type u) [CommRing K]
    {R L : Type u} [CommRing R] [IsDomain R] [ValuationRing R] [Field L]
    [Algebra K R] [Algebra R L] [Algebra K L] [IsScalarTower K R L] [IsFractionRing R L]
    {m n : ℕ}

lemma grassmannianChartChange_trans_right (i σ : Equiv.Perm (Fin m ⊕ Fin n)) :
    grassmannianChartChange i (σ.trans i) = σ := by
  apply Equiv.ext
  intro a
  simp [grassmannianChartChange]

lemma grassmannianChartEvaluation_glue_of_eq (i j σ : Equiv.Perm (Fin m ⊕ Fin n))
    (he : grassmannianChartChange i j = σ) (T : Matrix (Fin n) (Fin m) L)
    (h : Function.Bijective (graphTransitionFirst (graphCoordinatePermutation L σ) (Matrix.toLin' T))) :
    grassmannianChartEvaluation K T ≫ grassmannianChartι K i =
      grassmannianChartEvaluation K (graphTransitionMatrix σ T h) ≫ grassmannianChartι K j := by
  subst σ
  exact grassmannianChartEvaluation_glue K i j T h

/-- A fraction-field matrix point extends over a valuation ring after choosing an integral chart. -/
theorem grassmannian_matrix_valuation_extension
    (i : Equiv.Perm (Fin m ⊕ Fin n)) (T : Matrix (Fin n) (Fin m) L) :
    ∃ g : Spec (.of R) ⟶ grassmannianScheme K m n,
      Spec.map (CommRingCat.ofHom (algebraMap R L)) ≫ g =
        grassmannianChartEvaluation K T ≫ grassmannianChartι K i ∧
      g ≫ grassmannianToBase K m n = Spec.map (CommRingCat.ofHom (algebraMap K R)) := by
  obtain ⟨σ, hσ, hint⟩ := graph_exists_integral_normalization R T
  choose U hU using hint
  let V : Matrix (Fin n) (Fin m) R := Matrix.of U
  have hM : Matrix.map V (algebraMap R L) = graphTransitionMatrix σ T hσ := by
    funext a b
    exact hU a b
  let j := σ.trans i
  refine ⟨grassmannianChartEvaluation K V ≫ grassmannianChartι K j, ?_, ?_⟩
  · have hm := grassmannianChartEvaluation_map K (IsScalarTower.toAlgHom K R L) V
    have hm' : Spec.map (CommRingCat.ofHom (algebraMap R L)) ≫ grassmannianChartEvaluation K V =
        grassmannianChartEvaluation K (graphTransitionMatrix σ T hσ) := by
      exact hm.trans (congrArg (grassmannianChartEvaluation K) hM)
    rw [← Category.assoc, hm']
    exact (grassmannianChartEvaluation_glue_of_eq K i j σ
      (grassmannianChartChange_trans_right i σ) T hσ).symm
  · rw [Category.assoc, grassmannianChartι_toBase]
    exact grassmannianChartEvaluation_toBase K V

/-- Every Grassmannian-valued fraction-field point over the coefficient base extends to the valuation ring. -/
theorem grassmannian_valuation_extension
    (f : Spec (.of L) ⟶ grassmannianScheme K m n)
    (hf : f ≫ grassmannianToBase K m n = Spec.map (CommRingCat.ofHom (algebraMap K L))) :
    ∃ g : Spec (.of R) ⟶ grassmannianScheme K m n,
      Spec.map (CommRingCat.ofHom (algebraMap R L)) ≫ g = f ∧
      g ≫ grassmannianToBase K m n = Spec.map (CommRingCat.ofHom (algebraMap K R)) := by
  obtain ⟨i, T, hT⟩ := grassmannian_local_algebra_point K f hf
  obtain ⟨g, hg, hb⟩ := grassmannian_matrix_valuation_extension K (R := R) i T
  exact ⟨g, hg.trans hT, hb⟩

end
end PfaffianDescent
