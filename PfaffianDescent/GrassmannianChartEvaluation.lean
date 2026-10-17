import PfaffianDescent.GrassmannianScheme

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u
section
variable (K : Type u) [CommRing K] {A : Type u} [CommRing A] [Algebra K A] {m n : ℕ}

/-- The graph-chart point defined by a matrix over a coefficient algebra. -/
noncomputable def grassmannianChartEvaluation (T : Matrix (Fin n) (Fin m) A) :
    Spec (.of A) ⟶ grassmannianChartScheme K m n :=
  Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := K) (fun ij : Fin n × Fin m => T ij.1 ij.2)).toRingHom)

lemma grassmannianChartEvaluation_toBase (T : Matrix (Fin n) (Fin m) A) :
    grassmannianChartEvaluation K T ≫ grassmannianChartToBase K m n =
      Spec.map (CommRingCat.ofHom (algebraMap K A)) := by
  change Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := K) (fun ij : Fin n × Fin m => T ij.1 ij.2)).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap K (GrassmannianChartRing K m n))) = _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact (MvPolynomial.aeval (R := K) (fun ij : Fin n × Fin m => T ij.1 ij.2)).comp_algebraMap

lemma grassmannianOverlapLift_transition (σ : Equiv.Perm (Fin m ⊕ Fin n))
    (T : Matrix (Fin n) (Fin m) A)
    (h : Function.Bijective (graphTransitionFirst (graphCoordinatePermutation A σ) (Matrix.toLin' T))) :
    (grassmannianOverlapTransitionMatrix K σ).map
      (grassmannianOverlapLift K σ T ((graphOverlapDeterminant_isUnit_iff _ _).mpr h)) =
        graphTransitionMatrix σ T h := by
  have hT : (grassmannianOverlapUniversalMatrix K σ).map
      (grassmannianOverlapLift K σ T ((graphOverlapDeterminant_isUnit_iff _ _).mpr h)).toRingHom = T := by
    funext i j
    exact (grassmannianOverlapLift_apply K σ T ((graphOverlapDeterminant_isUnit_iff _ _).mpr h) (MvPolynomial.X (i, j))).trans (MvPolynomial.aeval_X _ _)
  exact graphTransition_matrix_map_of_eq
    (grassmannianOverlapLift K σ T ((graphOverlapDeterminant_isUnit_iff _ _).mpr h)).toRingHom σ
    (grassmannianOverlapUniversalMatrix K σ) T hT (grassmannianOverlapUniversal_bijective K σ) h

/-- A matrix in the overlap gives one morphism into the overlap scheme with the prescribed two chart values. -/
lemma grassmannianChartEvaluation_overlap (σ : Equiv.Perm (Fin m ⊕ Fin n))
    (T : Matrix (Fin n) (Fin m) A)
    (h : Function.Bijective (graphTransitionFirst (graphCoordinatePermutation A σ) (Matrix.toLin' T))) :
    ∃ a : Spec (.of A) ⟶ grassmannianOverlapScheme K σ,
      a ≫ grassmannianOverlapι K σ = grassmannianChartEvaluation K T ∧
      a ≫ grassmannianOverlapOtherι K σ = grassmannianChartEvaluation K (graphTransitionMatrix σ T h) := by
  let φ := grassmannianOverlapLift K σ T ((graphOverlapDeterminant_isUnit_iff _ _).mpr h)
  refine ⟨Spec.map (CommRingCat.ofHom φ.toRingHom), ?_, ?_⟩
  · change Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap _ _)) = _
    rw [← Spec.map_comp]
    apply congrArg (fun f => Spec.map (CommRingCat.ofHom f))
    apply RingHom.ext
    intro p
    exact grassmannianOverlapLift_apply K σ T ((graphOverlapDeterminant_isUnit_iff _ _).mpr h) p
  · rw [grassmannianOverlapOtherι_eq]
    change Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := K)
        (fun ij : Fin n × Fin m => grassmannianOverlapTransitionMatrix K σ ij.1 ij.2)).toRingHom) =
      Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := K)
        (fun ij : Fin n × Fin m => graphTransitionMatrix σ T h ij.1 ij.2)).toRingHom)
    rw [← Spec.map_comp]
    have he : φ.comp (MvPolynomial.aeval (R := K)
        (fun ij : Fin n × Fin m => grassmannianOverlapTransitionMatrix K σ ij.1 ij.2)) =
        MvPolynomial.aeval (R := K) (fun ij : Fin n × Fin m => graphTransitionMatrix σ T h ij.1 ij.2) := by
      apply MvPolynomial.algHom_ext
      rintro ⟨i, j⟩
      change φ (MvPolynomial.aeval _ (MvPolynomial.X (i, j))) = MvPolynomial.aeval _ (MvPolynomial.X (i, j))
      rw [MvPolynomial.aeval_X, MvPolynomial.aeval_X]
      exact congrFun (congrFun (grassmannianOverlapLift_transition K σ T h) i) j
    exact congrArg (fun f : GrassmannianChartRing K m n →ₐ[K] A =>
      Spec.map (CommRingCat.ofHom f.toRingHom)) he

lemma grassmannianChartEvaluation_glue (i j : Equiv.Perm (Fin m ⊕ Fin n))
    (T : Matrix (Fin n) (Fin m) A)
    (h : Function.Bijective (graphTransitionFirst (graphCoordinatePermutation A (grassmannianChartChange i j)) (Matrix.toLin' T))) :
    grassmannianChartEvaluation K T ≫ grassmannianChartι K i =
      grassmannianChartEvaluation K (graphTransitionMatrix (grassmannianChartChange i j) T h) ≫ grassmannianChartι K j := by
  obtain ⟨a, ha, hb⟩ := grassmannianChartEvaluation_overlap K (grassmannianChartChange i j) T h
  have hg := congrArg (fun f => a ≫ f) (grassmannianChartι_glue K i j)
  rw [← Category.assoc (grassmannianAtlasTransition K i j), grassmannianAtlasTransition_ι] at hg
  change a ≫ (grassmannianOverlapOtherι K (grassmannianChartChange i j) ≫ grassmannianChartι K j) =
    a ≫ (grassmannianOverlapι K (grassmannianChartChange i j) ≫ grassmannianChartι K i) at hg
  rw [← Category.assoc, hb, ← Category.assoc, ha] at hg
  exact hg.symm

end
end PfaffianDescent
