import PfaffianDescent.GrassmannianChartEvaluation
import PfaffianDescent.LocalRingChartFactorization
import PfaffianDescent.GrassmannianSmooth

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u
section
variable (K : Type u) [CommRing K] {A : Type u} [CommRing A] [Algebra K A] {m n : ℕ}

lemma grassmannianChartEvaluation_exists (f : Spec (.of A) ⟶ grassmannianChartScheme K m n)
    (hf : f ≫ grassmannianChartToBase K m n = Spec.map (CommRingCat.ofHom (algebraMap K A))) :
    ∃ T : Matrix (Fin n) (Fin m) A, grassmannianChartEvaluation K T = f := by
  obtain ⟨φ, hφ⟩ := Spec.map_surjective f
  have hC : φ.hom.comp (algebraMap K (GrassmannianChartRing K m n)) = algebraMap K A := by
    have hb : Spec.map (CommRingCat.ofHom (algebraMap K (GrassmannianChartRing K m n)) ≫ φ) =
        Spec.map (CommRingCat.ofHom (algebraMap K A)) := by
      rw [Spec.map_comp]
      exact (congrArg (fun f => f ≫ grassmannianChartToBase K m n) hφ).trans hf
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective hb)
  let T : Matrix (Fin n) (Fin m) A := fun i j => φ.hom (MvPolynomial.X (i, j))
  refine ⟨T, ?_⟩
  have he : (MvPolynomial.aeval (R := K) (fun ij : Fin n × Fin m => T ij.1 ij.2)).toRingHom = φ.hom := by
    apply MvPolynomial.ringHom_ext
    · intro k
      change MvPolynomial.aeval _ (MvPolynomial.C k) = φ.hom (MvPolynomial.C k)
      rw [MvPolynomial.aeval_C]
      exact (RingHom.congr_fun hC k).symm
    · intro ij
      exact MvPolynomial.aeval_X _ _
  exact (congrArg (fun f => Spec.map (CommRingCat.ofHom f)) he).trans hφ

lemma grassmannianChartEvaluation_map {B : Type u} [CommRing B] [Algebra K B]
    (φ : A →ₐ[K] B) (T : Matrix (Fin n) (Fin m) A) :
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ grassmannianChartEvaluation K T =
      grassmannianChartEvaluation K (T.map φ) := by
  change Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := K) (fun ij : Fin n × Fin m => T ij.1 ij.2)).toRingHom) = _
  rw [← Spec.map_comp]
  have he : φ.comp (MvPolynomial.aeval (R := K) (fun ij : Fin n × Fin m => T ij.1 ij.2)) =
      MvPolynomial.aeval (R := K) (fun ij : Fin n × Fin m => (T.map φ) ij.1 ij.2) := by
    apply MvPolynomial.algHom_ext
    intro ij
    simp only [AlgHom.comp_apply, MvPolynomial.aeval_X]
    rfl
  exact congrArg (fun f : GrassmannianChartRing K m n →ₐ[K] B => Spec.map (CommRingCat.ofHom f.toRingHom)) he

/-- Every local-algebra-valued Grassmannian point is represented by a matrix in one chart. -/
theorem grassmannian_local_algebra_point [IsLocalRing A]
    (f : Spec (.of A) ⟶ grassmannianScheme K m n)
    (hf : f ≫ grassmannianToBase K m n = Spec.map (CommRingCat.ofHom (algebraMap K A))) :
    ∃ (i : Equiv.Perm (Fin m ⊕ Fin n)) (T : Matrix (Fin n) (Fin m) A),
      grassmannianChartEvaluation K T ≫ grassmannianChartι K i = f := by
  obtain ⟨i, g, hg⟩ := localRing_morphism_factors_openCover A (grassmannianGlueData K m n).openCover f
  let j : Equiv.Perm (Fin m ⊕ Fin n) := i.down
  let g' : Spec (.of A) ⟶ grassmannianChartScheme K m n := g
  have hg' : g' ≫ grassmannianChartι K j = f := hg
  have hb : g' ≫ grassmannianChartToBase K m n = Spec.map (CommRingCat.ofHom (algebraMap K A)) := by
    calc
      g' ≫ grassmannianChartToBase K m n = g' ≫ (grassmannianChartι K j ≫ grassmannianToBase K m n) :=
        congrArg (fun t => g' ≫ t) (grassmannianChartι_toBase K j).symm
      _ = (g' ≫ grassmannianChartι K j) ≫ grassmannianToBase K m n := (Category.assoc _ _ _).symm
      _ = f ≫ grassmannianToBase K m n := congrArg (fun t => t ≫ grassmannianToBase K m n) hg'
      _ = _ := hf
  obtain ⟨T, hT⟩ := grassmannianChartEvaluation_exists K g' hb
  exact ⟨j, T, (congrArg (fun g => g ≫ grassmannianChartι K j) hT).trans hg'⟩

end
end PfaffianDescent
