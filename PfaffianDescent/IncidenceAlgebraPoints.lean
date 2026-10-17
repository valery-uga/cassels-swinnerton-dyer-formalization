import PfaffianDescent.IncidenceTripleProjection
import PfaffianDescent.IncidenceGrassmannianProjection
import PfaffianDescent.GrassmannianAlgebraPoints

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u
section
variable (K : Type u) [CommRing K] {A : Type u} [CommRing A] [Algebra K A]

/-- The scheme-valued incidence-chart point of an actual graph and isotropic triple. -/
noncomputable def incidenceChartEvaluation (p : IncidenceGraphPoints A) :
    Spec (.of A) ⟶ incidenceGraphScheme K :=
  Spec.map (CommRingCat.ofHom
    (MvPolynomial.aeval (R := K) (incidenceGraphPointCoordinates A p)).toRingHom)

lemma incidenceChartEvaluation_toBase (p : IncidenceGraphPoints A) :
    incidenceChartEvaluation K p ≫ incidenceGraphToBase K =
      Spec.map (CommRingCat.ofHom (algebraMap K A)) := by
  change Spec.map (CommRingCat.ofHom
    (MvPolynomial.aeval (R := K) (incidenceGraphPointCoordinates A p)).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap K (IncidenceGraphRing K))) = _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact (MvPolynomial.aeval (R := K) (incidenceGraphPointCoordinates A p)).comp_algebraMap

lemma incidenceGraphPointMap_aeval_universal (p : IncidenceGraphPoints A) :
    incidenceGraphPointMap
      (MvPolynomial.aeval (R := K) (incidenceGraphPointCoordinates A p)).toRingHom
      (incidenceGraphUniversal K) = p := by
  apply (incidenceGraphPointCoordinates A).injective
  rw [incidenceGraphPointMap_coordinates, incidenceGraphUniversal_coordinates]
  funext j
  exact MvPolynomial.aeval_X _ _

lemma incidenceChartEvaluation_exists (f : Spec (.of A) ⟶ incidenceGraphScheme K)
    (hf : f ≫ incidenceGraphToBase K = Spec.map (CommRingCat.ofHom (algebraMap K A))) :
    ∃ p : IncidenceGraphPoints A, incidenceChartEvaluation K p = f := by
  obtain ⟨φ, hφ⟩ := Spec.map_surjective f
  have hC : φ.hom.comp (algebraMap K (IncidenceGraphRing K)) = algebraMap K A := by
    have hb : Spec.map (CommRingCat.ofHom (algebraMap K (IncidenceGraphRing K)) ≫ φ) =
        Spec.map (CommRingCat.ofHom (algebraMap K A)) := by
      rw [Spec.map_comp]
      exact (congrArg (fun f => f ≫ incidenceGraphToBase K) hφ).trans hf
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective hb)
  let p := (incidenceGraphPointCoordinates A).symm (fun j => φ.hom (MvPolynomial.X j))
  have hc : incidenceGraphPointCoordinates A p = fun j => φ.hom (MvPolynomial.X j) :=
    (incidenceGraphPointCoordinates A).apply_symm_apply _
  refine ⟨p, ?_⟩
  have he : (MvPolynomial.aeval (R := K) (incidenceGraphPointCoordinates A p)).toRingHom = φ.hom := by
    apply MvPolynomial.ringHom_ext
    · intro k
      change MvPolynomial.aeval _ (MvPolynomial.C k) = φ.hom (MvPolynomial.C k)
      rw [MvPolynomial.aeval_C]
      exact (RingHom.congr_fun hC k).symm
    · intro j
      change MvPolynomial.aeval _ (MvPolynomial.X j) = φ.hom (MvPolynomial.X j)
      rw [MvPolynomial.aeval_X, hc]
  exact (congrArg (fun f => Spec.map (CommRingCat.ofHom f)) he).trans hφ

lemma incidenceChartEvaluation_toGraph (p : IncidenceGraphPoints A) :
    incidenceChartEvaluation K p ≫ incidenceGraphToGrassmannianChart K =
      grassmannianChartEvaluation K (LinearMap.toMatrix' p.1) := by
  change Spec.map (CommRingCat.ofHom
    (MvPolynomial.aeval (R := K) (incidenceGraphPointCoordinates A p)).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (MvPolynomial.rename (R := K) Sum.inl).toRingHom) = _
  rw [← Spec.map_comp]
  have he : (MvPolynomial.aeval (R := K) (incidenceGraphPointCoordinates A p)).comp
      (MvPolynomial.rename (R := K) (Sum.inl : Fin 3 × Fin 3 → IncidenceGraphIndex)) =
      MvPolynomial.aeval (R := K) (fun ij => LinearMap.toMatrix' p.1 ij.1 ij.2) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨i, j⟩
    simp only [AlgHom.comp_apply, MvPolynomial.rename_X, MvPolynomial.aeval_X]
    rfl
  exact congrArg (fun φ : GrassmannianChartRing K 3 3 →ₐ[K] A => Spec.map (CommRingCat.ofHom φ.toRingHom)) he

lemma incidenceChartEvaluation_toTriples (i : Equiv.Perm (Fin 3 ⊕ Fin 3))
    (p : IncidenceGraphPoints A) :
    incidenceChartEvaluation K p ≫ incidenceChartToTriples K i =
      Spec.map (CommRingCat.ofHom
        (MvPolynomial.aeval (R := K) (incidenceOriginalCoefficients i p)).toRingHom) := by
  change Spec.map (CommRingCat.ofHom
    (MvPolynomial.aeval (R := K) (incidenceGraphPointCoordinates A p)).toRingHom) ≫
    Spec.map (CommRingCat.ofHom
      (MvPolynomial.aeval (R := K) (incidenceOriginalCoefficients i (incidenceGraphUniversal K))).toRingHom) = _
  rw [← Spec.map_comp]
  have he : (MvPolynomial.aeval (R := K) (incidenceGraphPointCoordinates A p)).comp
      (MvPolynomial.aeval (R := K) (incidenceOriginalCoefficients i (incidenceGraphUniversal K))) =
      MvPolynomial.aeval (R := K) (incidenceOriginalCoefficients i p) := by
    apply MvPolynomial.algHom_ext
    intro j
    simp only [AlgHom.comp_apply, MvPolynomial.aeval_X]
    have hp := congrArg (fun q => incidenceOriginalCoefficients i q j)
      (incidenceGraphPointMap_aeval_universal K p)
    rw [incidenceOriginalCoefficients_map] at hp
    exact hp
  exact congrArg (fun φ : AlternatingTripleRing K →ₐ[K] A => Spec.map (CommRingCat.ofHom φ.toRingHom)) he

/-- Every local-algebra-valued point of the global incidence is represented by
an actual graph with an actual common-isotropic triple in one chart. -/
theorem incidence_local_algebra_point [IsLocalRing A]
    (f : Spec (.of A) ⟶ incidenceScheme K)
    (hf : f ≫ incidenceToBase K = Spec.map (CommRingCat.ofHom (algebraMap K A))) :
    ∃ (i : Equiv.Perm (Fin 3 ⊕ Fin 3)) (p : IncidenceGraphPoints A),
      incidenceChartEvaluation K p ≫ incidenceChartι K i = f := by
  obtain ⟨i, g, hg⟩ := localRing_morphism_factors_openCover A (incidenceGlueData K).openCover f
  let j : Equiv.Perm (Fin 3 ⊕ Fin 3) := i.down
  let g' : Spec (.of A) ⟶ incidenceGraphScheme K := g
  have hg' : g' ≫ incidenceChartι K j = f := hg
  have hb : g' ≫ incidenceGraphToBase K = Spec.map (CommRingCat.ofHom (algebraMap K A)) := by
    calc
      g' ≫ incidenceGraphToBase K = g' ≫ (incidenceChartι K j ≫ incidenceToBase K) :=
        congrArg (fun t => g' ≫ t) (incidenceChartι_toBase K j).symm
      _ = (g' ≫ incidenceChartι K j) ≫ incidenceToBase K := (Category.assoc _ _ _).symm
      _ = f ≫ incidenceToBase K := congrArg (fun t => t ≫ incidenceToBase K) hg'
      _ = _ := hf
  obtain ⟨p, hp⟩ := incidenceChartEvaluation_exists K g' hb
  exact ⟨j, p, (congrArg (fun g => g ≫ incidenceChartι K j) hp).trans hg'⟩

end
end PfaffianDescent
