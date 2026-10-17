import PfaffianDescent.GoodPairMixedIncidence
import PfaffianDescent.IncidenceAlgebraPoints

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u
section
variable (K : Type u) [CommRing K] {A B : Type u} [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]

lemma incidenceChartEvaluation_map (φ : A →ₐ[K] B) (p : IncidenceGraphPoints A) :
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ incidenceChartEvaluation K p =
      incidenceChartEvaluation K (incidenceGraphPointMap φ.toRingHom p) := by
  change Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := K) (incidenceGraphPointCoordinates A p)).toRingHom) = _
  rw [← Spec.map_comp]
  have he : φ.comp (MvPolynomial.aeval (R := K) (incidenceGraphPointCoordinates A p)) =
      MvPolynomial.aeval (R := K) (incidenceGraphPointCoordinates B (incidenceGraphPointMap φ.toRingHom p)) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, MvPolynomial.aeval_X, incidenceGraphPointMap_coordinates]
    rfl
  exact congrArg (fun ψ : IncidenceGraphRing K →ₐ[K] B => Spec.map (CommRingCat.ofHom ψ.toRingHom)) he

end
section
variable {R S : Type*} [CommRing R] [CommRing S]

lemma goodMixedPairAffinePoint_map (φ : R →+* S) (ε : Fin 3 → Bool) (u : Fin 3 → R) :
    incidenceGraphPointMap φ (goodMixedPairAffinePoint R ε u) = goodMixedPairAffinePoint S ε (φ ∘ u) := by
  have hT : Matrix.map (Matrix.diagonal u) φ = Matrix.diagonal (φ ∘ u) := by
    funext i j
    by_cases h : i = j
    · subst j
      simp
    · simp [Matrix.diagonal, h]
  have hfg (a : Fin 3 → R) :
      (goodMixedPairAffinePoint S ε (φ ∘ u)).1 (φ ∘ a) = φ ∘ (goodMixedPairAffinePoint R ε u).1 a := by
    have h := matrix_toLin_map_apply φ (Matrix.diagonal u) a
    rw [hT] at h
    exact h
  have hB (k : Fin 3) (x y : (Fin 3 → R) × (Fin 3 → R)) :
      ((goodMixedPairAffinePoint S ε (φ ∘ u)).2 k).1 ![(φ ∘ x.1, φ ∘ x.2), (φ ∘ y.1, φ ∘ y.2)] =
        φ (((goodMixedPairAffinePoint R ε u).2 k).1 ![x, y]) :=
    goodMixedPairChart_map φ ε k x y
  apply (incidenceGraphPointCoordinates S).injective
  rw [incidenceGraphPointMap_coordinates]
  exact (incidenceGraphPointCoordinates_of_compatible φ (goodMixedPairAffinePoint R ε u)
    (goodMixedPairAffinePoint S ε (φ ∘ u)) hfg hB).symm

end
end PfaffianDescent
