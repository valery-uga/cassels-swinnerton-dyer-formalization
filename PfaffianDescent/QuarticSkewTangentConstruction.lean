import PfaffianDescent.QuarticAffineLengthEight
import PfaffianDescent.QuarticJetNet
import PfaffianDescent.QuarticConjugateSpan

/-!
# Skew tangent matrix from a separable degree-four affine point

This packages the length-eight construction, geometric splitting, conjugate
coordinates, and semilinear normalization into the tangent matrix used by
the finite-net branches of Section 4.
-/

namespace PfaffianDescent
namespace QuarticNet

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial Module

universe u

theorem affine_length_eight_skew_tangent_construction
    {k L K : Type u} [Field k] [Field L] [Field K] [Algebra k L] [Algebra k K]
    [IsAlgClosed K] [Normal k K] [Infinite K]
    [FiniteDimensional k L] [Algebra.IsSeparable k L]
    (b : Basis (Fin 4) k L) (hb : b 0 = 1) (F : AffineThreeRing k)
    (hp : MvPolynomial.aeval (fun i : Fin 3 => b i.succ) F = 0)
    (hsmooth : affineDifferential (fun i : Fin 3 => b i.succ) F ≠ 0) :
    ∃ (e : Fin 4 ≃ (L →ₐ[k] K)) (v : Fin 3 → L)
      (hF : affineFirstJet (fun i : Fin 3 => b i.succ) v F = 0),
      v ≠ 0 ∧
      Function.Surjective (affineHypersurfaceJet (fun i : Fin 3 => b i.succ) v F hF) ∧
      IsClosedImmersion
        (Spec.map (CommRingCat.ofHom
          (affineHypersurfaceJet (fun i : Fin 3 => b i.succ) v F hF).toRingHom)) ∧
      Module.finrank k (DualNumber L) = 8 ∧
      ∃ l : Fin 4 → K, (∀ i, l i ≠ 0) ∧ ∀ i j,
        l i * conjugateTangentMatrix e b (Fin.cons 0 v)
          (conjugate_basis_span b e) i j =
          -(l j * conjugateTangentMatrix e b (Fin.cons 0 v)
            (conjugate_basis_span b e) j i) := by
  obtain ⟨v, hF, hv, hsurj, hclosed, hlen, hdim, _⟩ :=
    affine_length_eight_construction_geometrically_split (K := K) b hb F hp hsmooth
  have hL : Module.finrank k L = 4 := by simpa using finrank_eq_card_basis b
  obtain ⟨e⟩ := exists_four_embeddings (K := K) hL
  have hspan := conjugate_basis_span b e
  have hdim' : 3 ≤ Module.finrank k (affineJetQuadrics (k := k)
      (fun i : Fin 3 => b i.succ)
      (fun i : Fin 3 => (Fin.cons (0 : L) v : Fin 4 → L) i.succ)) := by
    have htail : (fun i : Fin 3 => (Fin.cons (0 : L) v : Fin 4 → L) i.succ) = v := by
      funext i
      simp
    rw [htail]
    exact hdim
  obtain ⟨l, hl, hskew⟩ := conjugate_skew_normalization_from_ground_jets
    e b (Fin.cons 0 v) hb (by rfl) hspan hdim'
  exact ⟨e, v, hF, hv, hsurj, hclosed, hlen, l, hl, hskew⟩

/-- The skew-normalized tangent-net construction, retaining the lower bound
on the space of quadrics through the selected ground-field jet. -/
theorem affine_length_eight_skew_tangent_construction_with_quadric_dimension
    {k L K : Type u} [Field k] [Field L] [Field K] [Algebra k L] [Algebra k K]
    [IsAlgClosed K] [Normal k K] [Infinite K]
    [FiniteDimensional k L] [Algebra.IsSeparable k L]
    (b : Basis (Fin 4) k L) (hb : b 0 = 1) (F : AffineThreeRing k)
    (hp : MvPolynomial.aeval (fun i : Fin 3 => b i.succ) F = 0)
    (hsmooth : affineDifferential (fun i : Fin 3 => b i.succ) F ≠ 0) :
    ∃ (e : Fin 4 ≃ (L →ₐ[k] K)) (v : Fin 3 → L)
      (hF : affineFirstJet (fun i : Fin 3 => b i.succ) v F = 0),
      v ≠ 0 ∧
      Function.Surjective (affineHypersurfaceJet (fun i : Fin 3 => b i.succ) v F hF) ∧
      IsClosedImmersion
        (Spec.map (CommRingCat.ofHom
          (affineHypersurfaceJet (fun i : Fin 3 => b i.succ) v F hF).toRingHom)) ∧
      Module.finrank k (DualNumber L) = 8 ∧
      3 ≤ Module.finrank k (affineJetQuadrics (k := k)
        (fun i : Fin 3 => b i.succ) v) ∧
      ∃ l : Fin 4 → K, (∀ i, l i ≠ 0) ∧ ∀ i j,
        l i * conjugateTangentMatrix e b (Fin.cons 0 v)
          (conjugate_basis_span b e) i j =
          -(l j * conjugateTangentMatrix e b (Fin.cons 0 v)
            (conjugate_basis_span b e) j i) := by
  obtain ⟨v, hF, hv, hsurj, hclosed, hlen, hdim, _⟩ :=
    affine_length_eight_construction_geometrically_split (K := K) b hb F hp hsmooth
  have hL : Module.finrank k L = 4 := by simpa using finrank_eq_card_basis b
  obtain ⟨e⟩ := exists_four_embeddings (K := K) hL
  have hspan := conjugate_basis_span b e
  have hdim' : 3 ≤ Module.finrank k (affineJetQuadrics (k := k)
      (fun i : Fin 3 => b i.succ)
      (fun i : Fin 3 => (Fin.cons (0 : L) v : Fin 4 → L) i.succ)) := by
    have htail : (fun i : Fin 3 => (Fin.cons (0 : L) v : Fin 4 → L) i.succ) = v := by
      funext i
      simp
    rw [htail]
    exact hdim
  obtain ⟨l, hl, hskew⟩ := conjugate_skew_normalization_from_ground_jets
    e b (Fin.cons 0 v) hb (by rfl) hspan hdim'
  exact ⟨e, v, hF, hv, hsurj, hclosed, hlen, hdim, l, hl, hskew⟩

end QuarticNet
end PfaffianDescent
