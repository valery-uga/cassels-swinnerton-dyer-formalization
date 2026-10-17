import PfaffianDescent.QuarticFiniteNetDescent
import PfaffianDescent.QuarticFourCycleNetDescent
import PfaffianDescent.QuarticTangentRescaling
import PfaffianDescent.QuarticJetNet
import PfaffianDescent.QuarticGaloisMatching
import PfaffianDescent.QuarticSkewTangentSupport
import PfaffianDescent.QuarticExceptionalBaseLocus
import PfaffianDescent.QuarticExceptionalTangentParam

/-!
# Finite branches of a geometric tangent net

These two results transport the normalized full-support and four-cycle
calculations through the coordinates of four geometric conjugate points.
They leave only the matching and exceptional twisted-cubic branches for the
final Section 4 assembly.
-/

namespace PfaffianDescent
namespace QuarticNet

open MvPolynomial Module

universe u

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

/-- The three-quadric ideal conclusion in a finite branch gives an explicit
nonzero ground-field cubic zero. -/
theorem cubic_point_of_mem_three_quadrics_range
    (Q : Fin 3 → MvPolynomial (Fin 4) k)
    (hQ : ∀ i, (Q i).IsHomogeneous 2)
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (hmem : F ∈ Ideal.span (Set.range Q)) :
    ∃ x : Fin 4 → k, x ≠ 0 ∧ MvPolynomial.eval x F = 0 := by
  have hset : Set.range Q = {Q 0, Q 1, Q 2} := by
    ext q
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rintro (h | h | h)
      · exact ⟨0, h.symm⟩
      · exact ⟨1, h.symm⟩
      · exact ⟨2, h.symm⟩
  apply cubic_has_nonzero_zero_of_mem_three_quadrics F (Q 0) (Q 1) (Q 2) hF
  · exact hQ 0
  · exact hQ 1
  · exact hQ 2
  · rwa [← hset]

/-- In the exceptional full-support case, three independent ground-field
quadrics through the geometric tangent jets become exactly the ideal of the
explicit exceptional twisted cubic after passing to the conjugate coordinates. -/
theorem exceptional_ground_quadric_ideal_eq_param_ker
    (Q : Fin 3 → MvPolynomial (Fin 4) k)
    (hQ : ∀ i, (Q i).IsHomogeneous 2) (hQI : LinearIndependent k Q)
    (B : Basis (Fin 4) K (Fin 4 → K)) (U : Fin 4 → Fin 4 → K)
    (hdiag : ∀ i, U i i = 0) (hskew : ∀ i j, U i j = -U j i)
    (hfull : ∀ i j, i ≠ j → U i j ≠ 0)
    (hdelta : baseLocusDelta (U 0 1) (U 0 2) (U 0 3)
      (U 1 2) (U 1 3) (U 2 3) = 0)
    (hQvan : ∀ i : Fin 3, ∀ r : Fin 4,
      aeval (tangentDualPoint U r)
        (linearSubstitution (basisCoordinateMatrix B) (map (algebraMap k K) (Q i))) = 0) :
    Ideal.span (Set.range (fun i => linearSubstitution (basisCoordinateMatrix B)
      (map (algebraMap k K) (Q i)))) =
      RingHom.ker (exceptionalTwistedCubicParam (U 0 1) (U 0 2) (U 0 3)
        (U 1 2) (U 1 3)).toRingHom := by
  let G : Fin 3 → MvPolynomial (Fin 4) K :=
    fun i => linearSubstitution (basisCoordinateMatrix B) (map (algebraMap k K) (Q i))
  have hG : ∀ i, (G i).IsHomogeneous 2 :=
    fun i => linearSubstitution_homogeneous (basisCoordinateMatrix B)
      ((hQ i).map (algebraMap k K))
  have hGI : LinearIndependent K G :=
    (polynomial_linearIndependent_map Q hQI).map'
      (linearSubstitutionEquiv (basisCoordinateMatrix B) (basisCoordinateMatrix_isUnit B)).toLinearEquiv.toLinearMap
      (LinearMap.ker_eq_bot.mpr
        (linearSubstitutionEquiv (basisCoordinateMatrix B) (basisCoordinateMatrix_isUnit B)).injective)
  have hU : U = skewTangentDirections (U 0 1) (U 0 2) (U 0 3)
      (U 1 2) (U 1 3) (U 2 3) :=
    skew_matrix_eq_parameters U hdiag hskew
  have hmem (i : Fin 3) : G i ∈ Ideal.span
      (Set.range (scaledBaseLocusQuadricPolynomials
        (U 0 1) (U 0 2) (U 0 3) (U 1 2) (U 1 3) (U 2 3))) :=
    homogeneous_tangent_quadric_mem_scaledBaseLocus_ideal
      (U 0 1) (U 0 2) (U 0 3) (U 1 2) (U 1 3) (U 2 3)
      (hfull 0 1 (by decide)) (hfull 0 2 (by decide)) (hfull 0 3 (by decide))
      (G i) (hG i) (by simpa only [← hU] using hQvan i)
  have hspan : Ideal.span (Set.range G) = Ideal.span
      (Set.range (scaledBaseLocusQuadricPolynomials
        (U 0 1) (U 0 2) (U 0 3) (U 1 2) (U 1 3) (U 2 3))) :=
    quadric_ideal_eq_of_independent G
      (scaledBaseLocusQuadricPolynomials
        (U 0 1) (U 0 2) (U 0 3) (U 1 2) (U 1 3) (U 2 3)) hG
      (scaledBaseLocusQuadricPolynomials_homogeneous
        (U 0 1) (U 0 2) (U 0 3) (U 1 2) (U 1 3) (U 2 3)) hmem hGI
  change Ideal.span (Set.range G) = _
  exact hspan.trans (exceptionalTwistedCubic_ideal_eq_param_ker
    (U 0 1) (U 0 2) (U 0 3) (U 1 2) (U 1 3) (U 2 3)
    (hfull 0 1 (by decide)) (hfull 0 2 (by decide)) (hfull 0 3 (by decide))
    (hfull 1 2 (by decide)) (hfull 1 3 (by decide)) hdelta)

/-- A full-support skew tangent net over the splitting field descends its
cubic ideal membership to the three ground-field quadrics. -/
theorem cubic_mem_ground_ideal_of_full_support_skew_geometric_net
    (Q : Fin 3 → MvPolynomial (Fin 4) k)
    (hQ : ∀ i, (Q i).IsHomogeneous 2) (hQI : LinearIndependent k Q)
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (B : Basis (Fin 4) K (Fin 4 → K))
    (U : Fin 4 → Fin 4 → K)
    (hdiag : ∀ i, U i i = 0) (hskew : ∀ i j, U i j = -U j i)
    (hfull : ∀ i j, i ≠ j → U i j ≠ 0)
    (hdelta : baseLocusDelta (U 0 1) (U 0 2) (U 0 3)
      (U 1 2) (U 1 3) (U 2 3) ≠ 0)
    (hQvan : ∀ i : Fin 3, ∀ r : Fin 4,
      aeval (tangentDualPoint U r)
        (linearSubstitution (basisCoordinateMatrix B) (map (algebraMap k K) (Q i))) = 0)
    (hFvan : ∀ r : Fin 4,
      aeval (tangentDualPoint U r)
        (linearSubstitution (basisCoordinateMatrix B) (map (algebraMap k K) F)) = 0) :
    F ∈ Ideal.span (Set.range Q) := by
  have heq := skew_matrix_eq_parameters U hdiag hskew
  apply cubic_mem_ground_ideal_of_full_support_geometric_net Q hQ hQI F hF
    (basisCoordinateMatrix B) (basisCoordinateMatrix_isUnit B)
    (U 0 1) (U 0 2) (U 0 3) (U 1 2) (U 1 3) (U 2 3)
    (hfull 0 1 (by decide)) (hfull 0 2 (by decide)) (hfull 0 3 (by decide))
    (hfull 1 2 (by decide)) (hfull 1 3 (by decide)) (hfull 2 3 (by decide)) hdelta
  · simpa only [← heq] using hQvan
  · simpa only [← heq] using hFvan

/-- A four-cycle skew tangent net over the splitting field descends its
cubic ideal membership to the three ground-field quadrics. -/
theorem cubic_mem_ground_ideal_of_fourCycle_skew_geometric_net
    (Q : Fin 3 → MvPolynomial (Fin 4) k)
    (hQ : ∀ i, (Q i).IsHomogeneous 2) (hQI : LinearIndependent k Q)
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (B : Basis (Fin 4) K (Fin 4 → K))
    (U : Fin 4 → Fin 4 → K)
    (hdiag : ∀ i, U i i = 0) (hskew : ∀ i j, U i j = -U j i)
    (hcycle : matchingPattern (!(nonzeroEdge (U 0 1))) (!(nonzeroEdge (U 0 2)))
      (!(nonzeroEdge (U 0 3))) (!(nonzeroEdge (U 1 2)))
      (!(nonzeroEdge (U 1 3))) (!(nonzeroEdge (U 2 3))))
    (hQvan : ∀ i : Fin 3, ∀ r : Fin 4,
      aeval (tangentDualPoint U r)
        (linearSubstitution (basisCoordinateMatrix B) (map (algebraMap k K) (Q i))) = 0)
    (hFvan : ∀ r : Fin 4,
      aeval (tangentDualPoint U r)
        (linearSubstitution (basisCoordinateMatrix B) (map (algebraMap k K) F)) = 0) :
    F ∈ Ideal.span (Set.range Q) := by
  obtain ⟨π, h01, h23, h02, h03, h12, h13⟩ := fourCycle_relabel U hskew hcycle
  let V := tangentRelabel U π
  have hdiagV : ∀ i, V i i = 0 := fun i => hdiag (π i)
  have hskewV : ∀ i j, V i j = -V j i := fun i j => hskew (π i) (π j)
  have heq : V = skewTangentDirections 0 (V 0 2) (V 0 3) (V 1 2) (V 1 3) 0 := by
    simpa only [V, h01, h23] using skew_matrix_eq_parameters V hdiagV hskewV
  apply cubic_mem_ground_ideal_of_fourCycle_geometric_net Q hQ hQI F hF
    (basisCoordinateMatrix (B.reindex π.symm)) (basisCoordinateMatrix_isUnit _)
    (V 0 2) (V 0 3) (V 1 2) (V 1 3) h02 h03 h12 h13
  · intro i r
    have h := tangentRelabel_vanishing B U π (map (algebraMap k K) (Q i)) (hQvan i) r
    simpa only [← heq] using h
  · intro r
    have h := tangentRelabel_vanishing B U π (map (algebraMap k K) F) hFvan r
    simpa only [← heq] using h

/-- The matching branch descends its Galois-stable pair of contained lines
to a ground-field cubic point. -/
theorem cubic_point_of_matching_skew_geometric_net [IsGalois k K]
    (B : Basis (Fin 4) K (Fin 4 → K))
    (U : Fin 4 → Fin 4 → K)
    (hdiag : ∀ i, U i i = 0) (hskew : ∀ i j, U i j = -U j i)
    (hmatch : matchingPattern (nonzeroEdge (U 0 1)) (nonzeroEdge (U 0 2))
      (nonzeroEdge (U 0 3)) (nonzeroEdge (U 1 2))
      (nonzeroEdge (U 1 3)) (nonzeroEdge (U 2 3)))
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (hvan : ∀ r : Fin 4,
      aeval (tangentDualPoint U r)
        (linearSubstitution (basisCoordinateMatrix B) (map (algebraMap k K) F)) = 0)
    (hact : ∀ g : K ≃ₐ[k] K, ∃ τ : Equiv.Perm (Fin 4),
      (∀ i m, g (B i m) = B (τ i) m) ∧
      (∀ i j, U i j ≠ 0 ↔ U (τ i) (τ j) ≠ 0)) :
    ∃ p : Fin 4 → k, p ≠ 0 ∧ aeval p F = 0 := by
  obtain ⟨π, ha, hf, h02, h03, h12, h13⟩ := matching_relabel U hskew hmatch
  let V := tangentRelabel U π
  have hdiagV : ∀ i, V i i = 0 := fun i => hdiag (π i)
  have hskewV : ∀ i j, V i j = -V j i := fun i j => hskew (π i) (π j)
  have heq : V = skewTangentDirections (V 0 1) 0 0 0 0 (V 2 3) := by
    simpa only [V, h02, h03, h12, h13] using skew_matrix_eq_parameters V hdiagV hskewV
  apply cubic_point_from_galois_matching (B.reindex π.symm) (V 0 1) (V 2 3) ha F hF
  · have h := tangentRelabel_vanishing B U π (map (algebraMap k K) F) hvan
    simpa only [← heq] using h
  · intro g
    obtain ⟨τ, hB, hU⟩ := hact g
    let ρ : Equiv.Perm (Fin 4) := π.trans (τ.trans π.symm)
    have hπ (i : Fin 4) : π (ρ i) = τ (π i) := by simp [ρ]
    refine ⟨ρ, ?_, ?_⟩
    · intro i m
      simpa only [Basis.reindex_apply, Equiv.symm_symm, hπ] using hB (π i) m
    · intro i j
      rw [← heq]
      change U (π i) (π j) ≠ 0 ↔ U (π (ρ i)) (π (ρ j)) ≠ 0
      rw [hπ, hπ]
      exact hU (π i) (π j)

theorem cubic_point_of_matching_ground_jet [IsGalois k K]
    {L : Type u} [Field L] [Algebra k L]
    (e : Fin 4 ≃ (L →ₐ[k] K)) (p v : Fin 4 → L)
    (hspan : Submodule.span K (Set.range (fun σ : L →ₐ[k] K => fun i => σ (p i))) = ⊤)
    (l : Fin 4 → K) (hl : ∀ i, l i ≠ 0)
    (hskew : ∀ i j, l i * conjugateTangentMatrix e p v hspan i j =
      -(l j * conjugateTangentMatrix e p v hspan j i))
    (hmatch : matchingPattern
      (nonzeroEdge (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 0 1))
      (nonzeroEdge (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 0 2))
      (nonzeroEdge (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 0 3))
      (nonzeroEdge (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 1 2))
      (nonzeroEdge (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 1 3))
      (nonzeroEdge (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 2 3)))
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (hFjet : aeval (R := k) (S₁ := DualNumber L)
      (fun i => TrivSqZeroExt.inl (p i) + TrivSqZeroExt.inr (v i)) F = 0) :
    ∃ x : Fin 4 → k, x ≠ 0 ∧ aeval x F = 0 := by
  apply cubic_point_of_matching_skew_geometric_net (conjugateBasis e p hspan)
    (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan))
  · intro i
    simp [rescaleTangentDirections, conjugateTangentMatrix_diagonal]
  · simpa only [rescaleTangentDirections] using hskew
  · exact hmatch
  · exact hF
  · exact rescaleTangentDirections_vanishing _ l _ (fun r =>
      (homogeneous_jet_vanishes_on_conjugates e p v hspan F 3 hF hFjet) r)
  · intro g
    refine ⟨indexedEmbeddingAction e g, ?_, ?_⟩
    · intro i m
      simp only [conjugateBasis_apply, indexedEmbeddingAction_apply]
    · intro i j
      rw [rescaleTangentDirections_nonzero _ l hl,
        rescaleTangentDirections_nonzero _ l hl]
      rw [← conjugateTangentMatrix_covariance e p v hspan g i j, map_ne_zero]

/- The following two forms begin with the selected affine jet over the
degree-four residue field.  They construct the three ground-field quadrics,
transport their vanishing to all four conjugate tangent double points, and
then invoke the appropriate finite branch above. -/

theorem exists_three_quadrics_and_ground_ideal_of_full_support_ground_jet
    {L : Type u} [Field L] [Algebra k L]
    (e : Fin 4 ≃ (L →ₐ[k] K)) (p v : Fin 4 → L)
    (hp : p 0 = 1) (hv0 : v 0 = 0)
    (hspan : Submodule.span K (Set.range (fun σ : L →ₐ[k] K => fun i => σ (p i))) = ⊤)
    (hdim : 3 ≤ Module.finrank k (affineJetQuadrics (k := k)
      (fun i : Fin 3 => p i.succ) (fun i : Fin 3 => v i.succ)))
    (l : Fin 4 → K)
    (hskew : ∀ i j, l i * conjugateTangentMatrix e p v hspan i j =
      -(l j * conjugateTangentMatrix e p v hspan j i))
    (hfull : ∀ i j, i ≠ j →
      rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) i j ≠ 0)
    (hdelta : baseLocusDelta
      (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 0 1)
      (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 0 2)
      (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 0 3)
      (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 1 2)
      (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 1 3)
      (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 2 3) ≠ 0)
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (hFjet : aeval (R := k) (S₁ := DualNumber L)
      (fun i => TrivSqZeroExt.inl (p i) + TrivSqZeroExt.inr (v i)) F = 0) :
    ∃ Q : Fin 3 → MvPolynomial (Fin 4) k,
      LinearIndependent k Q ∧ (∀ i, (Q i).IsHomogeneous 2) ∧
        F ∈ Ideal.span (Set.range Q) := by
  obtain ⟨Q, hQI, hQ, hQjet⟩ := exists_three_ground_quadrics p v hp hv0 hdim
  refine ⟨Q, hQI, hQ, ?_⟩
  apply cubic_mem_ground_ideal_of_full_support_skew_geometric_net Q hQ hQI F hF
    (conjugateBasis e p hspan)
    (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan))
  · intro i
    simp [rescaleTangentDirections, conjugateTangentMatrix_diagonal]
  · simpa only [rescaleTangentDirections] using hskew
  · exact hfull
  · exact hdelta
  · intro i
    exact rescaleTangentDirections_vanishing _ l _ (fun r =>
      (homogeneous_jet_vanishes_on_conjugates e p v hspan (Q i) 2 (hQ i) (hQjet i)) r)
  · exact rescaleTangentDirections_vanishing _ l _ (fun r =>
      (homogeneous_jet_vanishes_on_conjugates e p v hspan F 3 hF hFjet) r)

theorem exists_three_quadrics_and_ground_ideal_of_fourCycle_ground_jet
    {L : Type u} [Field L] [Algebra k L]
    (e : Fin 4 ≃ (L →ₐ[k] K)) (p v : Fin 4 → L)
    (hp : p 0 = 1) (hv0 : v 0 = 0)
    (hspan : Submodule.span K (Set.range (fun σ : L →ₐ[k] K => fun i => σ (p i))) = ⊤)
    (hdim : 3 ≤ Module.finrank k (affineJetQuadrics (k := k)
      (fun i : Fin 3 => p i.succ) (fun i : Fin 3 => v i.succ)))
    (l : Fin 4 → K)
    (hskew : ∀ i j, l i * conjugateTangentMatrix e p v hspan i j =
      -(l j * conjugateTangentMatrix e p v hspan j i))
    (hcycle : matchingPattern
      (!(nonzeroEdge (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 0 1)))
      (!(nonzeroEdge (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 0 2)))
      (!(nonzeroEdge (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 0 3)))
      (!(nonzeroEdge (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 1 2)))
      (!(nonzeroEdge (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 1 3)))
      (!(nonzeroEdge (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 2 3))))
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (hFjet : aeval (R := k) (S₁ := DualNumber L)
      (fun i => TrivSqZeroExt.inl (p i) + TrivSqZeroExt.inr (v i)) F = 0) :
    ∃ Q : Fin 3 → MvPolynomial (Fin 4) k,
      LinearIndependent k Q ∧ (∀ i, (Q i).IsHomogeneous 2) ∧
        F ∈ Ideal.span (Set.range Q) := by
  obtain ⟨Q, hQI, hQ, hQjet⟩ := exists_three_ground_quadrics p v hp hv0 hdim
  refine ⟨Q, hQI, hQ, ?_⟩
  apply cubic_mem_ground_ideal_of_fourCycle_skew_geometric_net Q hQ hQI F hF
    (conjugateBasis e p hspan)
    (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan))
  · intro i
    simp [rescaleTangentDirections, conjugateTangentMatrix_diagonal]
  · simpa only [rescaleTangentDirections] using hskew
  · exact hcycle
  · intro i
    exact rescaleTangentDirections_vanishing _ l _ (fun r =>
      (homogeneous_jet_vanishes_on_conjugates e p v hspan (Q i) 2 (hQ i) (hQjet i)) r)
  · exact rescaleTangentDirections_vanishing _ l _ (fun r =>
      (homogeneous_jet_vanishes_on_conjugates e p v hspan F 3 hF hFjet) r)

/-- In the exceptional branch of a ground jet, the selected three
ground-field quadrics become the defining ideal of the explicit twisted cubic
in conjugate coordinates. -/
theorem exists_three_quadrics_with_exceptional_param_ideal_of_ground_jet
    {L : Type u} [Field L] [Algebra k L]
    (e : Fin 4 ≃ (L →ₐ[k] K)) (p v : Fin 4 → L)
    (hp : p 0 = 1) (hv0 : v 0 = 0)
    (hspan : Submodule.span K (Set.range (fun σ : L →ₐ[k] K => fun i => σ (p i))) = ⊤)
    (hdim : 3 ≤ Module.finrank k (affineJetQuadrics (k := k)
      (fun i : Fin 3 => p i.succ) (fun i : Fin 3 => v i.succ)))
    (l : Fin 4 → K)
    (hskew : ∀ i j, l i * conjugateTangentMatrix e p v hspan i j =
      -(l j * conjugateTangentMatrix e p v hspan j i))
    (hfull : ∀ i j, i ≠ j →
      rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) i j ≠ 0)
    (hdelta : baseLocusDelta
      (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 0 1)
      (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 0 2)
      (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 0 3)
      (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 1 2)
      (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 1 3)
      (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 2 3) = 0) :
    ∃ Q : Fin 3 → MvPolynomial (Fin 4) k,
      LinearIndependent k Q ∧ (∀ i, (Q i).IsHomogeneous 2) ∧
      Ideal.span (Set.range (fun i =>
        linearSubstitution (basisCoordinateMatrix (conjugateBasis e p hspan))
          (map (algebraMap k K) (Q i)))) =
        RingHom.ker (exceptionalTwistedCubicParam
          (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 0 1)
          (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 0 2)
          (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 0 3)
          (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 1 2)
          (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 1 3)).toRingHom := by
  obtain ⟨Q, hQI, hQ, hQjet⟩ := exists_three_ground_quadrics p v hp hv0 hdim
  refine ⟨Q, hQI, hQ, ?_⟩
  let U := rescaleTangentDirections l (conjugateTangentMatrix e p v hspan)
  have hdiag : ∀ i, U i i = 0 := by
    intro i
    simp [U, rescaleTangentDirections, conjugateTangentMatrix_diagonal]
  have hskewU : ∀ i j, U i j = -U j i := by
    simpa only [U, rescaleTangentDirections] using hskew
  apply exceptional_ground_quadric_ideal_eq_param_ker Q hQ hQI
    (conjugateBasis e p hspan) U hdiag hskewU
  · exact hfull
  · exact hdelta
  · intro i
    exact rescaleTangentDirections_vanishing _ l _ (fun r =>
      (homogeneous_jet_vanishes_on_conjugates e p v hspan (Q i) 2 (hQ i) (hQjet i)) r)

/-- In the exceptional branch, if the transformed ground cubic contains the
explicit twisted cubic, then its membership in the three descended quadratic
generators gives a ground-field cubic point.  This disposes of the
``base curve lies on the surface'' alternative without needing a separate
descent theorem identifying that curve with `P¹` over the ground field. -/
theorem cubic_point_of_exceptional_ground_jet_of_mem_param
    {L : Type u} [Field L] [Algebra k L]
    (e : Fin 4 ≃ (L →ₐ[k] K)) (p v : Fin 4 → L)
    (hp : p 0 = 1) (hv0 : v 0 = 0)
    (hspan : Submodule.span K (Set.range (fun σ : L →ₐ[k] K => fun i => σ (p i))) = ⊤)
    (hdim : 3 ≤ Module.finrank k (affineJetQuadrics (k := k)
      (fun i : Fin 3 => p i.succ) (fun i : Fin 3 => v i.succ)))
    (l : Fin 4 → K)
    (hskew : ∀ i j, l i * conjugateTangentMatrix e p v hspan i j =
      -(l j * conjugateTangentMatrix e p v hspan j i))
    (hfull : ∀ i j, i ≠ j →
      rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) i j ≠ 0)
    (hdelta : baseLocusDelta
      (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 0 1)
      (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 0 2)
      (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 0 3)
      (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 1 2)
      (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 1 3)
      (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 2 3) = 0)
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (hmem : linearSubstitution (basisCoordinateMatrix (conjugateBasis e p hspan))
      (map (algebraMap k K) F) ∈
        RingHom.ker (exceptionalTwistedCubicParam
          (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 0 1)
          (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 0 2)
          (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 0 3)
          (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 1 2)
          (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 1 3)).toRingHom) :
    ∃ x : Fin 4 → k, x ≠ 0 ∧ MvPolynomial.eval x F = 0 := by
  obtain ⟨Q, hQI, hQ, hideal⟩ :=
    exists_three_quadrics_with_exceptional_param_ideal_of_ground_jet
      e p v hp hv0 hspan hdim l hskew hfull hdelta
  apply cubic_point_of_mem_three_quadrics_range Q hQ F hF
  apply polynomial_mem_span_of_linearSubstitution_map_range_descends
    (basisCoordinateMatrix (conjugateBasis e p hspan))
    (basisCoordinateMatrix_isUnit (conjugateBasis e p hspan)) Q F
  rw [hideal]
  exact hmem

/-- The transformed cubic vanishes at each of the four binary dual points of
the explicit exceptional parametrization attached to a full-support ground
jet. -/
theorem exceptional_param_contains_ground_jet_tangent_net
    {L : Type u} [Field L] [Algebra k L]
    (e : Fin 4 ≃ (L →ₐ[k] K)) (p v : Fin 4 → L)
    (hspan : Submodule.span K (Set.range (fun σ : L →ₐ[k] K => fun i => σ (p i))) = ⊤)
    (l : Fin 4 → K)
    (hskew : ∀ i j, l i * conjugateTangentMatrix e p v hspan i j =
      -(l j * conjugateTangentMatrix e p v hspan j i))
    (hdelta : baseLocusDelta
      (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 0 1)
      (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 0 2)
      (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 0 3)
      (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 1 2)
      (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 1 3)
      (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 2 3) = 0)
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (hFjet : aeval (R := k) (S₁ := DualNumber L)
      (fun i => TrivSqZeroExt.inl (p i) + TrivSqZeroExt.inr (v i)) F = 0) :
    MvPolynomial.aeval ![(1 : DualNumber K), TrivSqZeroExt.inr
        (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 0 1)]
        (exceptionalTwistedCubicParam
          (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 0 1)
          (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 0 2)
          (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 0 3)
          (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 1 2)
          (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 1 3)
          (linearSubstitution (basisCoordinateMatrix (conjugateBasis e p hspan))
            (map (algebraMap k K) F))) = 0 ∧
      MvPolynomial.aeval ![TrivSqZeroExt.inr
        (-(rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 0 1)),
        (1 : DualNumber K)]
        (exceptionalTwistedCubicParam
          (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 0 1)
          (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 0 2)
          (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 0 3)
          (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 1 2)
          (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 1 3)
          (linearSubstitution (basisCoordinateMatrix (conjugateBasis e p hspan))
            (map (algebraMap k K) F))) = 0 ∧
      MvPolynomial.aeval ![TrivSqZeroExt.inl
        (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 0 2) +
          TrivSqZeroExt.inr
            (-(rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 0 2) ^ 2 *
              rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 1 2),
        TrivSqZeroExt.inl
          (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 1 2)]
        (exceptionalTwistedCubicParam
          (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 0 1)
          (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 0 2)
          (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 0 3)
          (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 1 2)
          (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 1 3)
          (linearSubstitution (basisCoordinateMatrix (conjugateBasis e p hspan))
            (map (algebraMap k K) F))) = 0 ∧
      MvPolynomial.aeval ![TrivSqZeroExt.inl
        (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 0 3) +
          TrivSqZeroExt.inr
            (-(rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 0 3) ^ 2 *
              rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 1 3),
        TrivSqZeroExt.inl
          (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 1 3)]
        (exceptionalTwistedCubicParam
          (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 0 1)
          (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 0 2)
          (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 0 3)
          (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 1 2)
          (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 1 3)
          (linearSubstitution (basisCoordinateMatrix (conjugateBasis e p hspan))
            (map (algebraMap k K) F))) = 0 := by
  let U := rescaleTangentDirections l (conjugateTangentMatrix e p v hspan)
  let G := linearSubstitution (basisCoordinateMatrix (conjugateBasis e p hspan))
    (map (algebraMap k K) F)
  have hdiag : ∀ i, U i i = 0 := by
    intro i
    simp [U, rescaleTangentDirections, conjugateTangentMatrix_diagonal]
  have hskewU : ∀ i j, U i j = -U j i := by
    simpa only [U, rescaleTangentDirections] using hskew
  have hU : U = skewTangentDirections (U 0 1) (U 0 2) (U 0 3)
      (U 1 2) (U 1 3) (U 2 3) := skew_matrix_eq_parameters U hdiag hskewU
  have hG : G.IsHomogeneous 3 :=
    linearSubstitution_homogeneous (basisCoordinateMatrix (conjugateBasis e p hspan))
      (hF.map (algebraMap k K))
  have hGvan : ∀ r : Fin 4, aeval (tangentDualPoint U r) G = 0 :=
    rescaleTangentDirections_vanishing _ l _ (fun r =>
      (homogeneous_jet_vanishes_on_conjugates e p v hspan F 3 hF hFjet) r)
  have htangent : ∀ r : Fin 4,
      aeval (tangentDualPoint (skewTangentDirections (U 0 1) (U 0 2) (U 0 3)
        (U 1 2) (U 1 3) (U 2 3)) r) G = 0 := by
    simpa only [← hU] using hGvan
  simpa [U, G, pow_two] using exceptional_param_contains_normalized_tangent_net
    (U 0 1) (U 0 2) (U 0 3) (U 1 2) (U 1 3) (U 2 3)
    (by simpa only [U] using hdelta) G hG htangent

/-- The finite full-support branch of a ground jet yields a nonzero
ground-field zero of the cubic. -/
theorem cubic_point_of_full_support_ground_jet
    {L : Type u} [Field L] [Algebra k L]
    (e : Fin 4 ≃ (L →ₐ[k] K)) (p v : Fin 4 → L)
    (hp : p 0 = 1) (hv0 : v 0 = 0)
    (hspan : Submodule.span K (Set.range (fun σ : L →ₐ[k] K => fun i => σ (p i))) = ⊤)
    (hdim : 3 ≤ Module.finrank k (affineJetQuadrics (k := k)
      (fun i : Fin 3 => p i.succ) (fun i : Fin 3 => v i.succ)))
    (l : Fin 4 → K)
    (hskew : ∀ i j, l i * conjugateTangentMatrix e p v hspan i j =
      -(l j * conjugateTangentMatrix e p v hspan j i))
    (hfull : ∀ i j, i ≠ j →
      rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) i j ≠ 0)
    (hdelta : baseLocusDelta
      (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 0 1)
      (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 0 2)
      (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 0 3)
      (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 1 2)
      (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 1 3)
      (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 2 3) ≠ 0)
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (hFjet : aeval (R := k) (S₁ := DualNumber L)
      (fun i => TrivSqZeroExt.inl (p i) + TrivSqZeroExt.inr (v i)) F = 0) :
    ∃ x : Fin 4 → k, x ≠ 0 ∧ aeval x F = 0 := by
  obtain ⟨Q, -, hQ, hmem⟩ :=
    exists_three_quadrics_and_ground_ideal_of_full_support_ground_jet
      e p v hp hv0 hspan hdim l hskew hfull hdelta F hF hFjet
  obtain ⟨x, hx, hFx⟩ := cubic_point_of_mem_three_quadrics_range Q hQ F hF hmem
  exact ⟨x, hx, hFx⟩

/-- The four-cycle branch of a ground jet yields a nonzero ground-field zero
of the cubic. -/
theorem cubic_point_of_fourCycle_ground_jet
    {L : Type u} [Field L] [Algebra k L]
    (e : Fin 4 ≃ (L →ₐ[k] K)) (p v : Fin 4 → L)
    (hp : p 0 = 1) (hv0 : v 0 = 0)
    (hspan : Submodule.span K (Set.range (fun σ : L →ₐ[k] K => fun i => σ (p i))) = ⊤)
    (hdim : 3 ≤ Module.finrank k (affineJetQuadrics (k := k)
      (fun i : Fin 3 => p i.succ) (fun i : Fin 3 => v i.succ)))
    (l : Fin 4 → K)
    (hskew : ∀ i j, l i * conjugateTangentMatrix e p v hspan i j =
      -(l j * conjugateTangentMatrix e p v hspan j i))
    (hcycle : matchingPattern
      (!(nonzeroEdge (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 0 1)))
      (!(nonzeroEdge (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 0 2)))
      (!(nonzeroEdge (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 0 3)))
      (!(nonzeroEdge (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 1 2)))
      (!(nonzeroEdge (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 1 3)))
      (!(nonzeroEdge (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 2 3))))
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (hFjet : aeval (R := k) (S₁ := DualNumber L)
      (fun i => TrivSqZeroExt.inl (p i) + TrivSqZeroExt.inr (v i)) F = 0) :
    ∃ x : Fin 4 → k, x ≠ 0 ∧ aeval x F = 0 := by
  obtain ⟨Q, -, hQ, hmem⟩ :=
    exists_three_quadrics_and_ground_ideal_of_fourCycle_ground_jet
      e p v hp hv0 hspan hdim l hskew hcycle F hF hFjet
  obtain ⟨x, hx, hFx⟩ := cubic_point_of_mem_three_quadrics_range Q hQ F hF hmem
  exact ⟨x, hx, hFx⟩

/-- A normalized Galois-conjugate tangent net gives a ground-field cubic point
unless it has full support and lies on the exceptional discriminant locus. -/
theorem cubic_point_or_exceptional_full_support_ground_jet
    [Normal k K] [Infinite K] [IsGalois k K]
    {L : Type u} [Field L] [Algebra k L]
    (e : Fin 4 ≃ (L →ₐ[k] K)) (p v : Fin 4 → L)
    (hp : p 0 = 1) (hv0 : v 0 = 0) (hv : v ≠ 0)
    (hspan : Submodule.span K (Set.range (fun σ : L →ₐ[k] K => fun i => σ (p i))) = ⊤)
    (hdim : 3 ≤ Module.finrank k (affineJetQuadrics (k := k)
      (fun i : Fin 3 => p i.succ) (fun i : Fin 3 => v i.succ)))
    (l : Fin 4 → K) (hl : ∀ i, l i ≠ 0)
    (hskew : ∀ i j, l i * conjugateTangentMatrix e p v hspan i j =
      -(l j * conjugateTangentMatrix e p v hspan j i))
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (hFjet : aeval (R := k) (S₁ := DualNumber L)
      (fun i => TrivSqZeroExt.inl (p i) + TrivSqZeroExt.inr (v i)) F = 0) :
    (∃ x : Fin 4 → k, x ≠ 0 ∧ aeval x F = 0) ∨
      ((∀ i j, i ≠ j →
        rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) i j ≠ 0) ∧
      baseLocusDelta
        (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 0 1)
        (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 0 2)
        (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 0 3)
        (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 1 2)
        (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 1 3)
        (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 2 3) = 0) := by
  have hclass :=
    conjugate_tangent_full_support_or_support_classification e p v hspan l hl hskew hp hv0 hv
  have hrescale (i j : Fin 4) :
      nonzeroEdge (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) i j) =
        nonzeroEdge (conjugateTangentMatrix e p v hspan i j) := by
    apply nonzeroEdge_congr
    simp [rescaleTangentDirections, hl i]
  obtain hfull | hmatch | hcycle := hclass
  · have hfull' : ∀ i j, i ≠ j →
      rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) i j ≠ 0 := by
      intro i j hij
      exact (rescaleTangentDirections_nonzero _ l hl i j).mpr (hfull i j hij)
    by_cases hdelta : baseLocusDelta
        (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 0 1)
        (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 0 2)
        (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 0 3)
        (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 1 2)
        (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 1 3)
        (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 2 3) = 0
    · exact Or.inr ⟨hfull', hdelta⟩
    · left
      exact cubic_point_of_full_support_ground_jet e p v hp hv0 hspan hdim l hskew hfull'
        hdelta F hF hFjet
  · left
    apply cubic_point_of_matching_ground_jet e p v hspan l hl hskew
    simpa only [hrescale 0 1, hrescale 0 2, hrescale 0 3,
      hrescale 1 2, hrescale 1 3, hrescale 2 3] using hmatch
    exact hF
    exact hFjet
  · left
    apply cubic_point_of_fourCycle_ground_jet e p v hp hv0 hspan hdim l hskew
    · simpa only [hrescale 0 1, hrescale 0 2, hrescale 0 3,
        hrescale 1 2, hrescale 1 3, hrescale 2 3] using hcycle
    · exact hF
    · exact hFjet

end QuarticNet
end PfaffianDescent
