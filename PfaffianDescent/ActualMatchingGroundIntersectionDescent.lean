import PfaffianDescent.IntermediateMatchingProjectorPair
import PfaffianDescent.QuadraticGaloisStableIdealDescent
import PfaffianDescent.ActualMatchingProjectorCoefficientField
import AllCharacteristics.HomogeneousProjectiveAmbient

/-! SOURCE ONLY, UNVERIFIED. Construct a GROUND homogeneous ideal whose
extension to the SAME derived quadratic E is exactly the INTERSECTION of
the two E-line projector ideals. No graph/action/ideal-descent certificate
is a public input. The further E-to-K intersection comparison is separate. -/
noncomputable section
namespace PfaffianDescent.QuarticNet
open Module MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u
variable {k L K : Type u} [Field k] [Field L] [Field K]
  [Algebra k L] [Algebra k K] [IsGalois k K]
attribute [local instance] MvPolynomial.gradedAlgebra


theorem actualMatching_original_intersection_galois_stable
    (full : Fin 4 ≃ (L →ₐ[k] K)) (p v : Fin 4 → L)
    (hs : Submodule.span K (Set.range (fun sigma : L →ₐ[k] K =>
      fun m => sigma (p m))) = ⊤)
    (l : Fin 4 → K) (hl : ∀ r, l r ≠ 0) (pi : Equiv.Perm (Fin 4))
    (a f : K) (ha : a ≠ 0)
    (hU : tangentRelabel (rescaleTangentDirections l
      (conjugateTangentMatrix full p v hs)) pi =
        skewTangentDirections a 0 0 0 0 f) :
    let B := (conjugateBasis full p hs).reindex pi.symm
    ∀ g : K ≃ₐ[k] K,
      (matchingProjectorIntersectionIdeal (matchingEdgeProjectorMatrix B)).toIdeal.map
        (MvPolynomial.map g.toRingHom) =
      (matchingProjectorIntersectionIdeal (matchingEdgeProjectorMatrix B)).toIdeal := by
  dsimp only
  intro g
  exact matchingProjectorIntersectionIdeal_map_galois_pair _ g
    (actualMatching_projector_galois_pair full p v hs l hl pi a f ha hU g)

theorem actualMatching_ground_intersection_descent
    (full : Fin 4 ≃ (L →ₐ[k] K)) (p v : Fin 4 → L)
    (hs : Submodule.span K (Set.range (fun sigma : L →ₐ[k] K =>
      fun m => sigma (p m))) = ⊤)
    (l : Fin 4 → K) (hl : ∀ r, l r ≠ 0) (pi : Equiv.Perm (Fin 4))
    (a f : K) (ha : a ≠ 0)
    (hU : tangentRelabel (rescaleTangentDirections l
      (conjugateTangentMatrix full p v hs)) pi =
        skewTangentDirections a 0 0 0 0 f) :
    let B := (conjugateBasis full p hs).reindex pi.symm
    ∃ E : IntermediateField k K, ∃ _ : FiniteDimensional k E,
      finrank k E = 2 ∧ IsGalois k E ∧
      E = IntermediateField.adjoin k (Set.range (fun m => B 0 m + B 1 m)) ∧
      ∃ P : Matrix (Fin 4) (Fin 4) E,
        P.map E.val.toRingHom = matchingEdgeProjectorMatrix B ∧
        ∃ J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) k),
          J.toIdeal.map (MvPolynomial.map (algebraMap k E)) =
            (projectorLineIdeal P).toIdeal ⊓ (projectorLineIdeal (1 - P)).toIdeal := by
  classical
  dsimp only
  let B := (conjugateBasis full p hs).reindex pi.symm
  obtain ⟨E, hFD, hdeg, hGal, hE, P, hP⟩ :=
    actualMatching_projector_quadratic_field full p v hs l hl pi a f ha hU
  letI : FiniteDimensional k E := hFD
  letI : IsGalois k E := hGal
  have hPairK : ∀ g : K ≃ₐ[k] K,
      (P.map E.val.toRingHom).map g.toRingHom = P.map E.val.toRingHom ∨
      (P.map E.val.toRingHom).map g.toRingHom = 1 - P.map E.val.toRingHom := by
    rw [hP]
    exact actualMatching_projector_galois_pair full p v hs l hl pi a f ha hU
  have hPairE (sigma : E ≃ₐ[k] E) :
      P.map sigma.toRingHom = P ∨ P.map sigma.toRingHom = 1 - P :=
    intermediateMatchingProjector_galois_pair E P hPairK sigma
  let I := matchingProjectorIntersectionIdeal P
  have hStable : ∀ sigma : E ≃ₐ[k] E, ∀ q ∈ I.toIdeal,
      MvPolynomial.map sigma.toRingHom q ∈ I.toIdeal := by
    intro sigma q hq
    rw [← matchingProjectorIntersectionIdeal_map_galois_pair P sigma (hPairE sigma)]
    exact Ideal.mem_map_of_mem _ hq
  let J := I.comap (ambientCoefficientGradedRingHom (algebraMap k E))
  refine ⟨E, hFD, hdeg, hGal, hE, P, hP, J, ?_⟩
  change (I.toIdeal.comap (MvPolynomial.map (algebraMap k E))).map
      (MvPolynomial.map (algebraMap k E)) = I.toIdeal
  exact quadratic_galois_stable_polynomial_ideal_descends hdeg I.toIdeal hStable

end PfaffianDescent.QuarticNet
