import PfaffianDescent.ActualMatchingProjectorGaloisPair
import PfaffianDescent.IdempotentTwoKernelFrame
import PfaffianDescent.MatchingComplementProjectiveLineGeometry
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.OrderOfElement

/-! SOURCE ONLY / UNVERIFIED. A nonidentity automorphism of the SAME actual
quadratic E exchanges its two projectors. Transitivity of original quartic
conjugates, not a supplied interchange certificate, produces the automorphism. -/
noncomputable section
namespace PfaffianDescent.QuarticNet
open Module
universe u
variable {k L K : Type u} [Field k] [Field L] [Field K]
  [Algebra k L] [Algebra k K] [IsGalois k K]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem matchingEdgeProjectorMatrix_ne_complement
    (B : Basis (Fin 4) K (Fin 4 → K)) :
    matchingEdgeProjectorMatrix B ≠ 1 - matchingEdgeProjectorMatrix B := by
  intro h
  have hLeft : (matchingEdgeProjectorMatrix B).mulVec (B 0) = B 0 := by
    simpa using matchingEdgeProjectorMatrix_mulVec_basis B 0
  have hRight : (1 - matchingEdgeProjectorMatrix B).mulVec (B 0) = 0 := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, hLeft, sub_self]
  have hz : B 0 = 0 := by
    calc
      B 0 = (matchingEdgeProjectorMatrix B).mulVec (B 0) := hLeft.symm
      _ = (1 - matchingEdgeProjectorMatrix B).mulVec (B 0) :=
        congrArg (fun P => P.mulVec (B 0)) h
      _ = 0 := hRight
  exact B.linearIndependent.ne_zero 0 hz

/-- The actual quartic action has an element carrying the first edge to the
second. Its full projector equality is proved coefficient by coefficient. -/
theorem actualMatching_projector_exists_exchanging_automorphism
    (full : Fin 4 ≃ (L →ₐ[k] K)) (p v : Fin 4 → L)
    (hs : Submodule.span K (Set.range (fun sigma : L →ₐ[k] K =>
      fun m => sigma (p m))) = ⊤)
    (l : Fin 4 → K) (hl : ∀ r, l r ≠ 0) (pi : Equiv.Perm (Fin 4))
    (a f : K) (ha : a ≠ 0)
    (hU : tangentRelabel (rescaleTangentDirections l
      (conjugateTangentMatrix full p v hs)) pi =
        skewTangentDirections a 0 0 0 0 f) :
    let B := (conjugateBasis full p hs).reindex pi.symm
    ∃ g : K ≃ₐ[k] K,
      (matchingEdgeProjectorMatrix B).map g.toRingHom =
        1 - matchingEdgeProjectorMatrix B := by
  classical
  dsimp only
  let B := (conjugateBasis full p hs).reindex pi.symm
  obtain ⟨g, hg⟩ := indexedEmbeddingAction_transitive full (pi 0) (pi 2)
  let rho := pi.trans ((indexedEmbeddingAction full g).trans pi.symm)
  have hpi (r : Fin 4) : pi (rho r) = indexedEmbeddingAction full g (pi r) := by
    simp only [rho, Equiv.trans_apply, Equiv.apply_symm_apply]
  have hRho0 : rho 0 = 2 := by
    apply pi.injective
    rw [hpi, hg]
  have hB (r m : Fin 4) : g (B r m) = B (rho r) m := by
    simp only [B, Basis.reindex_apply, Equiv.symm_symm, conjugateBasis_apply, hpi]
    exact (indexedEmbeddingAction_apply full g (pi r) (p m)).symm
  have hEdge : skewTangentDirections a 0 0 0 0 f (rho 0) (rho 1) ≠ 0 := by
    have hRaw : conjugateTangentMatrix full p v hs (pi 0) (pi 1) ≠ 0 := by
      have hNonzero : tangentRelabel (rescaleTangentDirections l
          (conjugateTangentMatrix full p v hs)) pi 0 1 ≠ 0 := by
        rw [hU]
        exact ha
      change l (pi 0) * conjugateTangentMatrix full p v hs (pi 0) (pi 1) ≠ 0
        at hNonzero
      exact (mul_ne_zero_iff.mp hNonzero).2
    have hTarget : conjugateTangentMatrix full p v hs
        (indexedEmbeddingAction full g (pi 0))
        (indexedEmbeddingAction full g (pi 1)) ≠ 0 := by
      rw [← conjugateTangentMatrix_covariance full p v hs g]
      exact fun hz => hRaw (g.injective (hz.trans (map_zero g).symm))
    have hScaled : tangentRelabel (rescaleTangentDirections l
        (conjugateTangentMatrix full p v hs)) pi (rho 0) (rho 1) ≠ 0 := by
      change l (pi (rho 0)) *
        conjugateTangentMatrix full p v hs (pi (rho 0)) (pi (rho 1)) ≠ 0
      apply mul_ne_zero (hl _)
      simpa only [hpi] using hTarget
    simpa only [hU] using hScaled
  have hRho1 : rho 1 = 3 := by
    rcases matching_edge_cases a f (rho 0) (rho 1) hEdge with h | h | h | h
    · have hz : (2 : Fin 4) = 0 := hRho0.symm.trans h.1
      exact False.elim ((by decide : (2 : Fin 4) ≠ 0) hz)
    · have hz : (2 : Fin 4) = 1 := hRho0.symm.trans h.1
      exact False.elim ((by decide : (2 : Fin 4) ≠ 1) hz)
    · exact h.2
    · have hz : (2 : Fin 4) = 3 := hRho0.symm.trans h.1
      exact False.elim ((by decide : (2 : Fin 4) ≠ 3) hz)
  have hr (n i : Fin 4) : g (B.repr (Pi.single n 1) i) =
      B.repr (Pi.single n 1) (rho i) := by
    have hstd : (fun j : Fin 4 => g ((Pi.single n (1 : K) : Fin 4 → K) j)) =
        Pi.single n 1 := by
      funext j
      by_cases h : n = j <;> simp [Pi.single_apply, h]
    simpa only [hstd] using
      (permutedBasis_repr_covariance B g rho hB (Pi.single n 1) i).symm
  refine ⟨g, ?_⟩
  ext m n
  rw [matchingEdgeProjectorMatrix_complement_entry]
  change g (B 0 m * B.repr (Pi.single n 1) 0 +
    B 1 m * B.repr (Pi.single n 1) 1) =
      B 2 m * B.repr (Pi.single n 1) 2 + B 3 m * B.repr (Pi.single n 1) 3
  rw [map_add, map_mul, map_mul, hB, hB, hr, hr]
  simp only [hRho0, hRho1]

/-- Restrict that internally constructed automorphism to SAME E. It is
nonidentity, has square1, and acts on the WHOLE first line ideal by exchange. -/
theorem actualMatching_quadratic_projector_exchange
    (full : Fin 4 ≃ (L →ₐ[k] K)) (p v : Fin 4 → L)
    (hs : Submodule.span K (Set.range (fun sigma : L →ₐ[k] K =>
      fun m => sigma (p m))) = ⊤)
    (l : Fin 4 → K) (hl : ∀ r, l r ≠ 0) (pi : Equiv.Perm (Fin 4))
    (a f : K) (ha : a ≠ 0)
    (hU : tangentRelabel (rescaleTangentDirections l
      (conjugateTangentMatrix full p v hs)) pi =
        skewTangentDirections a 0 0 0 0 f)
    (E : IntermediateField k K) [FiniteDimensional k E] [IsGalois k E]
    (hdeg : finrank k E = 2) (P : Matrix (Fin 4) (Fin 4) E)
    (hP : P.map E.val.toRingHom =
      matchingEdgeProjectorMatrix ((conjugateBasis full p hs).reindex pi.symm)) :
    ∃ sigma : E ≃ₐ[k] E, sigma ≠ 1 ∧ sigma ^ 2 = 1 ∧
      P.map sigma.toRingHom = 1 - P ∧
      (projectorLineIdeal P).toIdeal.map (MvPolynomial.map sigma.toRingHom) =
        (projectorLineIdeal (1 - P)).toIdeal ∧
      (projectorLineIdeal (1 - P)).toIdeal.map (MvPolynomial.map sigma.toRingHom) =
        (projectorLineIdeal P).toIdeal := by
  let B := (conjugateBasis full p hs).reindex pi.symm
  obtain ⟨g, hg⟩ :=
    actualMatching_projector_exists_exchanging_automorphism full p v hs l hl pi a f ha hU
  let sigma := AlgEquiv.restrictNormalHom E g
  have hLift (z : E) : E.val (sigma z) = g (E.val z) :=
    AlgEquiv.restrictNormal_commutes g E z
  have hExchange : P.map sigma.toRingHom = 1 - P := by
    apply Matrix.ext
    intro m n
    apply E.val.injective
    change E.val (sigma (P m n)) = E.val ((1 - P) m n)
    rw [hLift]
    have hm := congrFun (congrFun hg m) n
    rw [← hP] at hm
    by_cases hmn : m = n <;>
      simpa [Matrix.map_apply, Matrix.sub_apply, Matrix.one_apply, hmn] using hm
  have hNe : sigma ≠ 1 := by
    intro h
    have hid : P.map sigma.toRingHom = P := by
      apply Matrix.ext
      intro m n
      change sigma (P m n) = P m n
      rw [h]
      rfl
    have he : P = 1 - P := hid.symm.trans hExchange
    apply matchingEdgeProjectorMatrix_ne_complement B
    have heMap := congrArg (fun Q => Q.map E.val.toRingHom) he
    have hComp : (1 - P).map E.val.toRingHom = 1 - P.map E.val.toRingHom :=
      matchingSideProjector_map E.val.toRingHom P true
    rw [hComp, hP] at heMap
    exact heMap
  have hSquare : sigma ^ 2 = 1 := by
    have hc : Nat.card (E ≃ₐ[k] E) = 2 := (IsGalois.card_aut_eq_finrank k E).trans hdeg
    simpa only [hc] using (pow_card_eq_one' (x := sigma))
  have hComplement : (1 - P).map sigma.toRingHom = P := by
    calc
      (1 - P).map sigma.toRingHom = 1 - P.map sigma.toRingHom :=
        matchingSideProjector_map sigma.toRingHom P true
      _ = 1 - (1 - P) := by rw [hExchange]
      _ = P := by abel
  refine ⟨sigma, hNe, hSquare, hExchange, ?_, ?_⟩
  · rw [projectorLineIdeal_baseChange, hExchange]
  · rw [projectorLineIdeal_baseChange, hComplement]

end PfaffianDescent.QuarticNet
