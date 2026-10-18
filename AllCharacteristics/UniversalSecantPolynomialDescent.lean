import AllCharacteristics.UniversalSecantPolynomial
import PfaffianDescent.QuadraticConjugateDescent

namespace PfaffianDescent

open MvPolynomial Module
open scoped BigOperators

universe u v

/-- Mapping polynomial coefficients retains the universal tangent variables. -/
theorem map_universalTangentDirectionPolynomial
    {L E : Type u} [Field L] [Field E] (f : L →+* E)
    (M : Matrix (Fin 4) (Fin 3) L) (a : L) :
    (fun i => MvPolynomial.map f (universalTangentDirectionPolynomial M a i)) =
      universalTangentDirectionPolynomial (M.map f) (f a) := by
  funext i
  simp [universalTangentDirectionPolynomial, Matrix.mulVec, dotProduct]

/-- Coefficient extension commutes with the full raw secant polynomial. -/
theorem map_universalTwoTangentSecantPolynomial
    {L E : Type u} [Field L] [Field E] (f : L →+* E)
    (c : Cubic L 4) (x y : Fin 4 → L)
    (M N : Matrix (Fin 4) (Fin 3) L) (a b : L) :
    (fun i => MvPolynomial.map f
      (universalTwoTangentSecantPolynomial c x y M N a b i)) =
      universalTwoTangentSecantPolynomial (c.map f)
        (fun i => f (x i)) (fun i => f (y i)) (M.map f) (N.map f) (f a) (f b) := by
  let μ : MvPolynomial ConjugateTangentParameterIndex L →+*
      MvPolynomial ConjugateTangentParameterIndex E := MvPolynomial.map f
  let cP := c.map (MvPolynomial.C : L →+* MvPolynomial ConjugateTangentParameterIndex L)
  have hc : cP.map μ = (c.map f).map MvPolynomial.C := by
    funext i
    simp [cP, Cubic.map, μ]
  have hx : (fun i => μ (MvPolynomial.C (x i))) = fun i => MvPolynomial.C (f (x i)) := by
    funext i
    simp [μ]
  have hy : (fun i => μ (MvPolynomial.C (y i))) = fun i => MvPolynomial.C (f (y i)) := by
    funext i
    simp [μ]
  change (fun i => μ (Cubic.secantResidualPoint cP
    (Cubic.tangentResidualPoint cP (fun i => MvPolynomial.C (x i))
      (universalTangentDirectionPolynomial M a))
    (Cubic.tangentResidualPoint cP (fun i => MvPolynomial.C (y i))
      (universalTangentDirectionPolynomial N b)) i)) = _
  rw [← Cubic.map_secantResidualPoint,
    ← Cubic.map_tangentResidualPoint μ cP (fun i => MvPolynomial.C (x i)),
    ← Cubic.map_tangentResidualPoint μ cP (fun i => MvPolynomial.C (y i)), hc, hx, hy]
  rw [map_universalTangentDirectionPolynomial f M a,
    map_universalTangentDirectionPolynomial f N b]
  rfl

/-- Conjugation exchanging the two complete sets of tangent data negates the
raw polynomial vector, coefficient by coefficient. -/
theorem universalTwoTangentSecantPolynomial_antiInvariant
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (c : Cubic L 4) (x y : Fin 4 → L)
    (M N : Matrix (Fin 4) (Fin 3) L) (a b : L)
    (hc : c.map σ.toRingHom = c)
    (hxy : (fun i => σ (x i)) = y) (hyx : (fun i => σ (y i)) = x)
    (hMN : M.map σ = N) (hNM : N.map σ = M)
    (hab : σ a = b) (hba : σ b = a) :
    (fun i => MvPolynomial.map σ.toRingHom
      (universalTwoTangentSecantPolynomial c x y M N a b i)) =
      -universalTwoTangentSecantPolynomial c x y M N a b := by
  rw [map_universalTwoTangentSecantPolynomial σ.toRingHom c x y M N a b, hc]
  change universalTwoTangentSecantPolynomial c (fun i => σ (x i))
    (fun i => σ (y i)) (M.map σ) (N.map σ) (σ a) (σ b) = _
  rw [hxy, hyx, hMN, hNM, hab, hba]
  unfold universalTwoTangentSecantPolynomial
  exact Cubic.secantResidualPoint_swap _ _ _

/-- An anti-invariant polynomial vector descends after multiplication by one
nonzero scalar of the quadratic splitting field.  The exact polynomial
scaling identity is retained for subsequent specialization and dominance. -/
theorem exists_polynomial_vector_of_scaled_antiInvariant
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    {ι : Type v} {n : ℕ}
    (σ : L ≃ₐ[K] L) (hσ : σ ≠ AlgEquiv.refl) (hdim : finrank K L = 2)
    (r : Fin n → MvPolynomial ι L)
    (hr : ∀ i, MvPolynomial.map σ.toRingHom (r i) = -(r i)) :
    ∃ (s : L) (R : Fin n → MvPolynomial ι K),
      s ≠ 0 ∧ ∀ i, MvPolynomial.map (algebraMap K L) (R i) = MvPolynomial.C s * r i := by
  classical
  obtain ⟨s, hs0, hsanti⟩ := exists_nonzero_antiInvariant_of_involution σ
    (galois_involution_of_finrank_two σ hσ hdim) hσ
  have hcover := galois_aut_eq_refl_or_of_finrank_two σ hσ hdim
  have hcoeff : ∀ i d, ∀ g : L ≃ₐ[K] L,
      g (s * MvPolynomial.coeff d (r i)) = s * MvPolynomial.coeff d (r i) := by
    intro i d g
    rcases hcover g with hg | hg
    · rw [hg]
      rfl
    · rw [hg]
      have hanti : σ (MvPolynomial.coeff d (r i)) = -(MvPolynomial.coeff d (r i)) := by
        have h := congrArg (MvPolynomial.coeff d) (hr i)
        simp only [MvPolynomial.coeff_map, MvPolynomial.coeff_neg] at h
        change σ (MvPolynomial.coeff d (r i)) = -(MvPolynomial.coeff d (r i)) at h
        exact h
      exact antiInvariant_mul_is_fixed σ s _ hsanti hanti
  choose z hz using fun i d =>
    (IsGalois.mem_range_algebraMap_iff_fixed (F := K)
      (s * MvPolynomial.coeff d (r i))).mpr (hcoeff i d)
  refine ⟨s, fun i => ∑ d ∈ (r i).support, MvPolynomial.monomial d (z i d), hs0, ?_⟩
  intro i
  have hsum : MvPolynomial.C s * r i =
      ∑ d ∈ (r i).support, MvPolynomial.monomial d (s * MvPolynomial.coeff d (r i)) := by
    calc
      _ = MvPolynomial.C s *
          (∑ d ∈ (r i).support, MvPolynomial.monomial d (MvPolynomial.coeff d (r i))) := by
            rw [MvPolynomial.support_sum_monomial_coeff]
      _ = _ := by simp only [Finset.mul_sum, MvPolynomial.C_mul_monomial]
  rw [hsum]
  simp only [_root_.map_sum, MvPolynomial.map_monomial, hz]

end PfaffianDescent
