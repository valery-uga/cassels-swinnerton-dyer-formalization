import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.KrullDimension.Polynomial

namespace PfaffianDescent

/-- Every maximal ideal of a polynomial ring in `n` variables over a field has height `n`. -/
theorem mvPolynomial_maximal_height
    {K : Type*} [Field K] (n : ℕ)
    (P : Ideal (MvPolynomial (Fin n) K)) [P.IsMaximal] : P.height = n := by
  induction n with
  | zero =>
      let e : MvPolynomial (Fin 0) K ≃+* K :=
        MvPolynomial.isEmptyRingEquiv K (Fin 0)
      let Q : Ideal K := Ideal.map e P
      have hQmax : Q.IsMaximal := Ideal.map_isMaximal_of_equiv e
      have hQ : Q = ⊥ := (Ideal.eq_bot_or_top Q).resolve_right
        (Ideal.IsMaximal.ne_top hQmax)
      rw [← e.height_map P]
      change Q.height = _
      rw [hQ, Ideal.height_bot]
      simp
  | succ n ih =>
      let e := MvPolynomial.finSuccEquiv K n
      let Q : Ideal (Polynomial (MvPolynomial (Fin n) K)) := Ideal.map e P
      have hQmax : Q.IsMaximal := Ideal.map_isMaximal_of_equiv e
      let p : Ideal (MvPolynomial (Fin n) K) := Q.under (MvPolynomial (Fin n) K)
      have hpmax : p.IsMaximal := Polynomial.isMaximal_comap_C_of_isJacobsonRing Q
      have hp : p.height = n := ih p
      have hQ : Q.height = p.height + 1 := Polynomial.height_eq_height_add_one p Q
      rw [← e.toRingEquiv.height_map P]
      change Q.height = _
      rw [hQ, hp]
      simp

/-- The preceding height computation after renaming an arbitrary finite variable set to `Fin n`. -/
theorem mvPolynomial_maximal_height_of_fintype
    {K σ : Type*} [Field K] [Fintype σ]
    (P : Ideal (MvPolynomial σ K)) [P.IsMaximal] : P.height = Fintype.card σ := by
  let e := MvPolynomial.renameEquiv K (Fintype.equivFin σ)
  let Q : Ideal (MvPolynomial (Fin (Fintype.card σ)) K) := Ideal.map e P
  have hQmax : Q.IsMaximal := Ideal.map_isMaximal_of_equiv e
  rw [← e.toRingEquiv.height_map P]
  change Q.height = _
  exact mvPolynomial_maximal_height (Fintype.card σ) Q

end PfaffianDescent
