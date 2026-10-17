import PfaffianDescent.GaloisFixedPolynomialCoefficientDescent
import Mathlib.SetTheory.Cardinal.Finite

/-! SOURCE ONLY, UNVERIFIED. WHOLE stable polynomial ideals descend over
any quadratic Galois extension, including characteristic 2. Coefficients
are split using alpha-sigma(alpha), never division by 2. The stability
hypothesis is an INTERNAL generic interface, derived for actual matching
intersection by a later factory. -/
noncomputable section
namespace PfaffianDescent
open Module MvPolynomial
universe u v
variable {k E : Type u} [Field k] [Field E] [Algebra k E]
  [FiniteDimensional k E] [IsGalois k E]

theorem quadratic_galois_involution_data (hdeg : finrank k E = 2) :
    ∃ sigma : E ≃ₐ[k] E, sigma ≠ 1 ∧
      (∀ g : E ≃ₐ[k] E, g = 1 ∨ g = sigma) ∧
      (∀ z, sigma (sigma z) = z) ∧ ∃ alpha, alpha ≠ sigma alpha := by
  classical
  have hcard : Nat.card (E ≃ₐ[k] E) = 2 :=
    (IsGalois.card_aut_eq_finrank k E).trans hdeg
  obtain ⟨sigma, hsigma, huniq⟩ :=
    (Nat.card_eq_two_iff' (1 : E ≃ₐ[k] E)).mp hcard
  have hcases (g : E ≃ₐ[k] E) : g = 1 ∨ g = sigma := by
    by_cases h : g = 1
    · exact Or.inl h
    · exact Or.inr (huniq g h)
  have hsquare : sigma * sigma = 1 := by
    rcases hcases (sigma * sigma) with h | h
    · exact h
    · have he : sigma * sigma = sigma * 1 := by simpa only [mul_one] using h
      exact False.elim (hsigma (mul_left_cancel he))
  have hnotfix : ¬ ∀ z, sigma z = z := by
    intro h
    apply hsigma
    ext z
    exact h z
  obtain ⟨alpha, halpha⟩ := not_forall.mp hnotfix
  refine ⟨sigma, hsigma, hcases, ?_, alpha, Ne.symm halpha⟩
  intro z
  have h := congrArg (fun g : E ≃ₐ[k] E => g z) hsquare
  simpa only [AlgEquiv.mul_apply, AlgEquiv.one_apply] using h

theorem quadratic_galois_stable_polynomial_ideal_descends {J : Type v}
    (hdeg : finrank k E = 2) (I : Ideal (MvPolynomial J E))
    (hstable : ∀ g : E ≃ₐ[k] E, ∀ q ∈ I, MvPolynomial.map g.toRingHom q ∈ I) :
    (I.comap (MvPolynomial.map (algebraMap k E))).map
      (MvPolynomial.map (algebraMap k E)) = I := by
  classical
  let f : MvPolynomial J k →+* MvPolynomial J E := MvPolynomial.map (algebraMap k E)
  apply le_antisymm
  · exact Ideal.map_le_iff_le_comap.mpr le_rfl
  · intro q hq
    obtain ⟨sigma, hsigma, hcases, hsquare, alpha, halpha⟩ :=
      quadratic_galois_involution_data (k := k) (E := E) hdeg
    let delta := alpha - sigma alpha
    have hdelta : delta ≠ 0 := sub_ne_zero.mpr halpha
    let S : MvPolynomial J E →+* MvPolynomial J E := MvPolynomial.map sigma.toRingHom
    let v : MvPolynomial J E := C delta⁻¹ * (q - S q)
    let u : MvPolynomial J E := q - C alpha * v
    have hS2 : S (S q) = q := by
      apply MvPolynomial.ext
      intro d
      simp only [S, MvPolynomial.coeff_map]
      change sigma (sigma (q.coeff d)) = q.coeff d
      exact hsquare (q.coeff d)
    have hdeltaS : sigma delta = -delta := by
      dsimp only [delta]
      rw [map_sub, hsquare]
      ring
    have hvfixed : S v = v := by
      dsimp only [S, v]
      rw [map_mul, MvPolynomial.map_C, map_sub]
      change C (sigma delta⁻¹) * (S q - S (S q)) = v
      rw [map_inv₀, hdeltaS, hS2]
      dsimp only [v]
      simp only [inv_neg, map_neg]
      ring
    have hrelation : C delta * v = q - S q := by
      dsimp only [v]
      rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hdelta, map_one, one_mul]
    have hufixed : S u = u := by
      dsimp only [u]
      rw [map_sub, map_mul, MvPolynomial.map_C, hvfixed]
      change S q - C (sigma alpha) * v = q - C alpha * v
      have hdC : (C delta : MvPolynomial J E) = C alpha - C (sigma alpha) := by
        dsimp only [delta]
        rw [map_sub]
      rw [hdC] at hrelation
      linear_combination hrelation
    have hvall (g : E ≃ₐ[k] E) : MvPolynomial.map g.toRingHom v = v := by
      rcases hcases g with rfl | rfl
      · change MvPolynomial.map (RingHom.id E) _ = _
        exact MvPolynomial.map_id _
      · exact hvfixed
    have huall (g : E ≃ₐ[k] E) : MvPolynomial.map g.toRingHom u = u := by
      rcases hcases g with rfl | rfl
      · change MvPolynomial.map (RingHom.id E) _ = _
        exact MvPolynomial.map_id _
      · exact hufixed
    have hvI : v ∈ I :=
      I.mul_mem_left _ (I.sub_mem hq (hstable sigma q hq))
    have huI : u ∈ I := I.sub_mem hq (I.mul_mem_left _ hvI)
    obtain ⟨U, hU⟩ := galois_fixed_polynomial_descends u huall
    obtain ⟨V, hV⟩ := galois_fixed_polynomial_descends v hvall
    have hUmem : U ∈ I.comap f := by
      change f U ∈ I
      exact hU.symm ▸ huI
    have hVmem : V ∈ I.comap f := by
      change f V ∈ I
      exact hV.symm ▸ hvI
    have hu : u ∈ (I.comap f).map f := by
      rw [← hU]
      exact Ideal.mem_map_of_mem f hUmem
    have hv : v ∈ (I.comap f).map f := by
      rw [← hV]
      exact Ideal.mem_map_of_mem f hVmem
    have hqeq : q = u + C alpha * v := by dsimp only [u]; ring
    rw [hqeq]
    exact Ideal.add_mem _ hu (Ideal.mul_mem_left _ _ hv)

end PfaffianDescent
