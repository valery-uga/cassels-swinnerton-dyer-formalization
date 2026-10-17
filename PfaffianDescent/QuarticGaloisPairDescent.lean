import PfaffianDescent.CubicPolynomialQuadraticDescent
import Mathlib.FieldTheory.Galois.Infinite

/-!
# Descent from a Galois-stable pair of cubic points

The matching-line branch produces a nonzero cubic zero whose Galois orbit has
at most two elements.  This file descends that zero without a characteristic
restriction.
-/

namespace PfaffianDescent

open Module MvPolynomial

universe u

variable {k K : Type u} [Field k] [Field K] [Algebra k K] [IsGalois k K]

theorem galois_fixed_element_descends (a : K) (ha : ∀ g : K ≃ₐ[k] K, g a = a) :
    ∃ c : k, algebraMap k K c = a := by
  apply IntermediateField.mem_bot.mp
  rw [← InfiniteGalois.fixedField_bot]
  exact (IntermediateField.mem_fixedField_iff _ _).mpr (fun g _ => ha g)

theorem cubic_point_of_fixed_vector (F : MvPolynomial (Fin 4) k)
    (x : Fin 4 → K) (hx : x ≠ 0) (hF : aeval x F = 0)
    (hfix : ∀ g : K ≃ₐ[k] K, ∀ i, g (x i) = x i) :
    ∃ p : Fin 4 → k, p ≠ 0 ∧ aeval p F = 0 := by
  choose p hp using fun i => galois_fixed_element_descends (x i) (fun g => hfix g i)
  have hpn : p ≠ 0 := by
    intro hz
    apply hx
    funext i
    rw [← hp i, hz]
    simp
  refine ⟨p, hpn, ?_⟩
  apply (algebraMap k K).injective
  have he : (Algebra.ofId k K).comp (aeval p) = aeval x := by
    ext i : 1
    simpa using hp i
  change (Algebra.ofId k K) ((aeval p) F) = (Algebra.ofId k K) 0
  rw [map_zero]
  exact (AlgHom.congr_fun he F).trans hF

theorem cubic_point_of_galois_pair (F : MvPolynomial (Fin 4) k)
    (hF : F.IsHomogeneous 3) (x y : Fin 4 → K) (hx : x ≠ 0) (hzero : aeval x F = 0)
    (hpair : ∀ g : K ≃ₐ[k] K,
      ((∀ i, g (x i) = x i) ∧ (∀ i, g (y i) = y i)) ∨
      ((∀ i, g (x i) = y i) ∧ (∀ i, g (y i) = x i))) :
    ∃ p : Fin 4 → k, p ≠ 0 ∧ aeval p F = 0 := by
  classical
  by_cases hfix : ∀ g : K ≃ₐ[k] K, ∀ i, g (x i) = x i
  · exact cubic_point_of_fixed_vector F x hx hzero hfix
  have hxy : x ≠ y := by
    intro he
    apply hfix
    intro g
    rcases hpair g with h | h
    · exact h.1
    · simpa only [he] using h.1
  obtain ⟨j, hj⟩ : ∃ j, x j ≠ y j := by
    by_contra! h
    exact hxy (funext h)
  let a := x j
  let a' := y j
  have hd : a - a' ≠ 0 := sub_ne_zero.mpr hj
  have hA (i : Fin 4) : ∀ g : K ≃ₐ[k] K,
      g ((a * y i - a' * x i) / (a - a')) = (a * y i - a' * x i) / (a - a') := by
    intro g
    rcases hpair g with ⟨hg, hg'⟩ | ⟨hg, hg'⟩
    · simp [a, a', map_div₀, map_sub, map_mul, hg, hg']
    · simp only [map_div₀ g, map_sub g, map_mul g]
      simp only [a, a', hg, hg']
      change (y j * x i - x j * y i) / (y j - x j) =
        (x j * y i - y j * x i) / (x j - y j)
      field_simp [sub_ne_zero.mpr hj, sub_ne_zero.mpr (Ne.symm hj)]
      ring
  have hB (i : Fin 4) : ∀ g : K ≃ₐ[k] K,
      g ((x i - y i) / (a - a')) = (x i - y i) / (a - a') := by
    intro g
    rcases hpair g with ⟨hg, hg'⟩ | ⟨hg, hg'⟩
    · simp [a, a', map_div₀, map_sub, hg, hg']
    · simp only [map_div₀ g, map_sub g]
      simp only [a, a', hg, hg']
      change (y i - x i) / (y j - x j) = (x i - y i) / (x j - y j)
      field_simp [sub_ne_zero.mpr hj, sub_ne_zero.mpr (Ne.symm hj)]
      ring
  choose A hAeq using fun i => galois_fixed_element_descends _ (hA i)
  choose B hBeq using fun i => galois_fixed_element_descends _ (hB i)
  have hcoords (i : Fin 4) : algebraMap k K (A i) + algebraMap k K (B i) * a = x i := by
    rw [hAeq, hBeq]
    field_simp [hd]
    ring
  have han : a ∉ (algebraMap k K).range := by
    rintro ⟨c, hc⟩
    apply hfix
    intro g i
    rw [← hcoords i, map_add, map_mul, AlgEquiv.commutes, AlgEquiv.commutes, ← hc,
      AlgEquiv.commutes]
  obtain ⟨s, hs⟩ := galois_fixed_element_descends (a + a') (by
    intro g
    rcases hpair g with h | h <;> simp [a, a', map_add, h.1, h.2, add_comm])
  obtain ⟨t, ht⟩ := galois_fixed_element_descends (a * a') (by
    intro g
    rcases hpair g with h | h <;> simp [a, a', map_mul, h.1, h.2, mul_comm])
  let q : Polynomial k := Polynomial.X ^ 2 - Polynomial.C s * Polynomial.X + Polynomial.C t
  have hqmap : q.map (algebraMap k K) =
      (Polynomial.X - Polynomial.C a) * (Polynomial.X - Polynomial.C a') := by
    simp [q, hs, ht]
    ring
  have hqdeg : q.natDegree = 2 := by
    rw [← Polynomial.natDegree_map (algebraMap k K), hqmap,
      Polynomial.natDegree_mul (Polynomial.monic_X_sub_C a).ne_zero
        (Polynomial.monic_X_sub_C a').ne_zero]
    simp
  have hqzero : Polynomial.aeval a q = 0 := by
    simp [q, hs, ht]
    ring
  have hai : IsIntegral k a := Algebra.IsIntegral.isIntegral a
  have hdeg : (minpoly k a).natDegree = 2 := by
    apply le_antisymm
    · have hqn : q ≠ 0 := by intro h; simp [h] at hqdeg
      exact (Polynomial.natDegree_le_of_dvd (minpoly.dvd k a hqzero) hqn).trans_eq hqdeg
    · exact (minpoly.two_le_natDegree_iff hai).mpr han
  let E := IntermediateField.adjoin k ({a} : Set K)
  letI : FiniteDimensional k E := IntermediateField.adjoin.finiteDimensional hai
  have hE : finrank k E = 2 := (IntermediateField.adjoin.finrank hai).trans hdeg
  let aE : E := ⟨a, IntermediateField.subset_adjoin k _ (Set.mem_singleton a)⟩
  let xE : Fin 4 → E := fun i => algebraMap k E (A i) + algebraMap k E (B i) * aE
  have hxE (i : Fin 4) : E.val (xE i) = x i := by
    simpa [xE, aE] using hcoords i
  have hxEn : xE ≠ 0 := by
    intro hz
    apply hx
    funext i
    rw [← hxE i, hz]
    simp
  have hzeroE : aeval xE F = 0 := by
    apply E.val.injective
    have he : E.val.comp (aeval xE) = aeval x := by
      ext i : 1
      simpa using hxE i
    change E.val ((aeval xE) F) = E.val 0
    rw [map_zero]
    exact (AlgHom.congr_fun he F).trans hzero
  exact homogeneous_cubic_degree_le_two_descent_without_characteristic F hF (by
    rw [hE]) xE hxEn hzeroE

end PfaffianDescent
