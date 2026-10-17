import PfaffianDescent.MatchingCoordinateLineSchemes
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Tactic
/-! SOURCE ONLY / UNVERIFIED. Mixed cubic pieces are computed from the
actual polynomial and actual coordinate-line ideal memberships. -/
noncomputable section
namespace PfaffianDescent.QuadraticSkewRationality.MixedNormalForm
open MvPolynomial
open scoped BigOperators
universe u
variable {E : Type u} [Field E]

def leftDegree (m : Fin 4 →₀ ℕ) : ℕ := m 0 + m 1

def blockPiece (d : ℕ) (G : MvPolynomial (Fin 4) E) : MvPolynomial (Fin 4) E :=
  ∑ m ∈ G.support.filter (fun m => leftDegree m = d), monomial m (G.coeff m)

theorem coeff_blockPiece (d : ℕ) (G : MvPolynomial (Fin 4) E) (m : Fin 4 →₀ ℕ) :
    (blockPiece d G).coeff m = if leftDegree m = d then G.coeff m else 0 := by
  classical
  by_cases hm : m ∈ G.support
  · simp [blockPiece, coeff_sum, coeff_monomial, hm, eq_comm]
  · have hz : G.coeff m = 0 := notMem_support_iff.mp hm
    simp [blockPiece, coeff_sum, coeff_monomial, hm, hz, eq_comm]

theorem blockPiece_homogeneous (d : ℕ) (G : MvPolynomial (Fin 4) E)
    (hG : G.IsHomogeneous 3) : (blockPiece d G).IsHomogeneous 3 := by
  intro m hm
  by_cases hdegree : leftDegree m = d
  · rw [coeff_blockPiece, if_pos hdegree] at hm
    exact hG hm
  · rw [coeff_blockPiece, if_neg hdegree] at hm
    exact (hm rfl).elim

/-- The literal line memberships eliminate pure-block cubic terms.
The remaining block degrees are exactly (2,1) and (1,2). -/
theorem cubic_support_leftDegree_one_or_two
    (G : MvPolynomial (Fin 4) E) (hG : G.IsHomogeneous 3)
    (hLeft : G ∈ Ideal.span ({X 0, X 1} : Set (MvPolynomial (Fin 4) E)))
    (hRight : G ∈ Ideal.span ({X 2, X 3} : Set (MvPolynomial (Fin 4) E))) :
    ∀ m ∈ G.support, leftDegree m = 1 ∨ leftDegree m = 2 := by
  classical
  intro m hm
  have hL : ∃ i ∈ ({0, 1} : Set (Fin 4)), m i ≠ 0 := by
    apply MvPolynomial.mem_ideal_span_X_image.mp ?_ m hm
    simpa only [Set.image_pair] using hLeft
  have hR : ∃ i ∈ ({2, 3} : Set (Fin 4)), m i ≠ 0 := by
    apply MvPolynomial.mem_ideal_span_X_image.mp ?_ m hm
    simpa only [Set.image_pair] using hRight
  have hLpos : 0 < m 0 + m 1 := by
    obtain ⟨i, hi, hmi⟩ := hL
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi
    rcases hi with rfl | rfl <;> omega
  have hRpos : 0 < m 2 + m 3 := by
    obtain ⟨i, hi, hmi⟩ := hR
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi
    rcases hi with rfl | rfl <;> omega
  have hd : m.degree = 3 := by
    by_contra h
    exact (mem_support_iff.mp hm) (hG.coeff_eq_zero h)
  have hsum : m 0 + m 1 + m 2 + m 3 = 3 := by
    simpa only [Finsupp.degree_eq_sum, Fin.sum_univ_four] using hd
  dsimp only [leftDegree]
  omega

theorem cubic_eq_two_mixed_block_pieces
    (G : MvPolynomial (Fin 4) E) (hG : G.IsHomogeneous 3)
    (hLeft : G ∈ Ideal.span ({X 0, X 1} : Set (MvPolynomial (Fin 4) E)))
    (hRight : G ∈ Ideal.span ({X 2, X 3} : Set (MvPolynomial (Fin 4) E))) :
    G = blockPiece 2 G + blockPiece 1 G := by
  classical
  ext m
  rw [coeff_add, coeff_blockPiece, coeff_blockPiece]
  by_cases hm : G.coeff m = 0
  · simp only [hm, ite_self, add_zero]
  · rcases cubic_support_leftDegree_one_or_two G hG hLeft hRight m
      (mem_support_iff.mpr hm) with h | h <;> simp [h]

def pairSwap : Equiv.Perm (Fin 4) :=
  (Equiv.swap 0 2).trans (Equiv.swap 1 3)

theorem pairSwap_involutive : Function.Involutive pairSwap := by
  intro i
  fin_cases i <;> decide

/-- These six exponents are the (2,1) mixed monomials. -/
def leftMixedExponent (i : Fin 3) (j : Fin 2) : Fin 4 →₀ ℕ :=
  Finsupp.single 0 (2 - i.val) + Finsupp.single 1 i.val +
    Finsupp.single 2 (1 - j.val) + Finsupp.single 3 j.val

/-- These six exponents are the conjugate (1,2) mixed monomials. -/
def rightMixedExponent (i : Fin 3) (j : Fin 2) : Fin 4 →₀ ℕ :=
  Finsupp.single 0 (1 - j.val) + Finsupp.single 1 j.val +
    Finsupp.single 2 (2 - i.val) + Finsupp.single 3 i.val

theorem leftMixedExponent_complete
    (m : Fin 4 →₀ ℕ) (hTotal : m 0 + m 1 + m 2 + m 3 = 3)
    (hLeft : leftDegree m = 2) :
    ∃ i : Fin 3, ∃ j : Fin 2, leftMixedExponent i j = m := by
  dsimp only [leftDegree] at hLeft
  refine ⟨⟨m 1, by omega⟩, ⟨m 3, by omega⟩, ?_⟩
  ext r
  fin_cases r <;> simp [leftMixedExponent] <;> omega

theorem rightMixedExponent_complete
    (m : Fin 4 →₀ ℕ) (hTotal : m 0 + m 1 + m 2 + m 3 = 3)
    (hLeft : leftDegree m = 1) :
    ∃ i : Fin 3, ∃ j : Fin 2, rightMixedExponent i j = m := by
  dsimp only [leftDegree] at hLeft
  refine ⟨⟨m 3, by omega⟩, ⟨m 1, by omega⟩, ?_⟩
  ext r
  fin_cases r <;> simp [rightMixedExponent] <;> omega

/-- The computed two pieces have precisely the six possible mixed
exponents in each block. Thus the normal form has no hidden other terms. -/
theorem blockPiece_support_mixed_exponent
    (G : MvPolynomial (Fin 4) E) (hG : G.IsHomogeneous 3) :
    (∀ m ∈ (blockPiece 2 G).support, ∃ i : Fin 3, ∃ j : Fin 2,
      leftMixedExponent i j = m) ∧
    (∀ m ∈ (blockPiece 1 G).support, ∃ i : Fin 3, ∃ j : Fin 2,
      rightMixedExponent i j = m) := by
  have hTotal (m : Fin 4 →₀ ℕ) (hm : G.coeff m ≠ 0) :
      m 0 + m 1 + m 2 + m 3 = 3 := by
    have hd : m.degree = 3 := by
      by_contra h
      exact hm (hG.coeff_eq_zero h)
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_four] at hd
    exact hd
  constructor
  · intro m hm
    have hc := mem_support_iff.mp hm
    by_cases h : leftDegree m = 2
    · rw [coeff_blockPiece, if_pos h] at hc
      exact leftMixedExponent_complete m (hTotal m hc) h
    · rw [coeff_blockPiece, if_neg h] at hc
      exact (hc rfl).elim
  · intro m hm
    have hc := mem_support_iff.mp hm
    by_cases h : leftDegree m = 1
    · rw [coeff_blockPiece, if_pos h] at hc
      exact rightMixedExponent_complete m (hTotal m hc) h
    · rw [coeff_blockPiece, if_neg h] at hc
      exact (hc rfl).elim

/-- Reconstruct a polynomial from a finite injective list containing its
support. This keeps each mixed-block reconstruction bounded at six terms. -/
theorem polynomial_eq_sum_of_support_covered
    {J : Type*} [Fintype J] (H : MvPolynomial (Fin 4) E)
    (e : J → Fin 4 →₀ ℕ) (he : Function.Injective e)
    (hCover : ∀ m ∈ H.support, ∃ a, e a = m) :
    H = ∑ a, monomial (e a) (H.coeff (e a)) := by
  classical
  ext m
  rw [coeff_sum]
  by_cases h : ∃ a, e a = m
  · obtain ⟨a, rfl⟩ := h
    simp [coeff_monomial, he.eq_iff]
  · have hzero : H.coeff m = 0 := by
      apply notMem_support_iff.mp
      exact fun hm => h (hCover m hm)
    rw [hzero]
    symm
    apply Finset.sum_eq_zero
    intro a _
    rw [coeff_monomial, if_neg]
    exact fun hm => h ⟨a, hm⟩

theorem leftMixedExponent_injective :
    Function.Injective (fun ij : Fin 3 × Fin 2 => leftMixedExponent ij.1 ij.2) := by
  intro a b h
  apply Prod.ext
  · apply Fin.ext
    have h₁ := DFunLike.congr_fun h (1 : Fin 4)
    simpa [leftMixedExponent] using h₁
  · apply Fin.ext
    have h₃ := DFunLike.congr_fun h (3 : Fin 4)
    simpa [leftMixedExponent] using h₃

theorem rightMixedExponent_injective :
    Function.Injective (fun ij : Fin 3 × Fin 2 => rightMixedExponent ij.1 ij.2) := by
  intro a b h
  apply Prod.ext
  · apply Fin.ext
    have h₃ := DFunLike.congr_fun h (3 : Fin 4)
    simpa [rightMixedExponent] using h₃
  · apply Fin.ext
    have h₁ := DFunLike.congr_fun h (1 : Fin 4)
    simpa [rightMixedExponent] using h₁

theorem leftMixedExponent_leftDegree (i : Fin 3) (j : Fin 2) :
    leftDegree (leftMixedExponent i j) = 2 := by
  simp [leftDegree, leftMixedExponent]
  omega

theorem rightMixedExponent_leftDegree (i : Fin 3) (j : Fin 2) :
    leftDegree (rightMixedExponent i j) = 1 := by
  simp [leftDegree, rightMixedExponent]
  omega

def leftMixedPolynomial (G : MvPolynomial (Fin 4) E) : MvPolynomial (Fin 4) E :=
  ∑ ij : Fin 3 × Fin 2, monomial (leftMixedExponent ij.1 ij.2)
    (G.coeff (leftMixedExponent ij.1 ij.2))

def rightMixedPolynomial (G : MvPolynomial (Fin 4) E) : MvPolynomial (Fin 4) E :=
  ∑ ij : Fin 3 × Fin 2, monomial (rightMixedExponent ij.1 ij.2)
    (G.coeff (rightMixedExponent ij.1 ij.2))

theorem blockPiece_two_eq_leftMixedPolynomial
    (G : MvPolynomial (Fin 4) E) (hG : G.IsHomogeneous 3) :
    blockPiece 2 G = leftMixedPolynomial G := by
  have hCover : ∀ m ∈ (blockPiece 2 G).support,
      ∃ ij : Fin 3 × Fin 2, leftMixedExponent ij.1 ij.2 = m := by
    intro m hm
    obtain ⟨i, j, h⟩ := (blockPiece_support_mixed_exponent G hG).1 m hm
    exact ⟨(i, j), h⟩
  rw [polynomial_eq_sum_of_support_covered (blockPiece 2 G) _
    leftMixedExponent_injective hCover]
  simp only [coeff_blockPiece, leftMixedExponent_leftDegree, if_true, leftMixedPolynomial]

theorem blockPiece_one_eq_rightMixedPolynomial
    (G : MvPolynomial (Fin 4) E) (hG : G.IsHomogeneous 3) :
    blockPiece 1 G = rightMixedPolynomial G := by
  have hCover : ∀ m ∈ (blockPiece 1 G).support,
      ∃ ij : Fin 3 × Fin 2, rightMixedExponent ij.1 ij.2 = m := by
    intro m hm
    obtain ⟨i, j, h⟩ := (blockPiece_support_mixed_exponent G hG).2 m hm
    exact ⟨(i, j), h⟩
  rw [polynomial_eq_sum_of_support_covered (blockPiece 1 G) _
    rightMixedExponent_injective hCover]
  simp only [coeff_blockPiece, rightMixedExponent_leftDegree, if_true, rightMixedPolynomial]

theorem cubic_eq_twelve_mixed_monomials
    (G : MvPolynomial (Fin 4) E) (hG : G.IsHomogeneous 3)
    (hLeft : G ∈ Ideal.span ({X 0, X 1} : Set (MvPolynomial (Fin 4) E)))
    (hRight : G ∈ Ideal.span ({X 2, X 3} : Set (MvPolynomial (Fin 4) E))) :
    G = leftMixedPolynomial G + rightMixedPolynomial G := by
  calc
    G = blockPiece 2 G + blockPiece 1 G := cubic_eq_two_mixed_block_pieces G hG hLeft hRight
    _ = leftMixedPolynomial G + rightMixedPolynomial G := by
      rw [blockPiece_two_eq_leftMixedPolynomial G hG,
        blockPiece_one_eq_rightMixedPolynomial G hG]

theorem leftMixedExponent_monomial (i : Fin 3) (j : Fin 2) (a : E) :
    monomial (leftMixedExponent i j) a =
      C a * X 0 ^ (2 - i.val) * X 1 ^ i.val *
        X 2 ^ (1 - j.val) * X 3 ^ j.val := by
  simp only [leftMixedExponent]
  rw [monomial_add_single, monomial_add_single, monomial_add_single,
    ← C_mul_X_pow_eq_monomial]

theorem rightMixedExponent_monomial (i : Fin 3) (j : Fin 2) (a : E) :
    monomial (rightMixedExponent i j) a =
      C a * X 0 ^ (1 - j.val) * X 1 ^ j.val *
        X 2 ^ (2 - i.val) * X 3 ^ i.val := by
  simp only [rightMixedExponent]
  rw [monomial_add_single, monomial_add_single, monomial_add_single,
    ← C_mul_X_pow_eq_monomial]

theorem rightMixedExponent_mapDomain_pairSwap (i : Fin 3) (j : Fin 2) :
    (rightMixedExponent i j).mapDomain pairSwap = leftMixedExponent i j := by
  simp only [rightMixedExponent, leftMixedExponent, Finsupp.mapDomain_add,
    Finsupp.mapDomain_single]
  have h0 : pairSwap (0 : Fin 4) = 2 := by decide
  have h1 : pairSwap (1 : Fin 4) = 3 := by decide
  have h2 : pairSwap (2 : Fin 4) = 0 := by decide
  have h3 : pairSwap (3 : Fin 4) = 1 := by decide
  simp only [h0, h1, h2, h3]
  ac_rfl

/-- Conjugation exchanges the twelve mixed coefficients. The needed
polynomial exchange identity is derived from the original paired frame
in the separate original-coordinate bridge. -/
theorem conjugate_mixed_coefficients_exchange
    {k : Type u} [Field k] [Algebra k E]
    (σ : E ≃ₐ[k] E) (G : MvPolynomial (Fin 4) E)
    (hExchange : MvPolynomial.map σ.toRingHom G = MvPolynomial.rename pairSwap G)
    (i : Fin 3) (j : Fin 2) :
    σ (G.coeff (leftMixedExponent i j)) = G.coeff (rightMixedExponent i j) := by
  have hRename : (MvPolynomial.rename pairSwap G).coeff (leftMixedExponent i j) =
      G.coeff (rightMixedExponent i j) := by
    rw [← rightMixedExponent_mapDomain_pairSwap]
    exact MvPolynomial.coeff_rename_mapDomain pairSwap pairSwap.injective G _
  have h := congrArg (fun p : MvPolynomial (Fin 4) E =>
    p.coeff (leftMixedExponent i j)) hExchange
  rw [MvPolynomial.coeff_map, hRename] at h
  exact h

end PfaffianDescent.QuadraticSkewRationality.MixedNormalForm
