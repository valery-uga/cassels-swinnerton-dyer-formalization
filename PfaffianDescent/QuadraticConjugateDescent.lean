import PfaffianDescent.CubicSecant
import Mathlib.FieldTheory.Galois.Basic

/-!
# Descent of anti-invariant quadratic-conjugate coordinates

The third-intersection coordinates of two conjugate tangent curves are
exchanged with a minus sign.  Over a quadratic Galois extension this is a
projective invariance: multiplication by a nonzero anti-invariant scalar
makes the coordinates invariant, after which Galois descent recovers
coordinates over the fixed field.
-/

namespace PfaffianDescent

open Module

universe u

section

variable {K L : Type u} [Field K] [Field L] [Algebra K L]

/-- An involution which is not the identity has a nonzero anti-invariant
scalar. -/
theorem exists_nonzero_antiInvariant_of_involution
    (σ : L ≃ₐ[K] L) (hσsq : σ.trans σ = AlgEquiv.refl)
    (hσne : σ ≠ AlgEquiv.refl) :
    ∃ s : L, s ≠ 0 ∧ σ s = -s := by
  have hmove : ∃ a : L, σ a ≠ a := by
    by_contra h
    push Not at h
    apply hσne
    ext a
    exact h a
  obtain ⟨a, ha⟩ := hmove
  refine ⟨a - σ a, ?_, ?_⟩
  · intro hzero
    exact ha (sub_eq_zero.mp hzero).symm
  · rw [map_sub]
    have hsq : σ (σ a) = a := by
      have h := DFunLike.congr_fun hσsq a
      change σ (σ a) = a at h
      exact h
    rw [hsq]
    ring

/-- Multiplying two anti-invariant quantities produces an invariant one. -/
theorem antiInvariant_mul_is_fixed
    (σ : L ≃ₐ[K] L) (s z : L)
    (hs : σ s = -s) (hz : σ z = -z) :
    σ (s * z) = s * z := by
  rw [map_mul, hs, hz]
  ring

/-- A cubic defined over the fixed field is unchanged by a fixed-field
automorphism after coefficient extension. -/
theorem cubic_map_algebraMap_fixed_by_algEquiv
    {n : ℕ} (c : Cubic K n) (σ : L ≃ₐ[K] L) :
    (c.map (algebraMap K L)).map σ.toRingHom = c.map (algebraMap K L) := by
  funext i
  exact σ.commutes (c i)

/-- A separable field extension of vector-space dimension two is Galois. -/
theorem isGalois_of_finrank_two_of_separable
    {K L : Type u} [Field K] [Field L] [Algebra K L] [Algebra.IsSeparable K L]
    (hdim : finrank K L = 2) : IsGalois K L := by
  let _ : Module.Free K L := Module.Free.of_divisionRing K L
  let _ : Algebra.IsQuadraticExtension K L := ⟨hdim⟩
  infer_instance

end

section

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- A nonidentity automorphism of a degree-two Galois extension is the only
automorphism other than the identity. -/
theorem galois_aut_eq_refl_or_of_finrank_two
    (σ : L ≃ₐ[K] L) (hσne : σ ≠ AlgEquiv.refl)
    (hdim : finrank K L = 2) :
    ∀ g : L ≃ₐ[K] L, g = AlgEquiv.refl ∨ g = σ := by
  intro g
  by_cases hg0 : g = AlgEquiv.refl
  · exact Or.inl hg0
  by_cases hgσ : g = σ
  · exact Or.inr hgσ
  exfalso
  let e : Fin 3 → (L ≃ₐ[K] L) := ![AlgEquiv.refl, σ, g]
  have he : Function.Injective e := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> try rfl
    · exfalso
      exact hσne (by simpa [e] using hij.symm)
    · exfalso
      exact hg0 (by simpa [e] using hij.symm)
    · exfalso
      exact hσne (by simpa [e] using hij)
    · exfalso
      exact hgσ (by simpa [e] using hij.symm)
    · exfalso
      exact hg0 (by simpa [e] using hij)
    · exfalso
      exact hgσ (by simpa [e] using hij)
  have hle := Fintype.card_le_of_injective e he
  have hcard : Fintype.card (L ≃ₐ[K] L) = 2 := by
    rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank, hdim]
  rw [Fintype.card_fin, hcard] at hle
  omega

/-- The nonidentity automorphism of a degree-two Galois extension is an
involution. -/
theorem galois_involution_of_finrank_two
    (σ : L ≃ₐ[K] L) (hσne : σ ≠ AlgEquiv.refl)
    (hdim : finrank K L = 2) : σ.trans σ = AlgEquiv.refl := by
  have hcover := galois_aut_eq_refl_or_of_finrank_two σ hσne hdim
  rcases hcover (σ.trans σ) with h | h
  · exact h
  · exfalso
    apply hσne
    ext a
    apply σ.injective
    have ha := DFunLike.congr_fun h a
    change σ (σ a) = σ a at ha
    exact ha

/-- A degree-two Galois extension has a nonidentity automorphism. -/
theorem exists_nontrivial_galois_aut_of_finrank_two
    (hdim : finrank K L = 2) :
    ∃ σ : L ≃ₐ[K] L, σ ≠ AlgEquiv.refl := by
  by_contra h
  push Not at h
  have hle : Fintype.card (L ≃ₐ[K] L) ≤ 1 := by
    apply Fintype.card_le_one_iff.mpr
    intro a b
    rw [h a, h b]
  have hcard : Fintype.card (L ≃ₐ[K] L) = 2 := by
    rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank, hdim]
  omega

/-- A vector which becomes invariant after multiplication by an anti-invariant
scalar descends through a two-element Galois group. -/
theorem exists_vector_of_scaled_antiInvariant
    {n : ℕ} (σ : L ≃ₐ[K] L)
    (hcover : ∀ g : L ≃ₐ[K] L, g = AlgEquiv.refl ∨ g = σ)
    (s : L) (r : Fin n → L)
    (hs : σ s = -s) (hr : ∀ i, σ (r i) = -(r i)) :
    ∃ x : Fin n → K, (fun i => algebraMap K L (x i)) = s • r := by
  have hfixed : ∀ i : Fin n, ∀ g : L ≃ₐ[K] L, g (s * r i) = s * r i := by
    intro i g
    rcases hcover g with hg | hg
    · rw [hg]
      rfl
    · rw [hg]
      exact antiInvariant_mul_is_fixed σ s (r i) hs (hr i)
  choose x hx using fun i =>
    (IsGalois.mem_range_algebraMap_iff_fixed (F := K) (s * r i)).mpr (hfixed i)
  refine ⟨x, ?_⟩
  funext i
  exact hx i

/-- An anti-invariant nonzero cubic point over a quadratic Galois extension
is projectively invariant and therefore supplies a nonzero cubic point over
its fixed field. -/
theorem exists_base_cubic_point_of_antiInvariant
    {n : ℕ} (σ : L ≃ₐ[K] L)
    (hσsq : σ.trans σ = AlgEquiv.refl) (hσne : σ ≠ AlgEquiv.refl)
    (hcover : ∀ g : L ≃ₐ[K] L, g = AlgEquiv.refl ∨ g = σ)
    (c : Cubic K n) (r : Vec L n)
    (hr0 : r ≠ 0) (hrc : (c.map (algebraMap K L)).eval r = 0)
    (hranti : ∀ i, σ (r i) = -(r i)) :
    ∃ x : Vec K n, x ≠ 0 ∧ c.eval x = 0 := by
  obtain ⟨s, hs0, hsanti⟩ :=
    exists_nonzero_antiInvariant_of_involution σ hσsq hσne
  obtain ⟨x, hx⟩ := exists_vector_of_scaled_antiInvariant σ hcover s r hsanti hranti
  refine ⟨x, ?_, ?_⟩
  · intro hx0
    have hzero : s • r = 0 := by
      rw [← hx, hx0]
      funext i
      simp
    apply hr0
    funext i
    apply (mul_left_cancel₀ hs0)
    have hi := congrFun hzero i
    change s * r i = 0 at hi
    simpa using hi
  · have hscaled : (c.map (algebraMap K L)).eval (s • r) = 0 := by
      rw [Cubic.eval_smul, hrc, mul_zero]
    have hxeval : (c.map (algebraMap K L)).eval
        (fun i => algebraMap K L (x i)) = 0 := by
      rw [hx]
      exact hscaled
    rw [Cubic.eval_map] at hxeval
    exact (algebraMap K L).injective (by simpa using hxeval)

/-- The preceding descent theorem specialized to a degree-two Galois
extension, where the two group-theoretic hypotheses follow automatically. -/
theorem exists_base_cubic_point_of_antiInvariant_of_finrank_two
    {n : ℕ} (σ : L ≃ₐ[K] L) (hσne : σ ≠ AlgEquiv.refl)
    (hdim : finrank K L = 2)
    (c : Cubic K n) (r : Vec L n)
    (hr0 : r ≠ 0) (hrc : (c.map (algebraMap K L)).eval r = 0)
    (hranti : ∀ i, σ (r i) = -(r i)) :
    ∃ x : Vec K n, x ≠ 0 ∧ c.eval x = 0 :=
  exists_base_cubic_point_of_antiInvariant σ
    (galois_involution_of_finrank_two σ hσne hdim) hσne
    (galois_aut_eq_refl_or_of_finrank_two σ hσne hdim)
    c r hr0 hrc hranti

/-- The algebraic descent step in the two-conjugate-tangent construction.
Two tangent residual points exchanged by the nontrivial automorphism of a
quadratic Galois extension have an anti-invariant secant residual.  Its
projective coordinates therefore descend to a nonzero cubic point over the
fixed field. -/
theorem exists_base_cubic_point_of_conjugate_tangent_secant
    {n : ℕ} (σ : L ≃ₐ[K] L) (hσne : σ ≠ AlgEquiv.refl)
    (hdim : finrank K L = 2)
    (c : Cubic K n) (p q dp dq : Vec L n)
    (hp : (c.map (algebraMap K L)).eval p = 0)
    (hq : (c.map (algebraMap K L)).eval q = 0)
    (htp : (c.map (algebraMap K L)).mixed p dp = 0)
    (htq : (c.map (algebraMap K L)).mixed q dq = 0)
    (hσp : (fun i => σ (p i)) = q) (hσq : (fun i => σ (q i)) = p)
    (hσdp : (fun i => σ (dp i)) = dq) (hσdq : (fun i => σ (dq i)) = dp)
    (hr0 : Cubic.secantResidualPoint (c.map (algebraMap K L))
      (Cubic.tangentResidualPoint (c.map (algebraMap K L)) p dp)
      (Cubic.tangentResidualPoint (c.map (algebraMap K L)) q dq) ≠ 0) :
    ∃ x : Vec K n, x ≠ 0 ∧ c.eval x = 0 := by
  let cL := c.map (algebraMap K L)
  let r := Cubic.secantResidualPoint cL
    (Cubic.tangentResidualPoint cL p dp)
    (Cubic.tangentResidualPoint cL q dq)
  have hcσ : cL.map σ.toRingHom = cL :=
    cubic_map_algebraMap_fixed_by_algEquiv c σ
  have hrc : cL.eval r = 0 := by
    apply Cubic.eval_secantResidualPoint
    · exact Cubic.eval_tangentResidualPoint cL p dp hp htp
    · exact Cubic.eval_tangentResidualPoint cL q dq hq htq
  have hranti : ∀ i, σ (r i) = -(r i) := by
    intro i
    have h := Cubic.map_twoTangentSecantResidual_eq_neg_of_conjugate
      σ.toRingHom cL p q dp dq hcσ hσp hσq hσdp hσdq
    exact congrFun h i
  exact exists_base_cubic_point_of_antiInvariant_of_finrank_two
    σ hσne hdim c r hr0 hrc hranti

end

end PfaffianDescent
