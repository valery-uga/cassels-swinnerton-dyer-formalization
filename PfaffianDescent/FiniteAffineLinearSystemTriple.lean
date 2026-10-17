import PfaffianDescent.GenericRegularSection
import PfaffianDescent.ArtinianQuotientMaximal
import PfaffianDescent.MvPolynomialMaximalHeight
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.KrullDimension.Zero
import Mathlib.RingTheory.HopkinsLevitzki

/-! Select three members of one linear system simultaneously on finitely many
three-dimensional polynomial charts. The FULL system's Artinian chart ideals
supply the avoidance witnesses internally. -/
noncomputable section
namespace PfaffianDescent
open Module
universe u v w
variable {K : Type u} [Field K] [Infinite K]
variable {V : Type v} [AddCommGroup V] [Module K V]
variable {J : Type w} [Finite J]

abbrev finiteAffineLinearSystemFullIdeal (φ : V →ₗ[K] MvPolynomial (Fin 3) K) :=
  Ideal.span (Set.range φ)

abbrev finiteAffineLinearSystemSelectedIdeal
    (φ : V →ₗ[K] MvPolynomial (Fin 3) K) {n : ℕ} (q : Fin n → V) :=
  Ideal.span (Set.range fun i => φ (q i))

private theorem selected_minimalPrime_height_le {n : ℕ}
    (φ : V →ₗ[K] MvPolynomial (Fin 3) K) (q : Fin n → V)
    (P : Ideal (MvPolynomial (Fin 3) K))
    (hP : P ∈ (finiteAffineLinearSystemSelectedIdeal φ q).minimalPrimes) :
    P.height ≤ n := by
  classical
  let s : Finset (MvPolynomial (Fin 3) K) := Finset.univ.image (fun i => φ (q i))
  have hPs : P ∈ (Ideal.span (s : Set (MvPolynomial (Fin 3) K))).minimalPrimes := by
    simpa [s, finiteAffineLinearSystemSelectedIdeal] using hP
  have hcard : s.card ≤ n := by
    exact (Finset.card_image_le).trans_eq (by simp)
  exact (Ideal.height_le_card_of_mem_minimalPrimes_span_finset hPs).trans
    (by exact_mod_cast hcard)

/-- One further section avoids every minimal component of all selected chart
ideals. Full-system finiteness prevents any such height-at-most-two component
from being a base component. -/
private theorem exists_avoiding_selected_minimalPrimes {n : ℕ} (hn : n < 3)
    (φ : J → (V →ₗ[K] MvPolynomial (Fin 3) K)) (q : Fin n → V)
    (hfull : ∀ j, IsArtinianRing
      (MvPolynomial (Fin 3) K ⧸ finiteAffineLinearSystemFullIdeal (φ j))) :
    ∃ r : V, ∀ j, ∀ P ∈ (finiteAffineLinearSystemSelectedIdeal (φ j) q).minimalPrimes,
      φ j r ∉ P := by
  classical
  let PT (j : J) := {P : Ideal (MvPolynomial (Fin 3) K) //
    P ∈ (finiteAffineLinearSystemSelectedIdeal (φ j) q).minimalPrimes}
  letI : ∀ j, Fintype (PT j) := fun j =>
    (Ideal.finite_minimalPrimes_of_isNoetherianRing (MvPolynomial (Fin 3) K)
      (finiteAffineLinearSystemSelectedIdeal (φ j) q)).fintype
  let bad : (Σ j, PT j) → Submodule K V := fun z =>
    ((z.2.val).restrictScalars K).comap (φ z.1)
  have hbad : ∀ z, bad z ≠ ⊤ := by
    rintro ⟨j, P, hP⟩ htop
    letI : P.IsPrime := hP.isPrime
    letI := hfull j
    have hfullP : finiteAffineLinearSystemFullIdeal (φ j) ≤ P := by
      apply Ideal.span_le.mpr
      rintro x ⟨v, rfl⟩
      have hv : v ∈ bad ⟨j, ⟨P, hP⟩⟩ := by
        rw [htop]
        exact Submodule.mem_top
      exact hv
    letI : P.IsMaximal := ideal_isMaximal_of_isArtinian_quotient
      (finiteAffineLinearSystemFullIdeal (φ j)) P hfullP
    have hheight : P.height = 3 := mvPolynomial_maximal_height 3 P
    have hbound := selected_minimalPrime_height_le (φ j) q P hP
    rw [hheight] at hbound
    have hn' : (n : ℕ∞) < 3 := by exact_mod_cast hn
    exact (not_le_of_gt hn') hbound
  obtain ⟨r, hr⟩ := exists_vector_avoiding_finite_submodules bad hbad
  refine ⟨r, ?_⟩
  intro j P hP
  exact hr ⟨j, ⟨P, hP⟩⟩

private theorem exists_selected_chart_height
    (φ : J → (V →ₗ[K] MvPolynomial (Fin 3) K))
    (hfull : ∀ j, IsArtinianRing
      (MvPolynomial (Fin 3) K ⧸ finiteAffineLinearSystemFullIdeal (φ j))) :
    ∀ n : ℕ, n ≤ 3 → ∃ q : Fin n → V,
      ∀ j (P : Ideal (MvPolynomial (Fin 3) K)), P.IsPrime →
        finiteAffineLinearSystemSelectedIdeal (φ j) q ≤ P → (n : ℕ∞) ≤ P.height := by
  intro n
  induction n with
  | zero =>
      intro hn
      exact ⟨fun i => Fin.elim0 i, fun _ _ _ _ => zero_le⟩
  | succ n ih =>
      intro hn
      obtain ⟨q, hq⟩ := ih (by omega)
      obtain ⟨r, hr⟩ := exists_avoiding_selected_minimalPrimes (by omega) φ q hfull
      refine ⟨Fin.cons r q, ?_⟩
      intro j P hP hIP
      letI : P.IsPrime := hP
      have hprev : finiteAffineLinearSystemSelectedIdeal (φ j) q ≤ P := by
        apply le_trans ?_ hIP
        apply Ideal.span_mono
        rintro x ⟨i, rfl⟩
        exact ⟨i.succ, by simp⟩
      obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_minimalPrimes_le hprev
      letI : Q.IsPrime := hQ.isPrime
      have hrP : φ j r ∈ P := hIP (Ideal.subset_span ⟨0, by simp⟩)
      have hQPne : Q ≠ P := by
        intro h
        exact hr j Q hQ (h.symm ▸ hrP)
      have hstrict : Q < P := lt_of_le_of_ne hQP hQPne
      calc
        ((n + 1 : ℕ) : ℕ∞) = (n : ℕ∞) + 1 := by simp
        _ ≤ Q.height + 1 := by
          simpa only [add_comm] using add_le_add_right (hq j Q hQ.isPrime hQ.le) 1
        _ ≤ P.height := Ideal.height_add_one_le_of_lt_of_isPrime hstrict

/-- Three members of the SAME linear system have Artinian intersection on
every affine chart whenever the FULL system does. No independently selected
triple or component-avoidance certificate is an input. -/
theorem exists_three_sections_of_full_chart_artinian
    (φ : J → (V →ₗ[K] MvPolynomial (Fin 3) K))
    (hfull : ∀ j, IsArtinianRing
      (MvPolynomial (Fin 3) K ⧸ finiteAffineLinearSystemFullIdeal (φ j))) :
    ∃ q : Fin 3 → V, ∀ j, IsArtinianRing
      (MvPolynomial (Fin 3) K ⧸ finiteAffineLinearSystemSelectedIdeal (φ j) q) := by
  obtain ⟨q, hq⟩ := exists_selected_chart_height φ hfull 3 le_rfl
  refine ⟨q, ?_⟩
  intro j
  apply isArtinianRing_iff_isNoetherianRing_krullDimLE_zero.mpr
  refine ⟨inferInstance, ?_⟩
  apply Ideal.krullDimLE_zero_quotient_iff_forall_minimalPrimes_isMaximal.mpr
  intro P hP
  letI : P.IsPrime := hP.isPrime
  obtain ⟨M, hM, hPM⟩ := Ideal.exists_le_maximal P (Ideal.IsPrime.ne_top ‹_›)
  letI : M.IsMaximal := hM
  have hPheight := hq j P hP.isPrime hP.le
  have hMheight : M.height = 3 := mvPolynomial_maximal_height 3 M
  have hEq : P = M := by
    by_contra hne
    have hlt := Ideal.height_strict_mono_of_isPrime_of_isPrime (lt_of_le_of_ne hPM hne)
    rw [hMheight] at hlt
    exact (not_lt_of_ge hPheight) hlt
  exact hEq ▸ hM

end PfaffianDescent
