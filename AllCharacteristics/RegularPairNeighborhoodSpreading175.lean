import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Ideal.Colon

/-! SOURCE ONLY / UNCHECKED175. Constructive finite-denominator cut for
spreading the WHOLE actual ideal. No neighborhood-generation or regularity
certificate is assumed. Regularity/clearing arbitrary stalk numerators are
subsequent cuts; this source does not claim the complete regular-pair result. -/

namespace AllCharacteristics

/-- Finitely many actual ideal-membership denominators can be combined
inside the original multiplicative set. -/
theorem exists_uniform_finset_ideal_multiplier175
    {A : Type*} [CommRing A] (S : Submonoid A) (I : Ideal A) (t : Finset A)
    (h : ∀ x ∈ t, ∃ s ∈ S, s * x ∈ I) :
    ∃ s ∈ S, ∀ x ∈ t, s * x ∈ I := by
  classical
  revert h
  induction t using Finset.induction_on with
  | empty =>
      intro h
      exact ⟨1, S.one_mem, by simp⟩
  | insert x t hxt ih =>
      intro h
      obtain ⟨u, hu, hx⟩ := h x (Finset.mem_insert_self x t)
      obtain ⟨v, hv, ht⟩ := ih (fun y hy => h y (Finset.mem_insert_of_mem hy))
      refine ⟨u * v, S.mul_mem hu hv, ?_⟩
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · simpa only [mul_assoc, mul_left_comm] using I.mul_mem_left v hx
      · simpa only [mul_assoc] using I.mul_mem_left u (ht y hy)

/-- Containment of the actual localized ideals at P supplies one original
multiplier outside P which works on EVERY element of the whole FG ideal. -/
theorem exists_uniform_multiplier_of_localized_ideal_le175
    {A : Type*} [CommRing A] (P : Ideal A) [P.IsPrime]
    (J I : Ideal A) (hJ : J.FG)
    (hle : J.map (algebraMap A (Localization.AtPrime P)) ≤
      I.map (algebraMap A (Localization.AtPrime P))) :
    ∃ s ∉ P, ∀ x ∈ J, s * x ∈ I := by
  classical
  obtain ⟨t, ht⟩ := hJ
  change Ideal.span (t : Set A) = J at ht
  have hgenerators : ∀ x ∈ t, ∃ s ∈ P.primeCompl, s * x ∈ I := by
    intro x hx
    have hxJ : x ∈ J := ht ▸ Ideal.subset_span (show x ∈ (t : Set A) from hx)
    have hxL : algebraMap A (Localization.AtPrime P) x ∈
        I.map (algebraMap A (Localization.AtPrime P)) :=
      hle (Ideal.mem_map_of_mem (algebraMap A (Localization.AtPrime P)) hxJ)
    exact (IsLocalization.algebraMap_mem_map_algebraMap_iff
      P.primeCompl (Localization.AtPrime P) I x).mp hxL
  obtain ⟨s, hs, hmult⟩ :=
    exists_uniform_finset_ideal_multiplier175 P.primeCompl I t hgenerators
  have hspan : J ≤ I.colon ({s} : Set A) := by
    rw [← ht]
    apply Ideal.span_le.mpr
    intro x hx
    apply Submodule.mem_colon_singleton.mpr
    simpa only [smul_eq_mul, mul_comm] using hmult x hx
  refine ⟨s, hs, ?_⟩
  intro x hx
  simpa only [smul_eq_mul, mul_comm] using
    (Submodule.mem_colon_singleton.mp (hspan hx))

/-- The whole FG ideal containment holds on a constructed principal
neighborhood, and remains valid on every further principal shrinking.
The maps are the actual algebraMaps into Localization.Away. -/
theorem exists_principal_neighborhood_ideal_le175
    {A : Type*} [CommRing A] (P : Ideal A) [P.IsPrime]
    (J I : Ideal A) (hJ : J.FG)
    (hle : J.map (algebraMap A (Localization.AtPrime P)) ≤
      I.map (algebraMap A (Localization.AtPrime P))) :
    ∃ s ∉ P, ∀ f : A, s ∣ f →
      J.map (algebraMap A (Localization.Away f)) ≤
        I.map (algebraMap A (Localization.Away f)) := by
  obtain ⟨s, hs, hmult⟩ :=
    exists_uniform_multiplier_of_localized_ideal_le175 P J I hJ hle
  refine ⟨s, hs, ?_⟩
  intro f hf
  apply Ideal.map_le_iff_le_comap.mpr
  intro x hx
  change algebraMap A (Localization.Away f) x ∈
    I.map (algebraMap A (Localization.Away f))
  apply (IsLocalization.algebraMap_mem_map_algebraMap_iff
    (Submonoid.powers f) (Localization.Away f) I x).mpr
  refine ⟨f, Submonoid.mem_powers f, ?_⟩
  obtain ⟨c, rfl⟩ := hf
  simpa only [mul_assoc, mul_left_comm] using I.mul_mem_left c (hmult x hx)

/-- Equality of two whole FG ideals at the actual stalk spreads to one
principal neighborhood without changing either ideal or localization map. -/
theorem exists_principal_neighborhood_ideal_eq175
    {A : Type*} [CommRing A] (P : Ideal A) [P.IsPrime]
    (J I : Ideal A) (hJ : J.FG) (hI : I.FG)
    (heq : J.map (algebraMap A (Localization.AtPrime P)) =
      I.map (algebraMap A (Localization.AtPrime P))) :
    ∃ s ∉ P, ∀ f : A, s ∣ f →
      J.map (algebraMap A (Localization.Away f)) =
        I.map (algebraMap A (Localization.Away f)) := by
  obtain ⟨u, hu, hJI⟩ :=
    exists_principal_neighborhood_ideal_le175 P J I hJ heq.le
  obtain ⟨v, hv, hIJ⟩ :=
    exists_principal_neighborhood_ideal_le175 P I J hI heq.symm.le
  refine ⟨u * v, P.primeCompl.mul_mem hu hv, ?_⟩
  intro f hf
  exact le_antisymm
    (hJI f (dvd_trans ⟨v, rfl⟩ hf))
    (hIJ f (dvd_trans ⟨u, mul_comm _ _⟩ hf))

/-- Cleared original affine numerators which generate the stalk ideal
actually generate the WHOLE ideal on a constructed principal neighborhood.
The stronger all-further-shrinkings conclusion lets regularity cuts share
one final denominator. No regularity-on-neighborhood premise occurs. -/
theorem exists_principal_neighborhood_pair_generates175
    {A : Type*} [CommRing A] [IsNoetherianRing A]
    (P : Ideal A) [P.IsPrime] (J : Ideal A) (a b : A)
    (heq : J.map (algebraMap A (Localization.AtPrime P)) =
      (Ideal.span ({a, b} : Set A)).map (algebraMap A (Localization.AtPrime P))) :
    ∃ s ∉ P, ∀ f : A, s ∣ f →
      J.map (algebraMap A (Localization.Away f)) =
        Ideal.span ({algebraMap A (Localization.Away f) a,
          algebraMap A (Localization.Away f) b} : Set (Localization.Away f)) := by
  obtain ⟨s, hs, hspread⟩ := exists_principal_neighborhood_ideal_eq175
    P J (Ideal.span ({a, b} : Set A))
    (IsNoetherian.noetherian J) (IsNoetherian.noetherian _) heq
  refine ⟨s, hs, ?_⟩
  intro f hf
  simpa only [Ideal.map_span, Set.image_insert_eq, Set.image_singleton] using hspread f hf

end AllCharacteristics
