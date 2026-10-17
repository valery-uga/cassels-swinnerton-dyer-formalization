import AllCharacteristics.RegularPairNeighborhoodRegularity176

/-! SOURCE ONLY / UNCHECKED177. The supplied ACTUAL stalk pair is cleared
using membership in the WHOLE actual ideal. Unit denominators preserve the
same spans and regularity. No pair-regular-on-neighborhood hypothesis. -/

open scoped nonZeroDivisors
namespace AllCharacteristics

/-- Clear the two actual stalk ideal generators to actual affine numerators
IN J. The explicit original denominator identities are retained, and units
preserve the full stalk ideal and both original NZD conditions. -/
theorem exists_affine_numerators_of_stalk_regular_pair177
    {A : Type*} [CommRing A] (P : Ideal A) [P.IsPrime] (J : Ideal A)
    (a b : Localization.AtPrime P)
    (hgen : J.map (algebraMap A (Localization.AtPrime P)) =
      Ideal.span ({a, b} : Set (Localization.AtPrime P)))
    (ha : a ∈ (Localization.AtPrime P)⁰)
    (hb : Ideal.Quotient.mk (Ideal.span ({a} : Set (Localization.AtPrime P))) b ∈
      ((Localization.AtPrime P) ⧸ Ideal.span ({a} : Set (Localization.AtPrime P)))⁰) :
    ∃ a₀ b₀ s t : A, s ∉ P ∧ t ∉ P ∧ a₀ ∈ J ∧ b₀ ∈ J ∧
      a * algebraMap A (Localization.AtPrime P) s =
        algebraMap A (Localization.AtPrime P) a₀ ∧
      b * algebraMap A (Localization.AtPrime P) t =
        algebraMap A (Localization.AtPrime P) b₀ ∧
      J.map (algebraMap A (Localization.AtPrime P)) =
        (Ideal.span ({a₀, b₀} : Set A)).map (algebraMap A (Localization.AtPrime P)) ∧
      algebraMap A (Localization.AtPrime P) a₀ ∈ (Localization.AtPrime P)⁰ ∧
      Ideal.Quotient.mk ((Ideal.span ({a₀} : Set A)).map
        (algebraMap A (Localization.AtPrime P)))
        (algebraMap A (Localization.AtPrime P) b₀) ∈
          ((Localization.AtPrime P) ⧸ (Ideal.span ({a₀} : Set A)).map
            (algebraMap A (Localization.AtPrime P)))⁰ := by
  have haJ : a ∈ J.map (algebraMap A (Localization.AtPrime P)) := by
    rw [hgen]
    exact Ideal.subset_span (by simp)
  have hbJ : b ∈ J.map (algebraMap A (Localization.AtPrime P)) := by
    rw [hgen]
    exact Ideal.subset_span (by simp)
  obtain ⟨⟨a₀, s⟩, has⟩ :=
    (IsLocalization.mem_map_algebraMap_iff P.primeCompl (Localization.AtPrime P)).mp haJ
  obtain ⟨⟨b₀, t⟩, hbt⟩ :=
    (IsLocalization.mem_map_algebraMap_iff P.primeCompl (Localization.AtPrime P)).mp hbJ
  have hspanA : Ideal.span ({algebraMap A (Localization.AtPrime P) (a₀ : A)} :
      Set (Localization.AtPrime P)) = Ideal.span {a} := by
    rw [← has]
    exact Ideal.span_singleton_mul_right_unit (IsLocalization.map_units _ s) a
  have hspanB : Ideal.span ({algebraMap A (Localization.AtPrime P) (b₀ : A)} :
      Set (Localization.AtPrime P)) = Ideal.span {b} := by
    rw [← hbt]
    exact Ideal.span_singleton_mul_right_unit (IsLocalization.map_units _ t) b
  have hgen₀ : J.map (algebraMap A (Localization.AtPrime P)) =
      (Ideal.span ({(a₀ : A), (b₀ : A)} : Set A)).map
        (algebraMap A (Localization.AtPrime P)) := by
    rw [Ideal.map_span, Set.image_insert_eq, Set.image_singleton, hgen]
    rw [Ideal.span_insert, Ideal.span_insert, hspanA, hspanB]
  have ha₀ : algebraMap A (Localization.AtPrime P) (a₀ : A) ∈
      (Localization.AtPrime P)⁰ := by
    rw [← has]
    exact mul_mem_nonZeroDivisors.mpr
      ⟨ha, (IsLocalization.map_units _ s).mem_nonZeroDivisors⟩
  have hb₀ : Ideal.Quotient.mk ((Ideal.span ({(a₀ : A)} : Set A)).map
      (algebraMap A (Localization.AtPrime P)))
      (algebraMap A (Localization.AtPrime P) (b₀ : A)) ∈
        ((Localization.AtPrime P) ⧸ (Ideal.span ({(a₀ : A)} : Set A)).map
          (algebraMap A (Localization.AtPrime P)))⁰ := by
    rw [Ideal.map_span, Set.image_singleton, hspanA, ← hbt, map_mul]
    exact mul_mem_nonZeroDivisors.mpr ⟨hb,
      ((IsLocalization.map_units _ t).map (Ideal.Quotient.mk (Ideal.span {a}))).mem_nonZeroDivisors⟩
  exact ⟨(a₀ : A), (b₀ : A), (s : A), (t : A), s.2, t.2, a₀.2, b₀.2,
    has, hbt, hgen₀, ha₀, hb₀⟩

/-- Actual stalk generators of the whole ideal which form a regular pair
spread to an ACTUAL regular pair generating the WHOLE ideal on a constructed
principal neighborhood. Both neighborhood coordinates are cleared original
numerators under the literal original algebraMap. -/
theorem exists_principal_neighborhood_regular_pair_of_stalk177
    {A : Type*} [CommRing A] [IsNoetherianRing A]
    (P : Ideal A) [P.IsPrime] (J : Ideal A)
    (a b : Localization.AtPrime P)
    (hgen : J.map (algebraMap A (Localization.AtPrime P)) =
      Ideal.span ({a, b} : Set (Localization.AtPrime P)))
    (ha : a ∈ (Localization.AtPrime P)⁰)
    (hb : Ideal.Quotient.mk (Ideal.span ({a} : Set (Localization.AtPrime P))) b ∈
      ((Localization.AtPrime P) ⧸ Ideal.span ({a} : Set (Localization.AtPrime P)))⁰) :
    ∃ f ∉ P, ∃ a' b' : Localization.Away f,
      J.map (algebraMap A (Localization.Away f)) = Ideal.span ({a', b'} : Set _) ∧
      a' ∈ (Localization.Away f)⁰ ∧
      Ideal.Quotient.mk (Ideal.span ({a'} : Set (Localization.Away f))) b' ∈
        ((Localization.Away f) ⧸ Ideal.span ({a'} : Set (Localization.Away f)))⁰ := by
  obtain ⟨a₀, b₀, s, t, hs, ht, haJ, hbJ, has, hbt, hgen₀, ha₀, hb₀⟩ :=
    exists_affine_numerators_of_stalk_regular_pair177 P J a b hgen ha hb
  obtain ⟨f, hf, hJ, hA, hB⟩ :=
    exists_principal_neighborhood_regular_pair_of_affine_numerators176
      P J a₀ b₀ hgen₀ ha₀ hb₀
  exact ⟨f, hf, algebraMap A (Localization.Away f) a₀,
    algebraMap A (Localization.Away f) b₀, hJ, hA, hB⟩

end AllCharacteristics
