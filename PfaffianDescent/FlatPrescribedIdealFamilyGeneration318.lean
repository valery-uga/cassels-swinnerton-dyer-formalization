import AllCharacteristics.FlatPrescribedIdealPairGeneration

/-!
Lift arbitrary generator families inside the original ideal by the
whole-ideal nilpotent Nakayama theorem. The construction extends the
regular-pair generator interface without assuming a finite generation,
basis, or relative-presentation conclusion.
-/

noncomputable section
namespace AllCharacteristics
universe u v w t

/-- Lifts inside the original ideal generate that entire ideal whenever
their reductions generate its entire special-fiber ideal. -/
theorem prescribedIdeal_eq_span_range_of_nilpotent_reduction318
    {R : Type u} {A : Type v} {A₀ : Type w} {ι : Type t}
    [CommRing R] [CommRing A] [CommRing A₀] [Algebra R A]
    (π : A →+* A₀) (hπ : Function.Surjective π)
    (I : Ideal R) (hI : IsNilpotent I)
    (hker : RingHom.ker π = I.map (algebraMap R A))
    (J : Ideal A) [Module.Flat R (A ⧸ J)]
    (f : ι → A) (hf : ∀ i, f i ∈ J)
    (hmap : J.map π = Ideal.span (Set.range (fun i => π (f i)))) :
    J = Ideal.span (Set.range f) := by
  have hL : Ideal.span (Set.range f) ≤ J := by
    apply Ideal.span_le.mpr
    rintro x ⟨i, rfl⟩
    exact hf i
  have hnil : IsNilpotent (RingHom.ker π) := by
    obtain ⟨n, hn⟩ := hI
    refine ⟨n, ?_⟩
    rw [hker, ← Ideal.map_pow, hn]
    simp only [Ideal.zero_eq_bot, Ideal.map_bot]
  have hLmap : (Ideal.span (Set.range f)).map π =
      Ideal.span (Set.range (fun i => π (f i))) := by
    rw [Ideal.map_span, ← Set.range_comp]
    rfl
  apply ideal_eq_of_same_nilpotent_reduction167 π hπ _ J hL
    (hmap.trans hLmap.symm) hnil
  rw [hker]
  exact quotient_flat_baseIdeal_inf_eq_mul167 I J

/-- Construct a family lifting every specified reduced generator inside
the original prescribed ideal, and prove whole-ideal generation. -/
theorem exists_prescribedIdeal_family_lifts_of_nilpotent_reduction318
    {R : Type u} {A : Type v} {A₀ : Type w} {ι : Type t}
    [CommRing R] [CommRing A] [CommRing A₀] [Algebra R A]
    (π : A →+* A₀) (hπ : Function.Surjective π)
    (I : Ideal R) (hI : IsNilpotent I)
    (hker : RingHom.ker π = I.map (algebraMap R A))
    (J : Ideal A) [Module.Flat R (A ⧸ J)] (f₀ : ι → A₀)
    (hmap : J.map π = Ideal.span (Set.range f₀)) :
    ∃ f : ι → A, (∀ i, f i ∈ J) ∧ (∀ i, π (f i) = f₀ i) ∧
      J = Ideal.span (Set.range f) := by
  have hlift : ∀ i, ∃ x : A, x ∈ J ∧ π x = f₀ i := by
    intro i
    have hi : f₀ i ∈ J.map π := by
      rw [hmap]
      exact Ideal.mem_span_range_self (x := i)
    exact (Ideal.mem_map_iff_of_surjective π hπ).mp hi
  choose f hf hff using hlift
  refine ⟨f, hf, hff, ?_⟩
  apply prescribedIdeal_eq_span_range_of_nilpotent_reduction318 π hπ I hI hker J f hf
  simpa only [hff] using hmap

end AllCharacteristics
end
