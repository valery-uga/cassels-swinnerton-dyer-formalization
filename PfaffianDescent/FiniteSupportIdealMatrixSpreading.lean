import AllCharacteristics.RegularPairNeighborhoodSpreading175
import Mathlib.RingTheory.Localization.Integer
import Mathlib.Data.Matrix.Basic

/-!
Spread whole-ideal equalities from an arbitrary localization and clear a
finite matrix with one simultaneous denominator. The multiplicative set
may be the constructed set avoiding the entire finite support.
-/
noncomputable section
namespace PfaffianDescent
universe u v w
set_option autoImplicit false

/-- One denominator in the original multiplicative set clears EVERY matrix
entry.  No injectivity/domain assumption is needed.  If S avoids a finite
support, this denominator avoids every support point simultaneously. -/
theorem finiteMatrix_exists_commonDenominator001
    {A : Type u} [CommRing A] (S : Submonoid A)
    {m : Type v} {n : Type w} [Finite m] [Finite n]
    (M : Matrix m n (Localization S)) :
    ∃ d : A, d ∈ S ∧ ∃ N : Matrix m n A,
      ∀ i j, algebraMap A (Localization S) (N i j) =
        algebraMap A (Localization S) d * M i j := by
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite S
    (fun ij : m × n => M ij.1 ij.2)
  have hnum : ∀ ij : m × n, ∃ a : A,
      algebraMap A (Localization S) a = (d : A) • M ij.1 ij.2 := hd
  choose a ha using hnum
  refine ⟨d, d.property, (fun i j => a (i, j)), ?_⟩
  intro i j
  simpa only [Algebra.smul_def] using ha (i, j)

/-- Whole finite-generated ideal containment in an arbitrary localization
has one clearing multiplier in its actual original multiplicative set. -/
theorem wholeIdeal_exists_multiplier_of_localized_le001
    {A : Type u} [CommRing A] (S : Submonoid A)
    (J I : Ideal A) (hJ : J.FG)
    (hle : J.map (algebraMap A (Localization S)) ≤
      I.map (algebraMap A (Localization S))) :
    ∃ s : A, s ∈ S ∧ ∀ x ∈ J, s * x ∈ I := by
  classical
  obtain ⟨t, ht⟩ := hJ
  change Ideal.span (t : Set A) = J at ht
  have hgenerators : ∀ x ∈ t, ∃ s ∈ S, s * x ∈ I := by
    intro x hx
    have hxJ : x ∈ J := ht ▸ Ideal.subset_span (show x ∈ (t : Set A) from hx)
    have hxL : algebraMap A (Localization S) x ∈
        I.map (algebraMap A (Localization S)) :=
      hle (Ideal.mem_map_of_mem (algebraMap A (Localization S)) hxJ)
    exact (IsLocalization.algebraMap_mem_map_algebraMap_iff
      S (Localization S) I x).mp hxL
  obtain ⟨s, hs, hmult⟩ :=
    AllCharacteristics.exists_uniform_finset_ideal_multiplier175 S I t hgenerators
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

/-- Whole ideal containment spreads to one principal localization and all
its further principal shrinkings.  This is not restricted to one prime. -/
theorem wholeIdeal_exists_principal_le_of_localized_le001
    {A : Type u} [CommRing A] (S : Submonoid A)
    (J I : Ideal A) (hJ : J.FG)
    (hle : J.map (algebraMap A (Localization S)) ≤
      I.map (algebraMap A (Localization S))) :
    ∃ s : A, s ∈ S ∧ ∀ f : A, s ∣ f →
      J.map (algebraMap A (Localization.Away f)) ≤
        I.map (algebraMap A (Localization.Away f)) := by
  obtain ⟨s, hs, hmult⟩ := wholeIdeal_exists_multiplier_of_localized_le001 S J I hJ hle
  refine ⟨s, hs, ?_⟩
  intro f hf
  apply Ideal.map_le_iff_le_comap.mpr
  intro x hx
  apply (IsLocalization.algebraMap_mem_map_algebraMap_iff
    (Submonoid.powers f) (Localization.Away f) I x).mpr
  obtain ⟨c, rfl⟩ := hf
  refine ⟨s * c, Submonoid.mem_powers (s * c), ?_⟩
  simpa only [mul_assoc, mul_left_comm] using I.mul_mem_left c (hmult x hx)

/-- Equality of whole FG ideals over the finite-support semilocal ring
spreads to ONE principal neighborhood containing that entire support.
This applies to the old ideal and a cleared matrix's minors ideal once
the semilocal Hilbert--Burch equality has actually been proved. -/
theorem wholeIdeal_exists_principal_eq_of_localized_eq001
    {A : Type u} [CommRing A] (S : Submonoid A)
    (J I : Ideal A) (hJ : J.FG) (hI : I.FG)
    (heq : J.map (algebraMap A (Localization S)) =
      I.map (algebraMap A (Localization S))) :
    ∃ s : A, s ∈ S ∧ ∀ f : A, s ∣ f →
      J.map (algebraMap A (Localization.Away f)) =
        I.map (algebraMap A (Localization.Away f)) := by
  obtain ⟨u, hu, hJI⟩ := wholeIdeal_exists_principal_le_of_localized_le001 S J I hJ heq.le
  obtain ⟨v, hv, hIJ⟩ := wholeIdeal_exists_principal_le_of_localized_le001 S I J hI heq.symm.le
  refine ⟨u * v, S.mul_mem hu hv, ?_⟩
  intro f hf
  exact le_antisymm
    (hJI f (dvd_trans ⟨v, rfl⟩ hf))
    (hIJ f (dvd_trans ⟨u, mul_comm _ _⟩ hf))

end PfaffianDescent
end
