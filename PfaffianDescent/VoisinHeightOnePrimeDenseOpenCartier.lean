import PfaffianDescent.VoisinHeightOnePrimeCartierCriterion
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Finiteness.Defs

/-!
# A dense-open Cartier equation for a height-one prime

An ideal inclusion at a prime can be spread to one basic open when its source
is finitely generated. Applied to the principal ideal at the generic point of
a height-one prime on a regular affine surface, this produces an equation on
a dense open neighborhood of that generic point. It does not assert that the
curve is Cartier at its closed specializations.
-/

namespace PfaffianDescent

universe u

/-- Clear the finitely many denominators of an ideal inclusion in a prime
localization. This is the elementary open-neighborhood step in spreading a
generic Cartier equation. -/
theorem exists_away_ideal_le_of_atPrime_le_of_fg
    {A : Type u} [CommRing A]
    (P I J : Ideal A) [P.IsPrime] (hfg : I.FG)
    (hle : I.map (algebraMap A (Localization.AtPrime P)) ≤
      J.map (algebraMap A (Localization.AtPrime P))) :
    ∃ s : A, s ∉ P ∧
      I.map (algebraMap A (Localization.Away s)) ≤
        J.map (algebraMap A (Localization.Away s)) := by
  classical
  obtain ⟨n, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hfg
  have hgi (i : Fin n) : g i ∈ I := by
    rw [← hg]
    exact Submodule.subset_span (Set.mem_range_self i)
  have hdenom (i : Fin n) :
      ∃ d : P.primeCompl, (d : A) * g i ∈ J := by
    have hm : algebraMap A (Localization.AtPrime P) (g i) ∈
        J.map (algebraMap A (Localization.AtPrime P)) :=
      hle (Ideal.mem_map_of_mem _ (hgi i))
    obtain ⟨d, hd, hmem⟩ :=
      (IsLocalization.algebraMap_mem_map_algebraMap_iff
        P.primeCompl (Localization.AtPrime P) J (g i)).mp hm
    exact ⟨⟨d, hd⟩, hmem⟩
  choose d hd using hdenom
  let s : A := ∏ i : Fin n, (d i : A)
  have hs : s ∉ P := by
    change s ∈ P.primeCompl
    exact P.primeCompl.prod_mem (fun i _ => (d i).property)
  refine ⟨s, hs, ?_⟩
  apply (Ideal.map_le_iff_le_comap).2
  rw [← hg]
  apply Ideal.span_le.mpr
  rintro x ⟨i, rfl⟩
  have hdiv : (d i : A) ∣ s := by
    exact Finset.dvd_prod_of_mem (fun j => (d j : A)) (Finset.mem_univ i)
  obtain ⟨t, ht⟩ := hdiv
  have hsg : s * g i ∈ J := by
    rw [ht]
    simpa only [mul_assoc, mul_left_comm, mul_comm] using
      J.mul_mem_left t (hd i)
  exact (IsLocalization.algebraMap_mem_map_algebraMap_iff
    (Submonoid.powers s) (Localization.Away s) J (g i)).mpr
      ⟨s, Submonoid.mem_powers s, hsg⟩

/-- A finitely generated height-one prime on a regular affine domain has a
regular principal equation on some dense basic open containing its generic
point. The statement is deliberately local near the generic point; it does
not conclude that the whole curve is Cartier. -/
theorem heightOnePrime_denseOpen_regularPrincipal_of_regularLocal
    {A : Type u} [CommRing A] [IsDomain A]
    (P : Ideal A) [P.IsPrime] (hfg : P.FG) (hheight : P.height = 1)
    (hregular : IsRegularLocalRing (Localization.AtPrime P)) :
    ∃ s : A, s ∉ P ∧ ∃ z : A, z ∈ P ∧
      IsRegular (algebraMap A (Localization.Away s) z) ∧
      P.map (algebraMap A (Localization.Away s)) =
        Ideal.span ({algebraMap A (Localization.Away s) z} :
          Set (Localization.Away s)) := by
  classical
  let S := Localization.AtPrime P
  obtain ⟨a, haRegular, haP⟩ :=
    heightOnePrime_atGeneric_regularPrincipal_of_regularLocal
      P hheight hregular
  have haMem : a ∈ P.map (algebraMap A S) := by
    rw [haP]
    exact Ideal.mem_span_singleton_self a
  obtain ⟨⟨⟨z, hzP⟩, d⟩, hzd⟩ :=
    (IsLocalization.mem_map_algebraMap_iff P.primeCompl S).mp haMem
  have hdUnit : IsUnit (algebraMap A S (d : A)) :=
    IsLocalization.map_units S d
  have hlocEq : P.map (algebraMap A S) =
      Ideal.span ({algebraMap A S z} : Set S) := by
    calc
      P.map (algebraMap A S) = Ideal.span ({a} : Set S) := haP
      _ = Ideal.span ({a * algebraMap A S (d : A)} : Set S) :=
        (Ideal.span_singleton_mul_right_unit hdUnit a).symm
      _ = Ideal.span ({algebraMap A S z} : Set S) := by rw [hzd]
  have hle : P.map (algebraMap A S) ≤
      (Ideal.span ({z} : Set A)).map (algebraMap A S) := by
    simpa only [Ideal.map_span, Set.image_singleton] using le_of_eq hlocEq
  obtain ⟨s, hsP, hleAway⟩ :=
    exists_away_ideal_le_of_atPrime_le_of_fg
      P P (Ideal.span ({z} : Set A)) hfg hle
  have hAwayEq : P.map (algebraMap A (Localization.Away s)) =
      Ideal.span ({algebraMap A (Localization.Away s) z} :
        Set (Localization.Away s)) := by
    apply le_antisymm
    · simpa only [Ideal.map_span, Set.image_singleton] using hleAway
    · exact (Ideal.span_singleton_le_iff_mem
        (P.map (algebraMap A (Localization.Away s)))).mpr
          (Ideal.mem_map_of_mem _ hzP)
  have ha0 : a ≠ 0 := (isRegular_iff_ne_zero).mp haRegular
  have hz0 : z ≠ 0 := by
    intro hz
    have hprod : a * algebraMap A S (d : A) = 0 := by
      calc
        a * algebraMap A S (d : A) = algebraMap A S z := hzd
        _ = 0 := by rw [hz]; exact map_zero _
    exact (mul_ne_zero ha0 hdUnit.ne_zero) hprod
  have hs0 : s ≠ 0 := by
    intro hzero
    exact hsP (by simpa [hzero] using P.zero_mem)
  letI : IsDomain (Localization.Away s) := Localization.Away.isDomain hs0
  have hAwayInj : Function.Injective (algebraMap A (Localization.Away s)) :=
    IsLocalization.injective (Localization.Away s)
      (powers_le_nonZeroDivisors_of_noZeroDivisors hs0)
  have hzAway0 : algebraMap A (Localization.Away s) z ≠ 0 := by
    intro hzero
    exact hz0 (hAwayInj (by simpa using hzero))
  exact ⟨s, hsP, z, hzP, isRegular_iff_ne_zero.mpr hzAway0, hAwayEq⟩

/-- The regular-ring form can be applied directly on a smooth affine cubic
chart once the curve kernel is known to be a height-one prime. -/
theorem heightOnePrime_denseOpen_regularPrincipal_of_regularRing
    {A : Type u} [CommRing A] [IsDomain A] [IsRegularRing A]
    (P : Ideal A) [P.IsPrime] (hfg : P.FG) (hheight : P.height = 1) :
    ∃ s : A, s ∉ P ∧ ∃ z : A, z ∈ P ∧
      IsRegular (algebraMap A (Localization.Away s) z) ∧
      P.map (algebraMap A (Localization.Away s)) =
        Ideal.span ({algebraMap A (Localization.Away s) z} :
          Set (Localization.Away s)) :=
  heightOnePrime_denseOpen_regularPrincipal_of_regularLocal
    P hfg hheight (IsRegularRing.isRegularLocalRing_localization P)

end PfaffianDescent
