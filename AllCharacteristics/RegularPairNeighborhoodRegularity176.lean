import AllCharacteristics.RegularPairNeighborhoodSpreading175
import Mathlib.Algebra.Ring.NonZeroDivisors

/-! SOURCE ONLY / UNCHECKED176. NZD spreading by actual finite annihilator
and colon ideals. All maps are the original algebraMaps, with no assumed
neighborhood regularity. This cut treats affine numerators; clearing an
arbitrary supplied stalk pair is a separate next cut. -/

open scoped nonZeroDivisors
namespace AllCharacteristics

/-- Vanishing of the localized actual annihilator makes the original
coefficient a non-zero-divisor in the actual localization. -/
theorem algebraMap_mem_nonZeroDivisors_of_annihilator_map_le176
    {A : Type*} [CommRing A] (M : Submonoid A)
    (B : Type*) [CommRing B] [Algebra A B] [IsLocalization M B]
    (a : A)
    (hann : ((⊥ : Ideal A).colon ({a} : Set A)).map (algebraMap A B) ≤ ⊥) :
    algebraMap A B a ∈ B⁰ := by
  apply mem_nonZeroDivisors_iff_right.mpr
  intro z hz
  obtain ⟨r, s, rfl⟩ := IsLocalization.exists_mk'_eq M z
  have hra : algebraMap A B (r * a) = 0 := by
    calc
      algebraMap A B (r * a) =
          (IsLocalization.mk' B r s * algebraMap A B s) * algebraMap A B a := by
        rw [IsLocalization.mk'_spec, map_mul]
      _ = (IsLocalization.mk' B r s * algebraMap A B a) * algebraMap A B s := by
        simp only [mul_assoc, mul_comm, mul_left_comm]
      _ = 0 := by rw [hz, zero_mul]
  obtain ⟨u, hu⟩ := (IsLocalization.map_eq_zero_iff M B (r * a)).mp hra
  have huAnn : (u : A) * r ∈ (⊥ : Ideal A).colon ({a} : Set A) := by
    apply Submodule.mem_colon_singleton.mpr
    change ((u : A) * r) * a = 0
    simpa only [mul_assoc] using hu
  have hur : algebraMap A B ((u : A) * r) = 0 := by
    have := hann (Ideal.mem_map_of_mem (algebraMap A B) huAnn)
    simpa only [Ideal.mem_bot] using this
  have hr : algebraMap A B r = 0 :=
    (mul_left_mem_nonZeroDivisors_eq_zero_iff
      (IsLocalization.map_units B u).mem_nonZeroDivisors).mp
      (by simpa only [map_mul] using hur)
  apply (IsLocalization.map_units B s).mul_left_inj.mp
  simpa only [zero_mul, hr] using IsLocalization.mk'_spec B r s

/-- The actual colon inclusion after localization gives exactly the NZD
condition in the quotient by the whole localized original ideal. -/
theorem quotient_algebraMap_mem_nonZeroDivisors_of_colon_map_le176
    {A : Type*} [CommRing A] (M : Submonoid A)
    (B : Type*) [CommRing B] [Algebra A B] [IsLocalization M B]
    (I : Ideal A) (b : A)
    (hcolon : (I.colon ({b} : Set A)).map (algebraMap A B) ≤
      I.map (algebraMap A B)) :
    Ideal.Quotient.mk (I.map (algebraMap A B)) (algebraMap A B b) ∈
      (B ⧸ I.map (algebraMap A B))⁰ := by
  apply mem_nonZeroDivisors_iff_left.mpr
  intro x hx
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨r, s, rfl⟩ := IsLocalization.exists_mk'_eq M z
  have hxI : algebraMap A B b * IsLocalization.mk' B r s ∈
      I.map (algebraMap A B) := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa only [map_mul] using hx
  have hbr : algebraMap A B (b * r) ∈ I.map (algebraMap A B) := by
    have heq : algebraMap A B (b * r) =
        algebraMap A B s * (algebraMap A B b * IsLocalization.mk' B r s) := by
      rw [map_mul, ← IsLocalization.mk'_spec B r s]
      simp only [mul_assoc, mul_comm, mul_left_comm]
    rw [heq]
    exact (I.map (algebraMap A B)).mul_mem_left _ hxI
  obtain ⟨u, huM, huI⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff
    M B I (b * r)).mp hbr
  have huC : u * r ∈ I.colon ({b} : Set A) := by
    apply Submodule.mem_colon_singleton.mpr
    change (u * r) * b ∈ I
    simpa only [mul_assoc, mul_comm, mul_left_comm] using huI
  have hur : algebraMap A B (u * r) ∈ I.map (algebraMap A B) :=
    hcolon (Ideal.mem_map_of_mem (algebraMap A B) huC)
  have hr : algebraMap A B r ∈ I.map (algebraMap A B) :=
    (Ideal.unit_mul_mem_iff_mem _ (IsLocalization.map_units B ⟨u, huM⟩)).mp
      (by simpa only [map_mul] using hur)
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact (IsLocalization.mk'_mem_iff (M := M) (S := B)).mpr hr

/-- A coefficient regular at P is regular on a constructed principal
neighborhood, uniformly under further shrinking. Noetherianity supplies
finite generation of its actual annihilator. -/
theorem exists_principal_neighborhood_nonZeroDivisor176
    {A : Type*} [CommRing A] [IsNoetherianRing A]
    (P : Ideal A) [P.IsPrime] (a : A)
    (ha : algebraMap A (Localization.AtPrime P) a ∈ (Localization.AtPrime P)⁰) :
    ∃ s ∉ P, ∀ f : A, s ∣ f →
      algebraMap A (Localization.Away f) a ∈ (Localization.Away f)⁰ := by
  let C : Ideal A := (⊥ : Ideal A).colon ({a} : Set A)
  have hCP : C.map (algebraMap A (Localization.AtPrime P)) ≤
      (⊥ : Ideal A).map (algebraMap A (Localization.AtPrime P)) := by
    rw [Ideal.map_bot]
    apply Ideal.map_le_iff_le_comap.mpr
    intro x hx
    change algebraMap A (Localization.AtPrime P) x = 0
    apply (mem_nonZeroDivisors_iff_right.mp ha) _
    have hxa : x * a = 0 := by
      simpa only [smul_eq_mul, Ideal.mem_bot] using
        (Submodule.mem_colon_singleton.mp hx)
    rw [← map_mul, hxa, map_zero]
  obtain ⟨s, hs, hspread⟩ := exists_principal_neighborhood_ideal_le175
    P C ⊥ (IsNoetherian.noetherian C) hCP
  refine ⟨s, hs, ?_⟩
  intro f hf
  apply algebraMap_mem_nonZeroDivisors_of_annihilator_map_le176
    (Submonoid.powers f) (Localization.Away f) a
  simpa only [Ideal.map_bot, C] using hspread f hf

/-- Regularity modulo the original ideal spreads by its actual finite colon
ideal. The quotient and localization maps remain literal original maps. -/
theorem exists_principal_neighborhood_quotient_nonZeroDivisor176
    {A : Type*} [CommRing A] [IsNoetherianRing A]
    (P : Ideal A) [P.IsPrime] (I : Ideal A) (b : A)
    (hb : Ideal.Quotient.mk (I.map (algebraMap A (Localization.AtPrime P)))
      (algebraMap A (Localization.AtPrime P) b) ∈
        ((Localization.AtPrime P) ⧸ I.map (algebraMap A (Localization.AtPrime P)))⁰) :
    ∃ s ∉ P, ∀ f : A, s ∣ f →
      Ideal.Quotient.mk (I.map (algebraMap A (Localization.Away f)))
        (algebraMap A (Localization.Away f) b) ∈
          ((Localization.Away f) ⧸ I.map (algebraMap A (Localization.Away f)))⁰ := by
  let C : Ideal A := I.colon ({b} : Set A)
  have hCP : C.map (algebraMap A (Localization.AtPrime P)) ≤
      I.map (algebraMap A (Localization.AtPrime P)) := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro x hx
    change algebraMap A (Localization.AtPrime P) x ∈
      I.map (algebraMap A (Localization.AtPrime P))
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply (mem_nonZeroDivisors_iff_right.mp hb) _
    rw [← map_mul]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [← map_mul]
    apply Ideal.mem_map_of_mem
    simpa only [smul_eq_mul] using (Submodule.mem_colon_singleton.mp hx)
  obtain ⟨s, hs, hspread⟩ := exists_principal_neighborhood_ideal_le175
    P C I (IsNoetherian.noetherian C) hCP
  refine ⟨s, hs, ?_⟩
  intro f hf
  exact quotient_algebraMap_mem_nonZeroDivisors_of_colon_map_le176
    (Submonoid.powers f) (Localization.Away f) I b (hspread f hf)

/-- Cleared affine generators with the actual stalk regularity hypotheses
produce a genuine regular pair generating the WHOLE original ideal on one
constructed principal neighborhood. No neighborhood assumption is used. -/
theorem exists_principal_neighborhood_regular_pair_of_affine_numerators176
    {A : Type*} [CommRing A] [IsNoetherianRing A]
    (P : Ideal A) [P.IsPrime] (J : Ideal A) (a b : A)
    (hgen : J.map (algebraMap A (Localization.AtPrime P)) =
      (Ideal.span ({a, b} : Set A)).map (algebraMap A (Localization.AtPrime P)))
    (ha : algebraMap A (Localization.AtPrime P) a ∈ (Localization.AtPrime P)⁰)
    (hb : Ideal.Quotient.mk ((Ideal.span ({a} : Set A)).map
      (algebraMap A (Localization.AtPrime P)))
      (algebraMap A (Localization.AtPrime P) b) ∈
        ((Localization.AtPrime P) ⧸ (Ideal.span ({a} : Set A)).map
          (algebraMap A (Localization.AtPrime P)))⁰) :
    ∃ f ∉ P,
      J.map (algebraMap A (Localization.Away f)) =
        Ideal.span ({algebraMap A (Localization.Away f) a,
          algebraMap A (Localization.Away f) b} : Set (Localization.Away f)) ∧
      algebraMap A (Localization.Away f) a ∈ (Localization.Away f)⁰ ∧
      Ideal.Quotient.mk (Ideal.span ({algebraMap A (Localization.Away f) a} :
        Set (Localization.Away f))) (algebraMap A (Localization.Away f) b) ∈
          ((Localization.Away f) ⧸ Ideal.span ({algebraMap A (Localization.Away f) a} :
            Set (Localization.Away f)))⁰ := by
  obtain ⟨u, hu, hgenU⟩ := exists_principal_neighborhood_pair_generates175 P J a b hgen
  obtain ⟨v, hv, haV⟩ := exists_principal_neighborhood_nonZeroDivisor176 P a ha
  obtain ⟨w, hw, hbW⟩ :=
    exists_principal_neighborhood_quotient_nonZeroDivisor176 P (Ideal.span {a}) b hb
  let f := u * v * w
  have huf : u ∣ f := ⟨v * w, mul_assoc _ _ _⟩
  have hvf : v ∣ f := ⟨u * w, by simp only [f, mul_assoc, mul_comm, mul_left_comm]⟩
  have hwf : w ∣ f := ⟨u * v, mul_comm _ _⟩
  refine ⟨f, P.primeCompl.mul_mem (P.primeCompl.mul_mem hu hv) hw,
    hgenU f huf, haV f hvf, ?_⟩
  have he : (Ideal.span ({a} : Set A)).map (algebraMap A (Localization.Away f)) =
      Ideal.span ({algebraMap A (Localization.Away f) a} : Set (Localization.Away f)) := by
    rw [Ideal.map_span, Set.image_singleton]
  exact he ▸ hbW f hwf

end AllCharacteristics
