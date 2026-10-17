import PfaffianDescent.ThreeGeneratorKoszul

/-! # Ambient Koszul exactness for three regular parameters

These statements work over any commutative ring. They do not require the
ambient local ring to carry a chosen factorization structure.
-/

namespace PfaffianDescent

open scoped nonZeroDivisors

variable {R : Type*} [CommRing R]

theorem pointCartierYoneda_first_injective {f g h : R} (hf : f ∈ R⁰) :
    Function.Injective (threeGeneratorFirst f g h) := by
  intro x y hxy
  apply sub_eq_zero.mp
  apply mem_nonZeroDivisors_iff_left.mp hf
  have heq := congrArg (fun v : R × R × R ↦ v.2.2) hxy
  change f * x = f * y at heq
  rw [mul_sub, heq, sub_self]

theorem pointCartierYoneda_middle_exact {f g h : R} (hf : f ∈ R⁰)
    (hg : Ideal.Quotient.mk (Ideal.span {f}) g ∈ (R ⧸ Ideal.span {f})⁰) :
    LinearMap.range (threeGeneratorFirst f g h) =
      LinearMap.ker (threeGeneratorMiddle f g h) := by
  apply le_antisymm
  · exact LinearMap.range_le_ker_iff.mpr (threeGenerator_middle_comp_first f g h)
  · rintro ⟨a, b, c⟩ habc
    have h₂ : f * a - h * c = 0 := congrArg (fun v : R × R × R ↦ v.2.1) habc
    have h₃ : f * b + g * c = 0 := congrArg (fun v : R × R × R ↦ v.2.2) habc
    have hbc : (b, c) ∈ LinearMap.ker (twoGeneratorLast f g) := h₃
    rw [← twoGenerator_exact_of_regular hf hg] at hbc
    obtain ⟨d, hd⟩ := hbc
    have hdb : -g * d = b := congrArg Prod.fst hd
    have hdc : f * d = c := congrArg Prod.snd hd
    have hda : h * d = a := by
      have hz : f * (h * d - a) = 0 := by
        rw [← hdc] at h₂
        linear_combination -h₂
      exact sub_eq_zero.mp (mem_nonZeroDivisors_iff_left.mp hf _ hz)
    exact ⟨d, Prod.ext hda (Prod.ext hdb hdc)⟩

theorem pointCartierYoneda_last_exact {f g h : R} (hf : f ∈ R⁰)
    (hg : Ideal.Quotient.mk (Ideal.span {f}) g ∈ (R ⧸ Ideal.span {f})⁰)
    (hh : ∀ x : R, h * x ∈ Ideal.span ({f, g} : Set R) →
      x ∈ Ideal.span ({f, g} : Set R)) :
    LinearMap.range (threeGeneratorMiddle f g h) =
      LinearMap.ker (threeGeneratorLast f g h) := by
  apply le_antisymm
  · exact LinearMap.range_le_ker_iff.mpr (threeGenerator_last_comp_middle f g h)
  · rintro ⟨x, y, z⟩ hxyz
    change f * x + g * y + h * z = 0 at hxyz
    have hhz : h * z ∈ Ideal.span ({f, g} : Set R) := by
      rw [← twoGeneratorLast_range]
      refine ⟨(-x, -y), ?_⟩
      change f * -x + g * -y = h * z
      linear_combination -hxyz
    have hz := hh z hhz
    rw [← twoGeneratorLast_range] at hz
    obtain ⟨⟨b, c⟩, hbc⟩ := hz
    change f * b + g * c = z at hbc
    have hsyzygy : (x + h * b, y + h * c) ∈
        LinearMap.ker (twoGeneratorLast f g) := by
      change f * (x + h * b) + g * (y + h * c) = 0
      rw [← hbc] at hxyz
      linear_combination hxyz
    rw [← twoGenerator_exact_of_regular hf hg] at hsyzygy
    obtain ⟨a, ha⟩ := hsyzygy
    have ha₁ : -g * a = x + h * b := congrArg Prod.fst ha
    have ha₂ : f * a = y + h * c := congrArg Prod.snd ha
    refine ⟨(a, b, c), ?_⟩
    apply Prod.ext
    · change -g * a - h * b = x
      linear_combination ha₁
    · apply Prod.ext
      · change f * a - h * c = y
        linear_combination ha₂
      · exact hbc

end PfaffianDescent
