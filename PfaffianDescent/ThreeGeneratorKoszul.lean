import PfaffianDescent.TwoGeneratorKoszul

/-!
# The three-generator Koszul complex

This is the elementary algebraic complex used for the two complete
intersections in Voisin's argument.  We state the last regularity condition
without any local-algebra shorthand: multiplication by `h` is injective
modulo `(f,g)`.  This makes the geometric obligation attached to the third
equation completely explicit.
-/

namespace PfaffianDescent

section
variable {R : Type*} [CommRing R]

/-- The degree-three-to-degree-two Koszul differential for `f,g,h`. -/
def threeGeneratorFirst (f g h : R) : R →ₗ[R] R × R × R where
  toFun a := (h * a, -g * a, f * a)
  map_add' a b := by ext <;> simp [mul_add]
  map_smul' r a := by ext <;> simp [mul_left_comm, mul_comm]

/-- The middle Koszul differential for `f,g,h`. -/
def threeGeneratorMiddle (f g h : R) : R × R × R →ₗ[R] R × R × R where
  toFun v := (-g * v.1 - h * v.2.1,
    f * v.1 - h * v.2.2, f * v.2.1 + g * v.2.2)
  map_add' a b := by
    ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring
  map_smul' r a := by
    ext <;> simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply] <;> ring

/-- The Koszul differential whose range is the ideal `(f,g,h)`. -/
def threeGeneratorLast (f g h : R) : R × R × R →ₗ[R] R where
  toFun v := f * v.1 + g * v.2.1 + h * v.2.2
  map_add' a b := by simp only [Prod.fst_add, Prod.snd_add]; ring
  map_smul' r a := by
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply]; ring

lemma threeGenerator_middle_comp_first (f g h : R) :
    (threeGeneratorMiddle f g h).comp (threeGeneratorFirst f g h) = 0 := by
  apply LinearMap.ext
  intro a
  apply Prod.ext
  · change -g * (h * a) - h * (-g * a) = 0
    ring
  · apply Prod.ext
    · change f * (h * a) - h * (f * a) = 0
      ring
    · change f * (-g * a) + g * (f * a) = 0
      ring

lemma threeGenerator_last_comp_middle (f g h : R) :
    (threeGeneratorLast f g h).comp (threeGeneratorMiddle f g h) = 0 := by
  apply LinearMap.ext
  intro a
  change f * (-g * a.1 - h * a.2.1) +
    g * (f * a.1 - h * a.2.2) + h * (f * a.2.1 + g * a.2.2) = 0
  ring

lemma threeGeneratorLast_range (f g h : R) :
    LinearMap.range (threeGeneratorLast f g h) =
      Ideal.span ({f, g, h} : Set R) := by
  apply le_antisymm
  · rintro x ⟨⟨a, b, c⟩, rfl⟩
    change f * a + g * b + h * c ∈ Ideal.span ({f, g, h} : Set R)
    exact Ideal.add_mem _
      (Ideal.add_mem _
        (Ideal.mul_mem_right a _ (Ideal.subset_span (by simp)))
        (Ideal.mul_mem_right b _ (Ideal.subset_span (by simp))))
      (Ideal.mul_mem_right c _ (Ideal.subset_span (by simp)))
  · apply Ideal.span_le.mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨(1, 0, 0), by simp [threeGeneratorLast]⟩
    · exact ⟨(0, 1, 0), by simp [threeGeneratorLast]⟩
    · exact ⟨(0, 0, 1), by simp [threeGeneratorLast]⟩

variable [IsDomain R] [DecompositionMonoid R]

lemma threeGeneratorFirst_injective {f g h : R} (hf : f ≠ 0) :
    Function.Injective (threeGeneratorFirst f g h) := by
  intro a b hab
  exact mul_left_cancel₀ hf (congrArg (fun v : R × R × R ↦ v.2.2) hab)

/-- Exactness at the last nontrivial term.  The hypotheses say that `f,g`
are relatively prime and that `h` is a non-zero-divisor modulo `(f,g)`. -/
theorem threeGenerator_exact_last {f g h : R}
    (hf : f ≠ 0) (hrel : IsRelPrime f g)
    (hregular : ∀ a : R,
      h * a ∈ Ideal.span ({f, g} : Set R) →
        a ∈ Ideal.span ({f, g} : Set R)) :
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
    have hz := hregular z hhz
    rw [← twoGeneratorLast_range] at hz
    obtain ⟨⟨b, c⟩, hbc⟩ := hz
    change f * b + g * c = z at hbc
    have hsyzygy : (x + h * b, y + h * c) ∈
        LinearMap.ker (twoGeneratorLast f g) := by
      change f * (x + h * b) + g * (y + h * c) = 0
      rw [← hbc] at hxyz
      linear_combination hxyz
    rw [← twoGenerator_exact hf hrel] at hsyzygy
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

/-- Exactness at the middle term of the three-generator Koszul complex. -/
theorem threeGenerator_exact_middle {f g h : R}
    (hg : g ≠ 0) (hf : f ≠ 0) (hrel : IsRelPrime f g) :
    LinearMap.range (threeGeneratorFirst f g h) =
      LinearMap.ker (threeGeneratorMiddle f g h) := by
  apply le_antisymm
  · exact LinearMap.range_le_ker_iff.mpr (threeGenerator_middle_comp_first f g h)
  · rintro ⟨a, b, c⟩ habc
    have h₁ : -g * a - h * b = 0 := congrArg Prod.fst habc
    have h₂ : f * a - h * c = 0 := congrArg (fun v : R × R × R ↦ v.2.1) habc
    have h₃ : f * b + g * c = 0 := congrArg (fun v : R × R × R ↦ v.2.2) habc
    have hbc : (b, c) ∈ LinearMap.ker (twoGeneratorLast f g) := h₃
    rw [← twoGenerator_exact hf hrel] at hbc
    obtain ⟨d, hd⟩ := hbc
    have hdb : -g * d = b := congrArg Prod.fst hd
    have hdc : f * d = c := congrArg Prod.snd hd
    have hda : h * d = a := by
      apply mul_left_cancel₀ hg
      rw [← hdb] at h₁
      linear_combination h₁
    refine ⟨d, ?_⟩
    exact Prod.ext hda (Prod.ext hdb hdc)

end

end PfaffianDescent
