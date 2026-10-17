import PfaffianDescent.ThreeGeneratorKoszul
import PfaffianDescent.HomogeneousProjection
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# Homogeneous pieces of the three-generator Koszul complex
-/

namespace PfaffianDescent

open MvPolynomial

section
variable {K : Type*} [Field K] {a b c : ℕ}

abbrev FourHomogeneous (K : Type*) [Field K] (d : ℕ) :=
  homogeneousSubmodule (Fin 4) K d

/-- The first differential in homogeneous degree `d + a + b + c`. -/
noncomputable def threeGeneratorGradedFirst
    (f g h : MvPolynomial (Fin 4) K)
    (hf : f.IsHomogeneous a) (hg : g.IsHomogeneous b)
    (hh : h.IsHomogeneous c) (d : ℕ) :
    FourHomogeneous K d →ₗ[K]
      FourHomogeneous K (d + c) ×
        FourHomogeneous K (d + b) × FourHomogeneous K (d + a) where
  toFun x :=
    (⟨h * x.val, by
        change (h * x.val).IsHomogeneous (d + c)
        simpa only [Nat.add_comm] using hh.mul x.property⟩,
      ⟨-g * x.val, by
        change (-g * x.val).IsHomogeneous (d + b)
        simpa only [Nat.add_comm] using hg.neg.mul x.property⟩,
      ⟨f * x.val, by
        change (f * x.val).IsHomogeneous (d + a)
        simpa only [Nat.add_comm] using hf.mul x.property⟩)
  map_add' x y := by
    apply Prod.ext
    · apply Subtype.ext
      simp [mul_add]
    · apply Prod.ext <;> apply Subtype.ext <;> simp [mul_add]
  map_smul' r x := by
    apply Prod.ext
    · apply Subtype.ext
      simp [mul_smul_comm]
    · apply Prod.ext <;> apply Subtype.ext <;> simp [mul_smul_comm]

/-- The middle differential in homogeneous degree `d + a + b + c`. -/
noncomputable def threeGeneratorGradedMiddle
    (f g h : MvPolynomial (Fin 4) K)
    (hf : f.IsHomogeneous a) (hg : g.IsHomogeneous b)
    (hh : h.IsHomogeneous c) (d : ℕ) :
    (FourHomogeneous K (d + c) ×
      FourHomogeneous K (d + b) × FourHomogeneous K (d + a)) →ₗ[K]
      FourHomogeneous K (d + b + c) ×
        FourHomogeneous K (d + a + c) × FourHomogeneous K (d + a + b) where
  toFun x :=
    (⟨-g * x.1.val - h * x.2.1.val, by
        apply IsHomogeneous.sub
        · simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            hg.neg.mul x.1.property
        · simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            hh.mul x.2.1.property⟩,
      ⟨f * x.1.val - h * x.2.2.val, by
        apply IsHomogeneous.sub
        · simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            hf.mul x.1.property
        · simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            hh.mul x.2.2.property⟩,
      ⟨f * x.2.1.val + g * x.2.2.val, by
        apply IsHomogeneous.add
        · simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            hf.mul x.2.1.property
        · simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            hg.mul x.2.2.property⟩)
  map_add' x y := by
    apply Prod.ext
    · apply Subtype.ext
      simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add]
      ring
    · apply Prod.ext
      · apply Subtype.ext
        simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add]
        ring
      · apply Subtype.ext
        simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add]
        ring
  map_smul' r x := by
    apply Prod.ext
    · apply Subtype.ext
      simp only [Prod.smul_fst, Prod.smul_snd, SetLike.val_smul,
        RingHom.id_apply, mul_smul_comm, smul_sub]
    · apply Prod.ext
      · apply Subtype.ext
        simp only [Prod.smul_fst, Prod.smul_snd, SetLike.val_smul,
          RingHom.id_apply, mul_smul_comm, smul_sub]
      · apply Subtype.ext
        simp only [Prod.smul_fst, Prod.smul_snd, SetLike.val_smul,
          RingHom.id_apply, mul_smul_comm, smul_add]

/-- The last differential in homogeneous degree `d + a + b + c`. -/
noncomputable def threeGeneratorGradedLast
    (f g h : MvPolynomial (Fin 4) K)
    (hf : f.IsHomogeneous a) (hg : g.IsHomogeneous b)
    (hh : h.IsHomogeneous c) (d : ℕ) :
    (FourHomogeneous K (d + b + c) ×
      FourHomogeneous K (d + a + c) × FourHomogeneous K (d + a + b)) →ₗ[K]
      FourHomogeneous K (d + a + b + c) where
  toFun x := ⟨f * x.1.val + g * x.2.1.val + h * x.2.2.val, by
    apply IsHomogeneous.add
    · apply IsHomogeneous.add
      · simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          hf.mul x.1.property
      · simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          hg.mul x.2.1.property
    · simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        hh.mul x.2.2.property⟩
  map_add' x y := by
    apply Subtype.ext
    simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add]
    ring
  map_smul' r x := by
    apply Subtype.ext
    simp only [Prod.smul_fst, Prod.smul_snd, SetLike.val_smul,
      RingHom.id_apply, mul_smul_comm, smul_add]

lemma threeGeneratorGradedFirst_injective
    (f g h : MvPolynomial (Fin 4) K)
    (hf : f.IsHomogeneous a) (hg : g.IsHomogeneous b)
    (hh : h.IsHomogeneous c) (hf0 : f ≠ 0) (d : ℕ) :
    Function.Injective (threeGeneratorGradedFirst f g h hf hg hh d) := by
  intro x y hxy
  apply Subtype.ext
  exact threeGeneratorFirst_injective hf0
    (congrArg (fun z ↦ (z.1.val, z.2.1.val, z.2.2.val)) hxy)

/-- Exactness at the last term, restricted to the appropriate homogeneous
pieces. -/
theorem threeGeneratorGraded_exact_last
    (f g h : MvPolynomial (Fin 4) K)
    (hf : f.IsHomogeneous a) (hg : g.IsHomogeneous b)
    (hh : h.IsHomogeneous c) (hf0 : f ≠ 0) (hrel : IsRelPrime f g)
    (hregular : ∀ x : MvPolynomial (Fin 4) K,
      h * x ∈ Ideal.span ({f, g} : Set (MvPolynomial (Fin 4) K)) →
        x ∈ Ideal.span ({f, g} : Set (MvPolynomial (Fin 4) K)))
    (d : ℕ) :
    LinearMap.range (threeGeneratorGradedMiddle f g h hf hg hh d) =
      LinearMap.ker (threeGeneratorGradedLast f g h hf hg hh d) := by
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    apply Subtype.ext
    change (threeGeneratorLast f g h)
      ((threeGeneratorMiddle f g h) (x.1.val, x.2.1.val, x.2.2.val)) = 0
    exact LinearMap.congr_fun (threeGenerator_last_comp_middle f g h) _
  · intro x hx
    have hx' : (x.1.val, x.2.1.val, x.2.2.val) ∈
        LinearMap.ker (threeGeneratorLast f g h) := congrArg Subtype.val hx
    rw [← threeGenerator_exact_last hf0 hrel hregular] at hx'
    obtain ⟨⟨r, s, t⟩, hrs⟩ := hx'
    have hrs₁ : -g * r - h * s = x.1.val := congrArg Prod.fst hrs
    have hrs₂ : f * r - h * t = x.2.1.val :=
      congrArg (fun z : _ × _ × _ ↦ z.2.1) hrs
    have hrs₃ : f * s + g * t = x.2.2.val :=
      congrArg (fun z : _ × _ × _ ↦ z.2.2) hrs
    let r' := homogeneousComponent (d + c) r
    let s' := homogeneousComponent (d + b) s
    let t' := homogeneousComponent (d + a) t
    refine ⟨(⟨r', homogeneousComponent_isHomogeneous _ _⟩,
      ⟨s', homogeneousComponent_isHomogeneous _ _⟩,
      ⟨t', homogeneousComponent_isHomogeneous _ _⟩), ?_⟩
    apply Prod.ext
    · apply Subtype.ext
      change -g * r' - h * s' = x.1.val
      have hgr : homogeneousComponent (d + b + c) (-g * r) = -g * r' := by
        change homogeneousComponent (d + b + c) ((-g) * r) = _
        rw [show d + b + c = b + (d + c) by omega]
        exact homogeneousComponent_mul_left (q := r) hg.neg (d + c)
      have hhs : homogeneousComponent (d + b + c) (h * s) = h * s' := by
        rw [show d + b + c = c + (d + b) by omega]
        exact homogeneousComponent_mul_left (q := s) hh (d + b)
      rw [← hgr, ← hhs, ← map_sub, hrs₁,
        homogeneousComponent_eq_self x.1.property]
    · apply Prod.ext
      · apply Subtype.ext
        change f * r' - h * t' = x.2.1.val
        have hfr : homogeneousComponent (d + a + c) (f * r) = f * r' := by
          rw [show d + a + c = a + (d + c) by omega]
          exact homogeneousComponent_mul_left (q := r) hf (d + c)
        have hht : homogeneousComponent (d + a + c) (h * t) = h * t' := by
          rw [show d + a + c = c + (d + a) by omega]
          exact homogeneousComponent_mul_left (q := t) hh (d + a)
        rw [← hfr, ← hht, ← map_sub, hrs₂,
          homogeneousComponent_eq_self x.2.1.property]
      · apply Subtype.ext
        change f * s' + g * t' = x.2.2.val
        have hfs : homogeneousComponent (d + a + b) (f * s) = f * s' := by
          rw [show d + a + b = a + (d + b) by omega]
          exact homogeneousComponent_mul_left (q := s) hf (d + b)
        have hgt : homogeneousComponent (d + a + b) (g * t) = g * t' := by
          rw [show d + a + b = b + (d + a) by omega]
          exact homogeneousComponent_mul_left (q := t) hg (d + a)
        rw [← hfs, ← hgt, ← map_add, hrs₃,
          homogeneousComponent_eq_self x.2.2.property]

/-- Exactness at the middle term, restricted to homogeneous pieces. -/
theorem threeGeneratorGraded_exact_middle
    (f g h : MvPolynomial (Fin 4) K)
    (hf : f.IsHomogeneous a) (hg : g.IsHomogeneous b)
    (hh : h.IsHomogeneous c) (hg0 : g ≠ 0) (hf0 : f ≠ 0)
    (hrel : IsRelPrime f g) (d : ℕ) :
    LinearMap.range (threeGeneratorGradedFirst f g h hf hg hh d) =
      LinearMap.ker (threeGeneratorGradedMiddle f g h hf hg hh d) := by
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    have hz := LinearMap.congr_fun (threeGenerator_middle_comp_first f g h) x.val
    exact Prod.ext (Subtype.ext (congrArg Prod.fst hz))
      (Prod.ext
        (Subtype.ext (congrArg (fun z : _ × _ × _ ↦ z.2.1) hz))
        (Subtype.ext (congrArg (fun z : _ × _ × _ ↦ z.2.2) hz)))
  · intro x hx
    have hx' : (x.1.val, x.2.1.val, x.2.2.val) ∈
        LinearMap.ker (threeGeneratorMiddle f g h) := by
      exact Prod.ext (congrArg Subtype.val (congrArg Prod.fst hx))
        (Prod.ext
          (congrArg Subtype.val (congrArg (fun z ↦ z.2.1) hx))
          (congrArg Subtype.val (congrArg (fun z ↦ z.2.2) hx)))
    rw [← threeGenerator_exact_middle hg0 hf0 hrel] at hx'
    obtain ⟨r, hr⟩ := hx'
    have hfr : f * r = x.2.2.val := congrArg (fun z : _ × _ × _ ↦ z.2.2) hr
    have hrh : r.IsHomogeneous d := homogeneous_of_mul_right hf hf0 (by
      rw [mul_comm r f, hfr]
      exact x.2.2.property)
    exact ⟨⟨r, hrh⟩, Prod.ext
      (Subtype.ext (congrArg Prod.fst hr))
      (Prod.ext
        (Subtype.ext (congrArg (fun z : _ × _ × _ ↦ z.2.1) hr))
        (Subtype.ext hfr))⟩

end

end PfaffianDescent
