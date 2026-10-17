import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.RingTheory.Ideal.Quotient.Operations
import PfaffianDescent.CompleteIntersectionSocleExt
import PfaffianDescent.CompleteIntersectionSocleHom
import PfaffianDescent.TwoGeneratorKoszul

/-!
# Short exact sequences for a regular pair

A relatively prime pair in a domain has the two-term Koszul resolution.  This
file packages that resolution into short exact sequences and records the
corresponding two-step Ext shift.  It is the local algebra needed to exclude
zero-dimensional embedded components of a two-equation intersection.
-/

namespace PfaffianDescent

open CategoryTheory Abelian

section

variable {R : Type*} [CommRing R] [IsDomain R] [DecompositionMonoid R]

/-- The initial short exact sequence in the Koszul resolution of a relatively
prime pair. -/
lemma twoGenerator_first_shortExact {f g : R}
    (hf : f ≠ 0) (hrel : IsRelPrime f g) :
    let α := twoGeneratorFirst f g
    let β := twoGeneratorLast f g
    let βr := β.rangeRestrict
    (ModuleCat.shortComplexOfCompEqZero α βr (by
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      change ((βr.comp α) x : R) = 0
      change β (α x) = 0
      exact LinearMap.congr_fun (twoGenerator_comp_zero f g) x)).ShortExact := by
  dsimp
  apply ModuleCat.shortComplex_shortExact
  · change Function.Exact (twoGeneratorFirst f g)
      (twoGeneratorLast f g).rangeRestrict
    rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict,
      ← twoGenerator_exact hf hrel]
  · exact twoGeneratorFirst_injective hf
  · rintro ⟨y, ⟨x, hx⟩⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    exact hx

/-- The quotient short exact sequence at the end of the two-generator Koszul
resolution. -/
lemma twoGenerator_second_shortExact (f g : R) :
    let β := twoGeneratorLast f g
    let I := Ideal.span ({f, g} : Set R)
    let βi := β.range.subtype
    let q := (Ideal.Quotient.mkₐ R I).toLinearMap
    (ModuleCat.shortComplexOfCompEqZero βi q (by
      apply LinearMap.ext
      intro x
      change Ideal.Quotient.mk I (x : R) = 0
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      change (x : R) ∈ Ideal.span ({f, g} : Set R)
      rw [← twoGeneratorLast_range]
      exact x.property)).ShortExact := by
  dsimp
  apply ModuleCat.shortComplex_shortExact
  · change Function.Exact (twoGeneratorLast f g).range.subtype
      (Ideal.Quotient.mkₐ R (Ideal.span ({f, g} : Set R))).toLinearMap
    rw [LinearMap.exact_iff, Submodule.range_subtype]
    apply le_antisymm
    · intro x hx
      change Ideal.Quotient.mk (Ideal.span ({f, g} : Set R)) x = 0 at hx
      have hmem : x ∈ Ideal.span ({f, g} : Set R) :=
        Ideal.Quotient.eq_zero_iff_mem.mp hx
      rw [twoGeneratorLast_range]
      exact hmem
    · intro x hx
      change Ideal.Quotient.mk (Ideal.span ({f, g} : Set R)) x = 0
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      rw [← twoGeneratorLast_range]
      exact hx
  · exact (twoGeneratorLast f g).range.injective_subtype
  · exact Ideal.Quotient.mkₐ_surjective R _

/-- Dimension shifting along the two-generator Koszul resolution. -/
lemma twoGenerator_quotient_ext_subsingleton
    [HasExt (ModuleCat R)] {X : ModuleCat R} {f g : R}
    (hf : f ≠ 0) (hrel : IsRelPrime f g)
    [Subsingleton (Ext X (ModuleCat.of R R) 2)]
    [Subsingleton (Ext X (ModuleCat.of R (R × R)) 1)]
    [Subsingleton (Ext X (ModuleCat.of R R) 0)] :
    Subsingleton (Ext X
      (ModuleCat.of R (R ⧸ Ideal.span ({f, g} : Set R))) 0) := by
  let α := twoGeneratorFirst f g
  let β := twoGeneratorLast f g
  let I := Ideal.span ({f, g} : Set R)
  let S₀ := ModuleCat.shortComplexOfCompEqZero α β.rangeRestrict (by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change ((β.rangeRestrict.comp α) x : R) = 0
    change β (α x) = 0
    exact LinearMap.congr_fun (twoGenerator_comp_zero f g) x)
  let S₁ := ModuleCat.shortComplexOfCompEqZero β.range.subtype
    (Ideal.Quotient.mkₐ R I).toLinearMap (by
      apply LinearMap.ext
      intro x
      change Ideal.Quotient.mk I (x : R) = 0
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      change (x : R) ∈ Ideal.span ({f, g} : Set R)
      rw [← twoGeneratorLast_range]
      exact x.property)
  have hS₀ : S₀.ShortExact := by
    dsimp [S₀, α, β]
    exact twoGenerator_first_shortExact hf hrel
  have hS₁ : S₁.ShortExact := by
    dsimp [S₁, β, I]
    exact twoGenerator_second_shortExact f g
  letI : Subsingleton (Ext X S₀.X₃ 1) :=
    ext_subsingleton_X3_of_shortExact hS₀ 1
  exact ext_subsingleton_X3_of_shortExact hS₁ 0

/-- A regular pair has no common annihilator by an ideal whose first three
Ext groups into the ambient ring vanish. -/
lemma twoGenerator_quotient_no_common_annihilator_of_ext_vanishing
    [HasExt (ModuleCat R)] {J : Ideal R} {f g : R}
    (hf : f ≠ 0) (hrel : IsRelPrime f g)
    [Subsingleton (Ext (ModuleCat.of R (R ⧸ J)) (ModuleCat.of R R) 2)]
    [Subsingleton (Ext (ModuleCat.of R (R ⧸ J)) (ModuleCat.of R (R × R)) 1)]
    [Subsingleton (Ext (ModuleCat.of R (R ⧸ J)) (ModuleCat.of R R) 0)]
    (x : R ⧸ Ideal.span ({f, g} : Set R))
    (hx : ∀ r ∈ J, Ideal.Quotient.mk (Ideal.span ({f, g} : Set R)) r * x = 0) :
    x = 0 := by
  letI : Subsingleton (Ext (ModuleCat.of R (R ⧸ J))
      (ModuleCat.of R (R ⧸ Ideal.span ({f, g} : Set R))) 0) :=
    twoGenerator_quotient_ext_subsingleton hf hrel
  have hHom : Subsingleton
      (ModuleCat.of R (R ⧸ J) ⟶
        ModuleCat.of R (R ⧸ Ideal.span ({f, g} : Set R))) :=
    Ext.homEquiv₀.symm.injective.subsingleton
  exact quotient_no_common_annihilator_of_hom_subsingleton hHom x hx

end

end PfaffianDescent
