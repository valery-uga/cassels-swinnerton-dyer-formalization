import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.RingTheory.Ideal.Quotient.Operations
import PfaffianDescent.CompleteIntersectionSocleExt
import PfaffianDescent.CompleteIntersectionSocleHom
import PfaffianDescent.ThreeGeneratorKoszul

/-!
# Short exact sequences from the three-generator Koszul complex

The elementary exactness results for the three-generator Koszul complex are
packaged here as three short exact sequences of modules.  This is the form
needed by the Ext calculation that proves the complete-intersection quotient
has no irrelevant socle.
-/

namespace PfaffianDescent

open CategoryTheory Abelian

section

variable {R : Type*} [CommRing R] [IsDomain R] [DecompositionMonoid R]

/-- The left-hand short exact sequence in the three-generator Koszul
resolution. -/
lemma threeGenerator_first_shortExact {f g h : R}
    (hf : f ≠ 0) (hg : g ≠ 0) (hrel : IsRelPrime f g) :
    let α := threeGeneratorFirst f g h
    let β := threeGeneratorMiddle f g h
    let βr := β.rangeRestrict
    (ModuleCat.shortComplexOfCompEqZero α βr (by
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      change ((βr.comp α) x : R × R × R) = 0
      change β (α x) = 0
      exact LinearMap.congr_fun (threeGenerator_middle_comp_first f g h) x)).ShortExact := by
  dsimp
  apply ModuleCat.shortComplex_shortExact
  · change Function.Exact (threeGeneratorFirst f g h)
      (threeGeneratorMiddle f g h).rangeRestrict
    rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict,
      ← threeGenerator_exact_middle hg hf hrel]
  · exact threeGeneratorFirst_injective hf
  · rintro ⟨y, ⟨x, hx⟩⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    exact hx

/-- The middle short exact sequence in the three-generator Koszul
resolution. -/
lemma threeGenerator_second_shortExact {f g h : R}
    (hf : f ≠ 0) (hrel : IsRelPrime f g)
    (hregular : ∀ a : R,
      h * a ∈ Ideal.span ({f, g} : Set R) →
        a ∈ Ideal.span ({f, g} : Set R)) :
    let β := threeGeneratorMiddle f g h
    let γ := threeGeneratorLast f g h
    let βi := β.range.subtype
    let γr := γ.rangeRestrict
    (ModuleCat.shortComplexOfCompEqZero βi γr (by
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      change γ (x : R × R × R) = 0
      rcases x.property with ⟨y, hy⟩
      rw [← hy]
      exact LinearMap.congr_fun (threeGenerator_last_comp_middle f g h) y)).ShortExact := by
  dsimp
  apply ModuleCat.shortComplex_shortExact
  · change Function.Exact (threeGeneratorMiddle f g h).range.subtype
      (threeGeneratorLast f g h).rangeRestrict
    rw [LinearMap.exact_iff, Submodule.range_subtype,
      LinearMap.ker_rangeRestrict, ← threeGenerator_exact_last hf hrel hregular]
  · exact (threeGeneratorMiddle f g h).range.injective_subtype
  · rintro ⟨y, ⟨x, hx⟩⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    exact hx

/-- The quotient short exact sequence at the end of the three-generator
Koszul resolution. -/
lemma threeGenerator_third_shortExact (f g h : R) :
    let γ := threeGeneratorLast f g h
    let I := Ideal.span ({f, g, h} : Set R)
    let γi := γ.range.subtype
    let q := (Ideal.Quotient.mkₐ R I).toLinearMap
    (ModuleCat.shortComplexOfCompEqZero γi q (by
      apply LinearMap.ext
      intro x
      change Ideal.Quotient.mk I (x : R) = 0
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      change (x : R) ∈ Ideal.span ({f, g, h} : Set R)
      rw [← threeGeneratorLast_range]
      exact x.property)).ShortExact := by
  dsimp
  apply ModuleCat.shortComplex_shortExact
  · change Function.Exact (threeGeneratorLast f g h).range.subtype
      (Ideal.Quotient.mkₐ R (Ideal.span ({f, g, h} : Set R))).toLinearMap
    rw [LinearMap.exact_iff, Submodule.range_subtype]
    apply le_antisymm
    · intro x hx
      change Ideal.Quotient.mk (Ideal.span ({f, g, h} : Set R)) x = 0 at hx
      have hmem : x ∈ Ideal.span ({f, g, h} : Set R) :=
        Ideal.Quotient.eq_zero_iff_mem.mp hx
      rw [threeGeneratorLast_range]
      exact hmem
    · intro x hx
      change Ideal.Quotient.mk (Ideal.span ({f, g, h} : Set R)) x = 0
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      rw [← threeGeneratorLast_range]
      exact hx
  · exact (threeGeneratorLast f g h).range.injective_subtype
  · exact Ideal.Quotient.mkₐ_surjective R _

/-- Dimension shifting along the three Koszul short exact sequences.  Once
the four corresponding Ext groups of the free terms vanish, the quotient by
the three equations has vanishing degree-zero Ext against `X`. -/
lemma threeGenerator_quotient_ext_subsingleton
    [HasExt (ModuleCat R)] {X : ModuleCat R} {f g h : R}
    (hf : f ≠ 0) (hg : g ≠ 0) (hrel : IsRelPrime f g)
    (hregular : ∀ a : R,
      h * a ∈ Ideal.span ({f, g} : Set R) →
        a ∈ Ideal.span ({f, g} : Set R))
    [Subsingleton (Ext X (ModuleCat.of R R) 3)]
    [Subsingleton (Ext X (ModuleCat.of R (R × R × R)) 2)]
    [Subsingleton (Ext X (ModuleCat.of R (R × R × R)) 1)]
    [Subsingleton (Ext X (ModuleCat.of R R) 0)] :
    Subsingleton (Ext X
      (ModuleCat.of R (R ⧸ Ideal.span ({f, g, h} : Set R))) 0) := by
  let α := threeGeneratorFirst f g h
  let β := threeGeneratorMiddle f g h
  let γ := threeGeneratorLast f g h
  let I := Ideal.span ({f, g, h} : Set R)
  let S₀ := ModuleCat.shortComplexOfCompEqZero α β.rangeRestrict (by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change ((β.rangeRestrict.comp α) x : R × R × R) = 0
    change β (α x) = 0
    exact LinearMap.congr_fun (threeGenerator_middle_comp_first f g h) x)
  let S₁ := ModuleCat.shortComplexOfCompEqZero β.range.subtype γ.rangeRestrict (by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change γ (x : R × R × R) = 0
    rcases x.property with ⟨y, hy⟩
    rw [← hy]
    exact LinearMap.congr_fun (threeGenerator_last_comp_middle f g h) y)
  let S₂ := ModuleCat.shortComplexOfCompEqZero γ.range.subtype
    (Ideal.Quotient.mkₐ R I).toLinearMap (by
      apply LinearMap.ext
      intro x
      change Ideal.Quotient.mk I (x : R) = 0
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      change (x : R) ∈ Ideal.span ({f, g, h} : Set R)
      rw [← threeGeneratorLast_range]
      exact x.property)
  have hS₀ : S₀.ShortExact := by
    dsimp [S₀, α, β]
    exact threeGenerator_first_shortExact hf hg hrel
  have hS₁ : S₁.ShortExact := by
    dsimp [S₁, β, γ]
    exact threeGenerator_second_shortExact hf hrel hregular
  have hS₂ : S₂.ShortExact := by
    dsimp [S₂, γ, I]
    exact threeGenerator_third_shortExact f g h
  letI : Subsingleton (Ext X S₀.X₃ 2) :=
    ext_subsingleton_X3_of_shortExact hS₀ 2
  letI : Subsingleton (Ext X S₁.X₃ 1) :=
    ext_subsingleton_X3_of_shortExact hS₁ 1
  exact ext_subsingleton_X3_of_shortExact hS₂ 0

/-- The Ext dimension shift rules out common annihilators by an ideal `J`
once its four free-term Ext groups vanish.  Taking `J` to be the homogeneous
coordinate ideal gives the no-irrelevant-socle statement needed for projective
saturation. -/
lemma threeGenerator_quotient_no_common_annihilator_of_ext_vanishing
    [HasExt (ModuleCat R)] {J : Ideal R} {f g h : R}
    (hf : f ≠ 0) (hg : g ≠ 0) (hrel : IsRelPrime f g)
    (hregular : ∀ a : R,
      h * a ∈ Ideal.span ({f, g} : Set R) →
        a ∈ Ideal.span ({f, g} : Set R))
    [Subsingleton (Ext (ModuleCat.of R (R ⧸ J)) (ModuleCat.of R R) 3)]
    [Subsingleton (Ext (ModuleCat.of R (R ⧸ J))
      (ModuleCat.of R (R × R × R)) 2)]
    [Subsingleton (Ext (ModuleCat.of R (R ⧸ J))
      (ModuleCat.of R (R × R × R)) 1)]
    [Subsingleton (Ext (ModuleCat.of R (R ⧸ J)) (ModuleCat.of R R) 0)]
    (x : R ⧸ Ideal.span ({f, g, h} : Set R))
    (hx : ∀ r ∈ J,
      Ideal.Quotient.mk (Ideal.span ({f, g, h} : Set R)) r * x = 0) :
    x = 0 := by
  letI : Subsingleton (Ext (ModuleCat.of R (R ⧸ J))
      (ModuleCat.of R (R ⧸ Ideal.span ({f, g, h} : Set R))) 0) :=
    threeGenerator_quotient_ext_subsingleton hf hg hrel hregular
  have hHom : Subsingleton
      (ModuleCat.of R (R ⧸ J) ⟶
        ModuleCat.of R (R ⧸ Ideal.span ({f, g, h} : Set R))) :=
    Ext.homEquiv₀.symm.injective.subsingleton
  exact quotient_no_common_annihilator_of_hom_subsingleton hHom x hx

end

end PfaffianDescent
