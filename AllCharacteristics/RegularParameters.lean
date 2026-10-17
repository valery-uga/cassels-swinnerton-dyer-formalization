import AllCharacteristics.RegularLocalLowDimension
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.LocalRing.Quotient

/-!
# Regular parameters and their quotients

These lemmas supply the parameter step in the higher-dimensional regular-local
specialization argument. We work with Mathlib's cotangent space and numerical
definition of regularity, without assuming the quotient is regular.
-/

namespace AllCharacteristics
open IsLocalRing Module

section Local
variable {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- Any element of `m` outside `m²` belongs to a generating set of `m` of
minimal cardinality. The proof extends its cotangent vector to a basis and
lifts that basis, fixing the specified element. -/
theorem exists_minimal_generators_containing (x : R)
    (hx : x ∈ maximalIdeal R) (hx₂ : x ∉ maximalIdeal R ^ 2) :
    ∃ s : Finset R, x ∈ s ∧ s.card = (maximalIdeal R).spanFinrank ∧
      Ideal.span (s : Set R) = maximalIdeal R := by
  classical
  let z : maximalIdeal R := ⟨x, hx⟩
  let q := (maximalIdeal R).toCotangent
  have hz : q z ≠ 0 := fun h => hx₂ (((maximalIdeal R).toCotangent_eq_zero z).mp h)
  have hs : LinearIndepOn (ResidueField R) id {q z} :=
    (linearIndepOn_singleton_iff (ResidueField R)).mpr hz
  let I := hs.extend (Set.subset_univ _)
  let b : Basis I (ResidueField R) (CotangentSpace R) := Basis.extend hs
  let i₀ : I := ⟨q z, hs.subset_extend (Set.subset_univ _) (Set.mem_singleton _)⟩
  let : Fintype I := FiniteDimensional.fintypeBasisIndex b
  choose v hv using fun i : I => (maximalIdeal R).toCotangent_surjective (b i)
  let w : I → maximalIdeal R := fun i => if i = i₀ then z else v i
  have hw₀ : w i₀ = z := by simp [w]
  have hqw : ∀ i, q (w i) = b i := by
    intro i
    by_cases hi : i = i₀
    · subst i
      rw [hw₀]
      exact (Basis.extend_apply_self hs i₀).symm
    · simpa only [w, if_neg hi] using hv i
  have hwinj : Function.Injective w := by
    intro i j hij
    apply b.injective
    rw [← hqw i, ← hqw j, hij]
  let wR : I → R := fun i => (w i : R)
  have hwRinj : Function.Injective wR := by
    intro i j hij
    exact hwinj (Subtype.ext hij)
  have hspan : Submodule.span R (Set.range w) = ⊤ := by
    apply CotangentSpace.span_image_eq_top_iff.mp
    rw [← Set.range_comp, show q ∘ w = ⇑b from funext hqw]
    exact b.span_eq
  have hspanR : Ideal.span (Set.range wR) = maximalIdeal R := by
    have hh := congrArg (Submodule.map (maximalIdeal R).subtype) hspan
    rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top,
      Submodule.range_subtype] at hh
    exact hh
  let s : Finset R := Finset.univ.image wR
  refine ⟨s, ?_, ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨i₀, Finset.mem_univ _, by simp [wR, hw₀, z]⟩
  · rw [Finset.card_image_of_injective _ hwRinj, Finset.card_univ,
      ← finrank_eq_card_basis b, ← spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]
  · simpa only [s, Finset.coe_image, Finset.coe_univ, Set.image_univ] using hspanR


/-- Killing a minimal generator decreases the number of generators of the
image maximal ideal by at least one. -/
theorem parameter_quotient_embedding_dimension_bound (x : R)
    (hx : x ∈ maximalIdeal R) (hx₂ : x ∉ maximalIdeal R ^ 2) :
    ((maximalIdeal R).map (Ideal.Quotient.mk (Ideal.span {x}))).spanFinrank + 1 ≤
      (maximalIdeal R).spanFinrank := by
  classical
  obtain ⟨s, hxs, hcard, hspan⟩ := exists_minimal_generators_containing x hx hx₂
  let f := Ideal.Quotient.mk (Ideal.span {x})
  have hfx : f x = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
  have himage : (maximalIdeal R).map f = Ideal.span (f '' (s.erase x : Set R)) := by
    rw [← hspan, Ideal.map_span]
    conv_lhs => rw [← Finset.insert_erase hxs]
    simp only [Finset.coe_insert, Set.image_insert_eq, hfx, Ideal.span_insert,
      Ideal.span_singleton_zero, bot_sup_eq]
  have hbound : ((maximalIdeal R).map f).spanFinrank ≤ (s.erase x).card := by
    rw [himage]
    calc
      (Ideal.span (f '' (s.erase x : Set R))).spanFinrank ≤
          (f '' (s.erase x : Set R)).ncard :=
        Submodule.spanFinrank_span_le_ncard_of_finite ((s.erase x).finite_toSet.image f)
      _ ≤ (s.erase x : Set R).ncard := Set.ncard_image_le (s.erase x).finite_toSet
      _ = (s.erase x).card := Set.ncard_coe_finset _
  have he := Finset.card_erase_add_one hxs
  change ((maximalIdeal R).map f).spanFinrank + 1 ≤ (maximalIdeal R).spanFinrank
  omega

/-- The principal-ideal dimension inequality for an element of the maximal ideal. -/
theorem ringKrullDim_le_parameter_quotient_add_one (x : R) (hx : x ∈ maximalIdeal R) :
    ringKrullDim R ≤ ringKrullDim (R ⧸ Ideal.span {x}) + 1 := by
  have h := ringKrullDim_le_ringKrullDim_quotient_add_card (R := R) {x} (by
    rw [Finset.coe_singleton, Set.singleton_subset_iff,
      IsLocalRing.ringJacobson_eq_maximalIdeal]
    exact hx)
  rw [Finset.coe_singleton, Finset.card_singleton, Nat.cast_one] at h
  exact h

end Local

section Regular
variable {R : Type*} [CommRing R] [IsRegularLocalRing R]

/-- Quotienting a regular local ring by an element of `m` outside `m²`
produces a regular local ring. The conclusion is derived from generator and
Krull-dimension inequalities, without assuming the original ring is a domain. -/
theorem isRegularLocalRing_quotient_parameter
    (x : R) (hx : x ∈ maximalIdeal R) (hx₂ : x ∉ maximalIdeal R ^ 2) :
    IsRegularLocalRing (R ⧸ Ideal.span {x}) := by
  have hp : Ideal.span {x} ≠ ⊤ :=
    ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top
      (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hx))
  have : Nontrivial (R ⧸ Ideal.span {x}) := Ideal.Quotient.nontrivial_iff.mpr hp
  have := IsLocalRing.of_surjective' (Ideal.Quotient.mk (Ideal.span {x}))
    Ideal.Quotient.mk_surjective
  have hb := parameter_quotient_embedding_dimension_bound x hx hx₂
  rw [map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective] at hb
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  apply ENat.WithBot.add_le_add_one_right_iff.mp
  calc
    ((maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank : WithBot ℕ∞) + 1 ≤
        (maximalIdeal R).spanFinrank := by exact_mod_cast hb
    _ = ringKrullDim R := IsRegularLocalRing.spanFinrank_maximalIdeal
    _ ≤ ringKrullDim (R ⧸ Ideal.span {x}) + 1 :=
      ringKrullDim_le_parameter_quotient_add_one x hx

/-- Killing a regular parameter decreases the Krull dimension by exactly one. -/
theorem ringKrullDim_quotient_parameter_add_one
    (x : R) (hx : x ∈ maximalIdeal R) (hx₂ : x ∉ maximalIdeal R ^ 2) :
    ringKrullDim (R ⧸ Ideal.span {x}) + 1 = ringKrullDim R := by
  have := isRegularLocalRing_quotient_parameter x hx hx₂
  have hb := parameter_quotient_embedding_dimension_bound x hx hx₂
  rw [map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective] at hb
  apply le_antisymm
  · rw [← IsRegularLocalRing.spanFinrank_maximalIdeal (R := R),
      ← IsRegularLocalRing.spanFinrank_maximalIdeal (R := R ⧸ Ideal.span {x})]
    exact_mod_cast hb
  · exact ringKrullDim_le_parameter_quotient_add_one x hx

end Regular
end AllCharacteristics
