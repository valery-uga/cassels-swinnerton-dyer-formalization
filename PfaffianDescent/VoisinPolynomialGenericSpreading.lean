import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Clearing denominators in a generic polynomial family

A homogeneous ideal defining a divisor over a configuration function field
has finitely many polynomial generators.  Before those generators can be
spread over an open base, their coefficients must be cleared over one common
nonzero denominator.  This file supplies the coefficient-level step without
assuming the ideal or its Picard class descends to the ground field.
-/

namespace PfaffianDescent

open MvPolynomial

universe u v

/-- A polynomial over the fraction field of a domain becomes the image of a
polynomial over the domain after multiplication by one nonzero denominator. -/
theorem exists_polynomial_denominator_clear
    {A : Type u} {F : Type v} {σ : Type*}
    [CommRing A] [IsDomain A] [Field F] [Algebra A F]
    [IsFractionRing A F]
    (f : MvPolynomial σ F) :
    ∃ (d : A) (g : MvPolynomial σ A), d ≠ 0 ∧
      MvPolynomial.map (algebraMap A F) g =
        MvPolynomial.C (algebraMap A F d) * f := by
  classical
  induction f using MvPolynomial.induction_on with
  | C a =>
      obtain ⟨n, d, hd, ha⟩ := IsFractionRing.div_surjective A a
      refine ⟨d, MvPolynomial.C n, ?_, ?_⟩
      · exact mem_nonZeroDivisors_iff_ne_zero.mp hd
      · have hden : algebraMap A F d ≠ 0 := by
          simpa only [map_zero] using (IsFractionRing.injective A F).ne
            (mem_nonZeroDivisors_iff_ne_zero.mp hd)
        have hnum : algebraMap A F n = algebraMap A F d * a := by
          rw [mul_comm]
          exact (div_eq_iff hden).mp ha
        rw [MvPolynomial.map_C, ← MvPolynomial.C_mul, hnum]
  | add p q hp hq =>
      obtain ⟨d₁, g₁, hd₁, hg₁⟩ := hp
      obtain ⟨d₂, g₂, hd₂, hg₂⟩ := hq
      refine ⟨d₁ * d₂, MvPolynomial.C d₂ * g₁ + MvPolynomial.C d₁ * g₂,
        mul_ne_zero hd₁ hd₂, ?_⟩
      simp only [map_add, map_mul, MvPolynomial.map_C, hg₁, hg₂, map_mul]
      ring
  | mul_X p i hp =>
      obtain ⟨d, g, hd, hg⟩ := hp
      refine ⟨d, g * MvPolynomial.X i, hd, ?_⟩
      simp only [map_mul, MvPolynomial.map_X, hg, mul_assoc]

/-- Denominator clearing preserves the homogeneous degree of a generic
equation.  Injectivity of the coefficient map reflects homogeneity back to
the equation over the base domain. -/
theorem polynomial_denominator_clear_isHomogeneous
    {A : Type u} {F : Type v} {σ : Type*}
    [CommRing A] [IsDomain A] [Field F] [Algebra A F]
    [IsFractionRing A F]
    (f : MvPolynomial σ F) (g : MvPolynomial σ A)
    (d : A) (n : ℕ) (hf : f.IsHomogeneous n)
    (hclear : MvPolynomial.map (algebraMap A F) g =
      MvPolynomial.C (algebraMap A F d) * f) :
    g.IsHomogeneous n := by
  apply MvPolynomial.IsHomogeneous.of_map (IsFractionRing.injective A F)
  rw [hclear]
  exact hf.C_mul _

/-- Finitely many generic polynomial equations can all be represented over
the same principal open subset of the coefficient domain. -/
theorem exists_finite_polynomials_common_denominator_clear
    {A : Type u} {F : Type v} {σ ι : Type*}
    [CommRing A] [IsDomain A] [Field F] [Algebra A F]
    [IsFractionRing A F]
    [DecidableEq ι]
    (s : Finset ι) (f : ι → MvPolynomial σ F) :
    ∃ d : A, d ≠ 0 ∧ ∀ i ∈ s,
      ∃ g : MvPolynomial σ A,
        MvPolynomial.map (algebraMap A F) g =
          MvPolynomial.C (algebraMap A F d) * f i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨1, one_ne_zero, ?_⟩
      intro i hi
      simp at hi
  | @insert a s ha ih =>
      obtain ⟨d₀, hd₀, h₀⟩ := ih
      obtain ⟨d₁, g₁, hd₁, hg₁⟩ :=
        exists_polynomial_denominator_clear (A := A) (F := F) (f a)
      refine ⟨d₀ * d₁, mul_ne_zero hd₀ hd₁, ?_⟩
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | his
      · refine ⟨MvPolynomial.C d₀ * g₁, ?_⟩
        simp only [map_mul, MvPolynomial.map_C, hg₁, map_mul]
        ring
      · obtain ⟨g₀, hg₀⟩ := h₀ i his
        refine ⟨MvPolynomial.C d₁ * g₀, ?_⟩
        simp only [map_mul, MvPolynomial.map_C, hg₀, map_mul]
        ring

/-- A homogeneous curve ideal over a function field has finitely many
generators whose coefficients admit one common denominator.  This is the
finite-presentation input for spreading the curve over a principal open. -/
theorem exists_ideal_generators_common_denominator_clear
    {A : Type u} {F : Type v}
    [CommRing A] [IsDomain A] [Field F] [Algebra A F]
    [IsFractionRing A F]
    (C : Ideal (MvPolynomial (Fin 4) F)) :
    ∃ (n : ℕ) (f : Fin n → MvPolynomial (Fin 4) F)
      (d : A) (g : Fin n → MvPolynomial (Fin 4) A),
      d ≠ 0 ∧ C = Ideal.span (Set.range f) ∧
        ∀ i, MvPolynomial.map (algebraMap A F) (g i) =
          MvPolynomial.C (algebraMap A F d) * f i := by
  classical
  have hfg : C.FG := IsNoetherian.noetherian C
  obtain ⟨n, f, hf⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hfg
  obtain ⟨d, hd, hclear⟩ :=
    exists_finite_polynomials_common_denominator_clear
      (A := A) (F := F) Finset.univ f
  let g : Fin n → MvPolynomial (Fin 4) A :=
    fun i => Classical.choose (hclear i (Finset.mem_univ i))
  refine ⟨n, f, d, g, hd, ?_, ?_⟩
  · exact hf.symm
  · intro i
    exact Classical.choose_spec (hclear i (Finset.mem_univ i))

/-- Clearing a common nonzero coefficient denominator does not change the
ideal generated over the fraction field. -/
theorem ideal_span_cleared_generators_eq
    {A : Type u} {F : Type v} {σ ι : Type*}
    [CommRing A] [IsDomain A] [Field F] [Algebra A F]
    [IsFractionRing A F]
    (f : ι → MvPolynomial σ F) (g : ι → MvPolynomial σ A)
    (d : A) (hd : d ≠ 0)
    (hclear : ∀ i, MvPolynomial.map (algebraMap A F) (g i) =
      MvPolynomial.C (algebraMap A F d) * f i) :
    Ideal.span (Set.range (fun i => MvPolynomial.map (algebraMap A F) (g i))) =
      Ideal.span (Set.range f) := by
  let J : Ideal (MvPolynomial σ F) :=
    Ideal.span (Set.range (fun i => MvPolynomial.map (algebraMap A F) (g i)))
  let H : Ideal (MvPolynomial σ F) := Ideal.span (Set.range f)
  have hden : algebraMap A F d ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective A F).ne hd
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro x ⟨i, rfl⟩
    change MvPolynomial.map (algebraMap A F) (g i) ∈ H
    rw [hclear i]
    exact H.mul_mem_left _ (Ideal.subset_span ⟨i, rfl⟩)
  · apply Ideal.span_le.mpr
    rintro x ⟨i, rfl⟩
    have hscaled : MvPolynomial.C (algebraMap A F d) * f i ∈ J := by
      rw [← hclear i]
      exact Ideal.subset_span ⟨i, rfl⟩
    have hback := J.mul_mem_left
      (MvPolynomial.C ((algebraMap A F d)⁻¹)) hscaled
    have hcancel : MvPolynomial.C ((algebraMap A F d)⁻¹) *
        (MvPolynomial.C (algebraMap A F d) * f i) = f i := by
      rw [← mul_assoc, ← MvPolynomial.C_mul, inv_mul_cancel₀ hden,
        map_one, one_mul]
    exact hcancel ▸ hback

/-- Every ideal of the generic four-variable polynomial ring is generated by
the coefficient images of finitely many equations over one principal open of
the coefficient domain.  This represents the generic ideal itself, not merely
a list of equations contained in it. -/
theorem exists_ideal_generators_over_principal_open
    {A : Type u} {F : Type v}
    [CommRing A] [IsDomain A] [Field F] [Algebra A F]
    [IsFractionRing A F]
    (C : Ideal (MvPolynomial (Fin 4) F)) :
    ∃ (n : ℕ) (d : A) (g : Fin n → MvPolynomial (Fin 4) A),
      d ≠ 0 ∧
        C = Ideal.span
          (Set.range (fun i => MvPolynomial.map (algebraMap A F) (g i))) := by
  obtain ⟨n, f, d, g, hd, hC, hclear⟩ :=
    exists_ideal_generators_common_denominator_clear (A := A) (F := F) C
  refine ⟨n, d, g, hd, ?_⟩
  exact hC.trans
    (ideal_span_cleared_generators_eq f g d hd hclear).symm

/-- The generic curve ideal is the coefficient extension of a finitely
generated ideal over the configuration coefficient domain.  Flatness and the
geometric properties of the resulting family are separate later steps. -/
theorem exists_finitelyGenerated_ideal_spread_of_fractionField
    {A : Type u} {F : Type v}
    [CommRing A] [IsDomain A] [Field F] [Algebra A F]
    [IsFractionRing A F]
    (C : Ideal (MvPolynomial (Fin 4) F)) :
    ∃ J : Ideal (MvPolynomial (Fin 4) A),
      J.FG ∧ Ideal.map (MvPolynomial.map (algebraMap A F)) J = C := by
  obtain ⟨n, d, g, hd, hC⟩ :=
    exists_ideal_generators_over_principal_open (A := A) (F := F) C
  let J : Ideal (MvPolynomial (Fin 4) A) := Ideal.span (Set.range g)
  refine ⟨J, ?_, ?_⟩
  · exact Submodule.fg_span (Set.finite_range g)
  · change Ideal.map (MvPolynomial.map (algebraMap A F))
        (Ideal.span (Set.range g)) = C
    rw [Ideal.map_span, ← Set.range_comp']
    change Ideal.span
      (Set.range (fun i => MvPolynomial.map (algebraMap A F) (g i))) = C
    exact hC.symm

end PfaffianDescent
