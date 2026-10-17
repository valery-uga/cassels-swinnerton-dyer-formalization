import PfaffianDescent.CechExtVanishingLowDegree
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives

/-! # Degree-one Ext vanishing for arbitrary coproducts -/
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
namespace PfaffianDescent
universe u v w t
variable {A : Type u} [Category.{v} A] [Abelian A] [HasExt.{w} A]

/-- Vanishing on each summand lifts maps out of an arbitrary coproduct
through the last map of a short exact sequence. -/
theorem coproduct_hom_postcomp_surjective_of_ext_one_subsingleton
    {J : Type t} (X : J → A) [HasCoproduct X]
    (S : ShortComplex A) (hS : S.ShortExact)
    [∀ j, Subsingleton (Ext.{w} (X j) S.X₁ 1)] :
    Function.Surjective (fun h : (∐ X) ⟶ S.X₂ => h ≫ S.g) := by
  classical
  intro h
  have hlocal (j : J) : ∃ l : X j ⟶ S.X₂, l ≫ S.g = Sigma.ι X j ≫ h := by
    have hz : (Ext.mk₀ (Sigma.ι X j ≫ h)).comp hS.extClass (zero_add 1) = 0 :=
      Subsingleton.elim _ _
    obtain ⟨e, he⟩ := Ext.covariant_sequence_exact₃ (X j) hS
      (Ext.mk₀ (Sigma.ι X j ≫ h)) (zero_add 1) hz
    refine ⟨Ext.homEquiv₀ e, ?_⟩
    apply (Ext.mk₀_bijective (X j) S.X₃).1
    rw [← Ext.mk₀_comp_mk₀, Ext.mk₀_homEquiv₀_apply]
    exact he
  choose l hl using hlocal
  refine ⟨Sigma.desc l, ?_⟩
  apply Sigma.hom_ext
  intro j
  rw [← Category.assoc, Sigma.ι_desc]
  exact hl j

/-- A short exact sequence with an injective middle term and surjective
coefficient lifting forces degree-one Ext to vanish. -/
theorem ext_one_subsingleton_of_injective_middle_and_hom_postcomp_surjective
    (P : A) (S : ShortComplex A) (hS : S.ShortExact) [Injective S.X₂]
    (hlift : Function.Surjective (fun h : P ⟶ S.X₂ => h ≫ S.g)) :
    Subsingleton (Ext.{w} P S.X₁ 1) := by
  apply subsingleton_of_forall_eq 0
  intro z
  obtain ⟨e, he⟩ := Ext.covariant_sequence_exact₁ P hS z
    (Ext.eq_zero_of_injective _) (zero_add 1)
  obtain ⟨h, hh⟩ := hlift (Ext.homEquiv₀ e)
  change h ≫ S.g = Ext.homEquiv₀ e at hh
  have hmk : e = (Ext.mk₀ h).comp (Ext.mk₀ S.g) (zero_add 0) := by
    rw [Ext.mk₀_comp_mk₀, hh, Ext.mk₀_homEquiv₀_apply]
  rw [← he, hmk, Ext.comp_assoc_of_second_deg_zero _ _ _ (zero_add 1), hS.comp_extClass, Ext.comp_zero]

/-- Unlike higher-degree finite-biproduct arguments, degree-one vanishing
extends to arbitrary coproducts by assembling independent lifts. -/
theorem ext_one_coproduct_subsingleton
    [EnoughInjectives A] {J : Type t} (X : J → A) [HasCoproduct X] (Y : A)
    [∀ j, Subsingleton (Ext.{w} (X j) Y 1)] :
    Subsingleton (Ext.{w} (∐ X) Y 1) := by
  let S : ShortComplex A :=
    ShortComplex.mk (Injective.ι Y) (cokernel.π (Injective.ι Y))
      (cokernel.condition (Injective.ι Y))
  have hS : S.ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel S.f) }
  exact ext_one_subsingleton_of_injective_middle_and_hom_postcomp_surjective
    (∐ X) S hS (coproduct_hom_postcomp_surjective_of_ext_one_subsingleton X S hS)
end PfaffianDescent
