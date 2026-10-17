import PfaffianDescent.PointCartierYonedaUnitBoundary
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
import Mathlib.Algebra.Category.ModuleCat.Projective

/-! # Nonzero ambient local Koszul classes

This proves local algebraic nonvanishing only. It does not assert that a
global trace is nonzero or that a global trace agrees with this coordinate.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace PfaffianDescent

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open scoped nonZeroDivisors

universe u w

variable {R : Type u} [CommRing R] [hExt : HasExt.{w} (ModuleCat R)]

theorem pointCartierYonedaAmbientClass_mem_of_eq_zero
    (f g h : R) (hf : f ∈ R⁰)
    (hg : Ideal.Quotient.mk (Ideal.span {f}) g ∈ (R ⧸ Ideal.span {f})⁰)
    (hh : ∀ x : R, h * x ∈ Ideal.span ({f, g} : Set R) →
      x ∈ Ideal.span ({f, g} : Set R)) (r : R)
    (hz : pointCartierYonedaAmbientClass f g h hf hg hh r = 0) :
    r ∈ Ideal.span ({f, g, h} : Set R) := by
  let T := pointCartierYonedaAmbientResolution f g h hf hg hh
  let ψ : T.K₂ ⟶ ModuleCat.of R R :=
    degreeThreeCocycleDesc (ModuleCat.ofHom (threeGeneratorFirst f g h))
      (0 : ModuleCat.of R PUnit ⟶ ModuleCat.of R R) (by simp)
      (pointCartierYonedaAmbientFirst_exact f g h hf) (pointCartierYonedaAmbientTopCocycle r)
  letI : Subsingleton (Ext.{w} T.C₀ (ModuleCat.of R R) 2) := by
    change Subsingleton (Ext.{w} (ModuleCat.of R R) (ModuleCat.of R R) (1 + 1))
    exact Ext.subsingleton_of_projective _ _ 1
  letI : Subsingleton (Ext.{w} T.C₁ (ModuleCat.of R R) 1) := by
    change Subsingleton (Ext.{w} (ModuleCat.of R (R × R × R)) (ModuleCat.of R R) (0 + 1))
    exact Ext.subsingleton_of_projective _ _ 0
  obtain ⟨q, hq⟩ := (T.connecting_eq_zero_iff (ModuleCat.of R R) ψ).mp hz
  change ModuleCat.of R (R × R × R) ⟶ ModuleCat.of R R at q
  have hq' : ModuleCat.ofHom (threeGeneratorFirst f g h) ≫ q =
      ModuleCat.ofHom (LinearMap.lsmul R R r) := by
    change Abelian.factorThruCoimage (ModuleCat.ofHom (threeGeneratorFirst f g h)) ≫ q =
      degreeThreeCocycleDesc _ _ _ _ _ at hq
    rw [← Abelian.coimage.fac (ModuleCat.ofHom (threeGeneratorFirst f g h)), Category.assoc,
      hq, coimage_π_comp_degreeThreeCocycleDesc]
    rfl
  have hlin := congrArg (fun k : ModuleCat.of R R ⟶ ModuleCat.of R R ↦ k.hom) hq'
  change q.hom.comp (threeGeneratorFirst f g h) = LinearMap.lsmul R R r at hlin
  have hval := LinearMap.congr_fun hlin 1
  simp only [LinearMap.comp_apply, threeGeneratorFirst, LinearMap.coe_mk, AddHom.coe_mk,
    LinearMap.lsmul_apply, smul_eq_mul, mul_one] at hval
  change q.hom (h, -g, f) = r at hval
  have ht : (h, -g, f) =
      h • (1, 0, 0) + (-g) • (0, 1, 0) + f • (0, 0, 1) := by
    ext <;> simp
  rw [ht, map_add, map_add, map_smul, map_smul, map_smul] at hval
  change h * q.hom (1, 0, 0) + (-g) * q.hom (0, 1, 0) + f * q.hom (0, 0, 1) = r at hval
  rw [← hval]
  apply Ideal.add_mem
  · apply Ideal.add_mem
    · exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))
    · exact Ideal.mul_mem_right _ _ ((Ideal.span ({f, g, h} : Set R)).neg_mem
        (Ideal.subset_span (by simp)))
  · exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))

/-- A unit coefficient gives a nonzero ambient local point class whenever
the point ideal is proper. -/
theorem pointCartierYonedaAmbientClass_unit_ne_zero
    (f g h : R) (hf : f ∈ R⁰)
    (hg : Ideal.Quotient.mk (Ideal.span {f}) g ∈ (R ⧸ Ideal.span {f})⁰)
    (hh : ∀ x : R, h * x ∈ Ideal.span ({f, g} : Set R) →
      x ∈ Ideal.span ({f, g} : Set R)) (v : Rˣ)
    (hproper : Ideal.span ({f, g, h} : Set R) ≠ ⊤) :
    pointCartierYonedaAmbientClass f g h hf hg hh (v : R) ≠ 0 := by
  intro hz
  have hmem := pointCartierYonedaAmbientClass_mem_of_eq_zero f g h hf hg hh (v : R) hz
  have hone : (1 : R) ∈ Ideal.span ({f, g, h} : Set R) := by
    have hm := Ideal.mul_mem_left (Ideal.span ({f, g, h} : Set R)) (v⁻¹ : Rˣ) hmem
    simpa only [Units.inv_mul] using hm
  exact hproper ((Ideal.eq_top_iff_one _).mpr hone)

end PfaffianDescent
