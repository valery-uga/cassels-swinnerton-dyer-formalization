import PfaffianDescent.QuadraticConjugateDescent
import PfaffianDescent.GaloisFixedPolynomialCoefficientDescent
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic

/-! SOURCE ONLY / UNVERIFIED. Actual inverse quadratics descend from the
paired linear coordinate forms. No rationality or field-of-functions
descent certificate is an input. -/
noncomputable section
namespace PfaffianDescent.QuadraticSkewRationality.InverseQuadratics
open Module MvPolynomial
universe u v
variable {k E : Type u} [Field k] [Field E] [Algebra k E]
  [FiniteDimensional k E] [IsGalois k E]

theorem quadratic_fixed_polynomial_descends
    {J : Type v} (σ : E ≃ₐ[k] E) (hσ : σ ≠ AlgEquiv.refl)
    (h₂ : finrank k E = 2) (q : MvPolynomial J E)
    (hfix : MvPolynomial.map σ.toRingHom q = q) :
    ∃ Q : MvPolynomial J k, MvPolynomial.map (algebraMap k E) Q = q := by
  apply galois_fixed_polynomial_descends q
  intro g
  rcases galois_aut_eq_refl_or_of_finrank_two σ hσ h₂ g with hg | hg
  · subst g
    change MvPolynomial.map (RingHom.id E) q = q
    exact MvPolynomial.map_id q
  · subst g
    exact hfix

/-- The source-chart denominator and the two inverse numerators are actual
ground homogeneous quadratics in the original projective coordinates. -/
theorem conjugate_inverse_quadratics_descend
    {J : Type v} (σ : E ≃ₐ[k] E) (hσ : σ ≠ AlgEquiv.refl)
    (h₂ : finrank k E = 2) (α : E) (hα : α ≠ σ α)
    (x : Fin 4 → MvPolynomial J E)
    (hx : ∀ i, (x i).IsHomogeneous 1)
    (hx₀ : MvPolynomial.map σ.toRingHom (x 0) = x 2)
    (hx₁ : MvPolynomial.map σ.toRingHom (x 1) = x 3)
    (hy₀ : MvPolynomial.map σ.toRingHom (x 2) = x 0)
    (hy₁ : MvPolynomial.map σ.toRingHom (x 3) = x 1) :
    ∃ Q R_T R_U : MvPolynomial J k,
      Q.IsHomogeneous 2 ∧ R_T.IsHomogeneous 2 ∧ R_U.IsHomogeneous 2 ∧
      MvPolynomial.map (algebraMap k E) Q = x 0 * x 2 ∧
      MvPolynomial.map (algebraMap k E) R_T =
        C (α - σ α)⁻¹ * (C α * x 3 * x 0 - C (σ α) * x 1 * x 2) ∧
      MvPolynomial.map (algebraMap k E) R_U =
        C (α - σ α)⁻¹ * (x 1 * x 2 - x 3 * x 0) := by
  classical
  have hsq : σ (σ α) = α := by
    have h := DFunLike.congr_fun (galois_involution_of_finrank_two σ hσ h₂) α
    change σ (σ α) = α at h
    exact h
  have hδ : σ (α - σ α) = -(α - σ α) := by
    rw [map_sub, hsq]
    ring
  have hδinv : σ ((α - σ α)⁻¹) = -((α - σ α)⁻¹) := by
    rw [map_inv₀, hδ, neg_inv]
  have hαmap : σ.toRingHom α = σ α := rfl
  have hβmap : σ.toRingHom (σ α) = α := hsq
  have hδinvmap : σ.toRingHom ((α - σ α)⁻¹) = -((α - σ α)⁻¹) := hδinv
  let q := x 0 * x 2
  let t := C (α - σ α)⁻¹ * (C α * x 3 * x 0 - C (σ α) * x 1 * x 2)
  let u := C (α - σ α)⁻¹ * (x 1 * x 2 - x 3 * x 0)
  have hqfix : MvPolynomial.map σ.toRingHom q = q := by
    simp only [q, map_mul, hx₀, hy₀]
    ring
  have htfix : MvPolynomial.map σ.toRingHom t = t := by
    simp only [t, map_mul, map_sub, MvPolynomial.map_C,
      hδinvmap, hαmap, hβmap, hx₀, hx₁, hy₀, hy₁, map_neg]
    ring
  have hufix : MvPolynomial.map σ.toRingHom u = u := by
    simp only [u, map_mul, map_sub, MvPolynomial.map_C,
      hδinvmap, hx₀, hx₁, hy₀, hy₁, map_neg]
    ring
  obtain ⟨Q, hQ⟩ := quadratic_fixed_polynomial_descends σ hσ h₂ q hqfix
  obtain ⟨R_T, hT⟩ := quadratic_fixed_polynomial_descends σ hσ h₂ t htfix
  obtain ⟨R_U, hU⟩ := quadratic_fixed_polynomial_descends σ hσ h₂ u hufix
  have hqhom : q.IsHomogeneous 2 := (hx 0).mul (hx 2)
  have hthom : t.IsHomogeneous 2 :=
    (((hx 3).C_mul α).mul (hx 0)).sub
      (((hx 1).C_mul (σ α)).mul (hx 2)) |>.C_mul _
  have huhom : u.IsHomogeneous 2 :=
    ((hx 1).mul (hx 2)).sub ((hx 3).mul (hx 0)) |>.C_mul _
  have hmap := (algebraMap k E).injective
  refine ⟨Q, R_T, R_U, ?_, ?_, ?_, hQ, hT, hU⟩
  · apply MvPolynomial.IsHomogeneous.of_map hmap
    rw [hQ]
    exact hqhom
  · apply MvPolynomial.IsHomogeneous.of_map hmap
    rw [hT]
    exact hthom
  · apply MvPolynomial.IsHomogeneous.of_map hmap
    rw [hU]
    exact huhom

/-- These are the exact functions represented by the descended quadratic
fractions on the projective basic open, before any scheme glue. -/
theorem inverse_quadratic_ratios
    (α β x₀ x₁ y₀ y₁ : E) (hαβ : α ≠ β)
    (hx₀ : x₀ ≠ 0) (hy₀ : y₀ ≠ 0) :
    ((α - β)⁻¹ * (α * y₁ * x₀ - β * x₁ * y₀)) / (x₀ * y₀) =
        (α * (y₁ / y₀) - β * (x₁ / x₀)) / (α - β) ∧
    ((α - β)⁻¹ * (x₁ * y₀ - y₁ * x₀)) / (x₀ * y₀) =
        ((x₁ / x₀) - (y₁ / y₀)) / (α - β) := by
  constructor <;> field_simp [sub_ne_zero.mpr hαβ, hx₀, hy₀] <;> ring

end PfaffianDescent.QuadraticSkewRationality.InverseQuadratics
