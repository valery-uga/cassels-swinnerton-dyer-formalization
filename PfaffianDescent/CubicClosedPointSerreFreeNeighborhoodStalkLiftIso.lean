import PfaffianDescent.CubicClosedPointSerreLocalFreeAlgebra

/-! # Projection-compatible native free coordinates for the actual stalk -/
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped nonZeroDivisors
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

/-- The checked unit-coordinate elimination retains the actual quotient map
to the two-generator ideal. -/
theorem cubicClosedPointSerreFreeNeighborhood_freeOfUnit_projection
    {R : Type u} [CommRing R] (f g : R) (u₀ : Rˣ)
    (z : localSerreExtensionPresentation f g (u₀ : R)) :
    localSerreExtensionToIdeal f g (u₀ : R) z =
      localKoszulToIdeal f g (localSerreExtensionFreeOfUnit f g u₀ z) := by
  induction z using Submodule.Quotient.induction_on with
  | _ z =>
    rw [localSerreExtensionToIdeal_mk]
    simp only [localSerreExtensionFreeOfUnit, LinearEquiv.trans_apply,
      Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk]
    apply Subtype.ext
    change z.1 * f + z.2.1 * g =
      (z.1 - g * (u₀⁻¹ : Rˣ) * z.2.2) * f +
        (z.2.1 + f * (u₀⁻¹ : Rˣ) * z.2.2) * g
    ring

/-- Exactness and actual stalk freeness construct a rank-two coordinate
whose inverse commutes with the actual ideal projection. This is the
native coordinate needed to lift the two quotient generators to a free
neighborhood. -/
theorem cubicClosedPointSerreFreeNeighborhood_exists_stalk_lift_iso
    {R : Type u} [CommRing R] [IsLocalRing R]
    {E : Type u} [AddCommGroup E] [Module R E] [Module.Free R E]
    (ι : R →ₗ[R] E) (f g : R) (π : E →ₗ[R] Ideal.span ({f, g} : Set R))
    (hexact : Function.Exact ι π) (hinj : Function.Injective ι)
    (hsurj : Function.Surjective π)
    (hf : f ∈ R⁰)
    (hg : Ideal.Quotient.mk (Ideal.span {f}) g ∈ (R ⧸ Ideal.span {f})⁰)
    (hfm : f ∈ IsLocalRing.maximalIdeal R) (hgm : g ∈ IsLocalRing.maximalIdeal R) :
    ∃ (l : (R × R) ≃ₗ[R] E), ∀ (z : R × R),
      π (l.toLinearMap z) = localKoszulToIdeal f g z := by
  obtain ⟨e₁, he₁⟩ := hsurj ⟨f, Ideal.subset_span (by simp)⟩
  obtain ⟨e₂, he₂⟩ := hsurj ⟨g, Ideal.subset_span (by simp)⟩
  have hz : π ((-g) • e₁ + f • e₂) = 0 := by
    rw [map_add, map_smul, map_smul, he₁, he₂]
    apply Subtype.ext
    change -g * f + f * g = 0
    ring
  obtain ⟨c, hc⟩ := (hexact _).mp hz
  have hrel : (-g) • e₁ + f • e₂ = c • ι 1 := by
    rw [← hc]
    simpa only [smul_eq_mul, mul_one] using ι.map_smul c (1 : R)
  let d := localSerreExtensionPresentationEquiv_of_exact_of_lifts
    ι f g c π e₁ e₂ hexact hinj he₁ he₂ hrel hf hg
  letI : Module.Free R (localSerreExtensionPresentation f g c) := Module.Free.of_equiv d
  have hunit : IsUnit c :=
    (localSerreExtensionPresentation_free_iff_isUnit f g c hf hfm hgm).mp inferInstance
  obtain ⟨u₀, hu⟩ := hunit
  subst c
  let l := (d.trans (localSerreExtensionFreeOfUnit f g u₀)).symm
  refine ⟨l, ?_⟩
  intro z
  have hp := localSerreExtensionPresentationEquiv_of_exact_of_lifts_projection
    ι f g (u₀ : R) π e₁ e₂ hexact hinj he₁ he₂ hrel hf hg (l z)
  calc
    π (l z) = localSerreExtensionToIdeal f g (u₀ : R) (d (l z)) := hp.symm
    _ = localKoszulToIdeal f g (localSerreExtensionFreeOfUnit f g u₀ (d (l z))) :=
      cubicClosedPointSerreFreeNeighborhood_freeOfUnit_projection f g u₀ _
    _ = localKoszulToIdeal f g z := by
      exact congrArg (localKoszulToIdeal f g)
        ((d.trans (localSerreExtensionFreeOfUnit f g u₀)).apply_symm_apply z)

end PfaffianDescent
