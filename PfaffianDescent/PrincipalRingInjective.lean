import Mathlib.Algebra.Module.Injective
import Mathlib.RingTheory.PrincipalIdealDomain

namespace PfaffianDescent
section
variable {R M : Type*} [CommRing R] [IsPrincipalIdealRing R]
    [AddCommGroup M] [Module R M]

/-- A divisible module over a principal ideal ring is injective. -/
theorem injective_of_principal_divisible
    (hd : ∀ r : R, r ≠ 0 → Function.Surjective (fun m : M => r • m)) : Module.Injective R M := by
  apply Module.Baer.injective
  intro I g
  rcases IsPrincipalIdealRing.principal I with ⟨a, rfl⟩
  obtain rfl | ha := eq_or_ne a 0
  · refine ⟨0, fun x hx => ?_⟩
    rw [Submodule.span_zero_singleton] at hx
    subst hx
    exact (map_zero g).symm
  let aI : (Submodule.span R ({a} : Set R)) := ⟨a, Submodule.subset_span (Set.mem_singleton a)⟩
  obtain ⟨m, hm⟩ := hd a ha (g aI)
  change a • m = g aI at hm
  refine ⟨LinearMap.toSpanSingleton R M m, fun x hx => ?_⟩
  rcases Submodule.mem_span_singleton.mp hx with ⟨r, rfl⟩
  change (r*a) • m = g ⟨r*a, _⟩
  rw [mul_smul, hm]
  exact (g.map_smul r aI).symm

/-- Divisibility passes to every module quotient. -/
theorem principal_quotient_injective
    (hd : ∀ r : R, r ≠ 0 → Function.Surjective (fun m : M => r • m)) (N : Submodule R M) :
    Module.Injective R (M ⧸ N) := by
  apply injective_of_principal_divisible
  intro r hr v
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective N v
  obtain ⟨y, hy⟩ := hd r hr x
  change r • y = x at hy
  refine ⟨N.mkQ y, ?_⟩
  change r • N.mkQ y = N.mkQ x
  rw [← map_smul, hy]

end
section
variable {R F : Type*} [CommRing R] [IsPrincipalIdealRing R] [Field F]
    [Algebra R F] [FaithfulSMul R F]

lemma fieldModule_divisible (r : R) (hr : r ≠ 0) :
    Function.Surjective (fun x : F => r • x) := by
  intro x
  have h : algebraMap R F r ≠ 0 := by
    intro he
    apply hr
    apply FaithfulSMul.algebraMap_injective R F
    rw [he, map_zero]
  refine ⟨(algebraMap R F r)⁻¹ * x, ?_⟩
  change r • ((algebraMap R F r)⁻¹ * x) = x
  rw [Algebra.smul_def, ← mul_assoc, mul_inv_cancel₀ h, one_mul]

/-- A faithful field algebra is injective over a principal ideal base ring. -/
theorem fieldModule_injective : Module.Injective R F :=
  injective_of_principal_divisible fieldModule_divisible

/-- Quotients of a faithful field algebra are also injective over the principal base ring. -/
theorem fieldModule_quotient_injective (N : Submodule R F) : Module.Injective R (F ⧸ N) :=
  principal_quotient_injective fieldModule_divisible N

end
end PfaffianDescent
