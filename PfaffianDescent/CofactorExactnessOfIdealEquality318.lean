import PfaffianDescent.RelativeSurfacePresentation318
import Mathlib.RingTheory.FiniteType

/-!
Once the actual cofactor ideal has been identified
with the original ideal, cofactor exactness follows from the original exact
complex. The induced surjective endomorphism of the finitely generated
ideal is injective by the commutative-ring Orzech theorem. No domain,
regular-pair, unit scalar, or cofactor-kernel equality input is required.
-/

noncomputable section
namespace AllCharacteristics
open LinearMap Matrix HilbertSurfaceDraft
universe u v

theorem cofactor_exact_of_original_presentation_and_ideal_equality318
    {A : Type u} {ι : Type v} [CommRing A] [Fintype ι] [DecidableEq ι]
    (J : Ideal A) (M : Matrix (Option ι) ι A) (a : Option ι → A)
    (hJa : J = Ideal.span (Set.range a))
    (hMrange : LinearMap.range M.mulVecLin = LinearMap.ker (rowFunctional008 a))
    (hJcof : J = Ideal.span (Set.range (PfaffianDescent.hilbertBurchCofactors318 M))) :
    LinearMap.range M.mulVecLin = LinearMap.ker
      (rowFunctional008 (PfaffianDescent.hilbertBurchCofactors318 M)) := by
  let cof := PfaffianDescent.hilbertBurchCofactors318 M
  have ha (i : Option ι) : a i ∈ J := by
    rw [hJa]
    exact Ideal.mem_span_range_self (x := i)
  have hcof (i : Option ι) : cof i ∈ J := by
    rw [hJcof]
    exact Ideal.mem_span_range_self (x := i)
  let f := familyIdealMap318 J a ha
  let ψ := familyIdealMap318 J cof hcof
  have hf : Function.Surjective f := familyIdealMap318_surjective J a ha hJa
  have hψ : Function.Surjective ψ := familyIdealMap318_surjective J cof hcof hJcof
  have hrel (b : ι → A) : rowFunctional008 cof (M *ᵥ b) = 0 := by
    change dotProduct cof (M *ᵥ b) = 0
    rw [dotProduct_mulVec]
    have hzero : cof ᵥ* M = 0 := by
      ext j
      exact PfaffianDescent.hilbertBurchCofactors_relation318 M j
    rw [hzero]
    simp
  have hker : f.ker ≤ ψ.ker := by
    rw [familyIdealMap318_ker, familyIdealMap318_ker, ← hMrange]
    rintro z ⟨b, rfl⟩
    exact hrel b
  obtain ⟨φ, hφ⟩ := exists_linearMap_factor_of_ker_le f hf ψ hker
  have hφeval (z : Option ι → A) : φ (f z) = ψ z :=
    congrArg (fun L : (Option ι → A) →ₗ[A] J => L z) hφ
  have hφsurj : Function.Surjective φ := by
    intro j
    obtain ⟨z, hz⟩ := hψ j
    exact ⟨f z, (hφeval z).trans hz⟩
  letI : Module.Finite A J := Module.Finite.of_surjective f hf
  have hφinj : Function.Injective φ :=
    OrzechProperty.injective_of_surjective_endomorphism φ hφsurj
  have hkerEq : ψ.ker = f.ker := by
    ext z
    change ψ z = 0 ↔ f z = 0
    constructor
    · intro hz
      apply hφinj
      rw [map_zero, hφeval, hz]
    · intro hz
      rw [← hφeval, hz, map_zero]
  rw [familyIdealMap318_ker, familyIdealMap318_ker] at hkerEq
  exact hMrange.trans hkerEq.symm

end AllCharacteristics
end
