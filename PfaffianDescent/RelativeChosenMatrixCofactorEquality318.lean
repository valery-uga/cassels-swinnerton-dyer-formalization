import PfaffianDescent.RelativeSurfacePresentation318
import PfaffianDescent.OriginalArtinIdealRegularPair318
import PfaffianDescent.NilpotentUnitReflection318

/-!
Identify the cofactor ideal of a chosen exact relative matrix from an exact
regular-surface residue presentation. Any residue syzygy basis is allowed;
no normalization equating its cofactor row to its generator row is needed.
This comparison supplies the local step in semilocal equality reflection,
without a global regular-pair, scalar-factor, or cofactor-ideal input.
-/

noncomputable section
namespace AllCharacteristics
open LinearMap Matrix HilbertSurfaceDraft
universe u v w t

theorem cofactorIdeal_eq_of_relative_presentation_and_exact_fiber318
    {S : Type u} {A : Type v} {A₀ : Type w} {ι : Type t}
    [CommRing S] [CommRing A] [CommRing A₀] [Algebra S A]
    [Module.Flat S A] [IsRegularLocalRing A₀] [Fintype ι] [DecidableEq ι]
    (I : Ideal S) [I.IsMaximal] (hI : IsNilpotent I)
    (π : A →+* A₀) (hπ : Function.Surjective π)
    (hker : RingHom.ker π = I.map (algebraMap S A))
    (hdim : ringKrullDim A₀ = 2) (J : Ideal A)
    [IsArtinianRing (A₀ ⧸ J.map π)]
    (M : Matrix (Option ι) ι A) (a : Option ι → A)
    (hJa : J = Ideal.span (Set.range a))
    (hMrange : LinearMap.range M.mulVecLin = LinearMap.ker (rowFunctional008 a))
    (hM₀inj : Function.Injective (M.map π).mulVecLin)
    (hM₀range : LinearMap.range (M.map π).mulVecLin =
      LinearMap.ker (rowFunctional008 (fun i => π (a i)))) :
    Ideal.span (Set.range (PfaffianDescent.hilbertBurchCofactors318 M)) = J := by
  have ha (i : Option ι) : a i ∈ J := by
    rw [hJa]
    exact Ideal.mem_span_range_self (x := i)
  let f := familyIdealMap318 J a ha
  have hf : Function.Surjective f := familyIdealMap318_surjective J a ha hJa
  have hrow : J.subtype.comp f = rowFunctional008 a := by
    apply LinearMap.ext
    intro z
    change (∑ i, z i * a i) = ∑ i, a i * z i
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  let cof := PfaffianDescent.hilbertBurchCofactors318 M
  let ψ := rowFunctional008 cof
  have hrel (b : ι → A) : ψ (M *ᵥ b) = 0 := by
    change dotProduct cof (M *ᵥ b) = 0
    rw [dotProduct_mulVec]
    have hzero : cof ᵥ* M = 0 := by
      ext j
      exact PfaffianDescent.hilbertBurchCofactors_relation318 M j
    rw [hzero]
    simp
  have hkerψ : f.ker ≤ ψ.ker := by
    intro z hz
    have hzrow : rowFunctional008 a z = 0 := by
      rw [← hrow]
      change (f z : A) = 0
      rw [LinearMap.mem_ker.mp hz]
      rfl
    have hzrange : z ∈ LinearMap.range M.mulVecLin := by
      rw [hMrange]
      exact hzrow
    obtain ⟨b, hb⟩ := hzrange
    apply LinearMap.mem_ker.mpr
    rw [← hb]
    exact hrel b
  obtain ⟨φ, hφ⟩ := exists_linearMap_factor_of_ker_le f hf ψ hkerψ
  obtain ⟨p, q, hpJ, hqJ, hp, hq⟩ :=
    exists_regularPair_in_originalIdeal_of_regularSurface_fiber318 hdim I hI π hπ hker J
  obtain ⟨c, hcAll⟩ := ideal_linearMap_eq_mul_of_regular_pair J p q hpJ hqJ hp hq φ
  have hc (i : Option ι) : PfaffianDescent.hilbertBurchCofactors318 M i = c * a i := by
    have hφi : φ (f (Pi.single i 1)) = cof i := by
      simpa [LinearMap.comp_apply, ψ, rowFunctional008_apply] using
        congrArg (fun L : (Option ι → A) →ₗ[A] A => L (Pi.single i 1)) hφ
    have hfi : (f (Pi.single i 1) : A) = a i := by
      simpa [LinearMap.comp_apply, rowFunctional008_apply] using
        congrArg (fun L : (Option ι → A) →ₗ[A] A => L (Pi.single i 1)) hrow
    exact hφi.symm.trans ((hcAll _).trans (congrArg (fun z : A => c * z) hfi))
  have hJ₀ : J.map π = Ideal.span (Set.range (fun i => π (a i))) := by
    rw [hJa, Ideal.map_span, ← Set.range_comp]
    rfl
  have hc₀ (i : Option ι) :
      PfaffianDescent.hilbertBurchCofactors318 (M.map π) i = π c * π (a i) := by
    rw [← PfaffianDescent.hilbertBurchCofactors_map318, hc, map_mul]
  have hc₀unit : IsUnit (π c) :=
    isUnit_cofactor_factor_of_artinian_presentation009 hdim (J.map π)
      (M.map π) (fun i => π (a i)) (π c) hJ₀ hM₀inj hM₀range hc₀
  have hπnil : IsNilpotent (RingHom.ker π) := by
    obtain ⟨n, hn⟩ := hI
    refine ⟨n, ?_⟩
    rw [hker, ← Ideal.map_pow, hn]
    simp only [Ideal.zero_eq_bot, Ideal.map_bot]
  have hcunit : IsUnit c := isUnit_of_surjective_nilpotent_reduction318 π hπ hπnil c hc₀unit
  exact (cofactorIdeal_eq_of_unit_factor009 M a c hc hcunit).trans hJa.symm

end AllCharacteristics
end
