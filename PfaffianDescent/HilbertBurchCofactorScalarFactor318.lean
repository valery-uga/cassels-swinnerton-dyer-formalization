import PfaffianDescent.HilbertBurchSurfaceResolution318
import PfaffianDescent.HilbertBurchRegularPairPowers318
import PfaffianDescent.HilbertBurchCofactorFactorUnit318

/-!
Derives the cofactor scalar factor from the actual exact presentation, rather
than assuming it, and recovers the original ideal by the unit-factor theorem.
-/

noncomputable section

namespace AllCharacteristics.HilbertSurfaceDraft

open Matrix

theorem exists_cofactor_scalar_of_artinian_presentation010
    {R ι : Type*} [CommRing R] [IsRegularLocalRing R]
    [Fintype ι] [DecidableEq ι]
    (hdim : ringKrullDim R = 2)
    (I : Ideal R) [IsArtinianRing (R ⧸ I)]
    (M : Matrix (Option ι) ι R) (a : Option ι → R)
    (f : (Option ι → R) →ₗ[R] I) (hf : Function.Surjective f)
    (hrow : I.subtype.comp f = rowFunctional008 a)
    (hgf : LinearMap.range M.mulVecLin = LinearMap.ker (rowFunctional008 a)) :
    ∃ c : R, ∀ i, PfaffianDescent.hilbertBurchCofactors318 M i = c * a i := by
  let cof := PfaffianDescent.hilbertBurchCofactors318 M
  let ψ := rowFunctional008 cof
  have hrel (u : ι → R) : ψ (M *ᵥ u) = 0 := by
    change dotProduct cof (M *ᵥ u) = 0
    rw [dotProduct_mulVec]
    have hzero : cof ᵥ* M = 0 := by
      ext j
      exact PfaffianDescent.hilbertBurchCofactors_relation318 M j
    rw [hzero]
    simp
  have hker : LinearMap.ker f ≤ LinearMap.ker ψ := by
    intro z hz
    have hzrow : rowFunctional008 a z = 0 := by
      rw [← hrow]
      change (f z : R) = 0
      rw [LinearMap.mem_ker.mp hz]
      rfl
    have hzrange : z ∈ LinearMap.range M.mulVecLin := by
      rw [hgf]
      exact hzrow
    obtain ⟨u, hu⟩ := hzrange
    apply LinearMap.mem_ker.mpr
    rw [← hu]
    exact hrel u
  obtain ⟨φ, hφ⟩ := exists_linearMap_factor_of_ker_le f hf ψ hker
  obtain ⟨x, y, hxI, hyI, hx, hy⟩ :=
    exists_regular_pair_in_ideal_of_artinian_quotient hdim I
  obtain ⟨c, hc⟩ := ideal_linearMap_eq_mul_of_regular_pair I x y hxI hyI hx hy φ
  refine ⟨c, fun i ↦ ?_⟩
  have hφi : φ (f (Pi.single i 1)) = cof i := by
    simpa [LinearMap.comp_apply, ψ, rowFunctional008_apply] using
      congrArg (fun L : (Option ι → R) →ₗ[R] R ↦ L (Pi.single i 1)) hφ
  have hfi : (f (Pi.single i 1) : R) = a i := by
    simpa [LinearMap.comp_apply, rowFunctional008_apply] using
      congrArg (fun L : (Option ι → R) →ₗ[R] R ↦ L (Pi.single i 1)) hrow
  calc
    PfaffianDescent.hilbertBurchCofactors318 M i = φ (f (Pi.single i 1)) := hφi.symm
    _ = c * (f (Pi.single i 1) : R) := hc _
    _ = c * a i := congrArg (fun z : R ↦ c * z) hfi

/-- The genuine signed maximal minors generate the given arbitrary
finite-colength ideal.  The only presentation premises are actual maps,
surjectivity, injectivity, and kernel/image exactness. -/
theorem cofactorIdeal_eq_original_of_artinian_presentation010
    {R ι : Type*} [CommRing R] [IsRegularLocalRing R]
    [Fintype ι] [DecidableEq ι]
    (hdim : ringKrullDim R = 2)
    (I : Ideal R) [IsArtinianRing (R ⧸ I)]
    (M : Matrix (Option ι) ι R) (a : Option ι → R)
    (hI : I = Ideal.span (Set.range a))
    (f : (Option ι → R) →ₗ[R] I) (hf : Function.Surjective f)
    (hrow : I.subtype.comp f = rowFunctional008 a)
    (hg : Function.Injective M.mulVecLin)
    (hgf : LinearMap.range M.mulVecLin = LinearMap.ker (rowFunctional008 a)) :
    Ideal.span (Set.range (PfaffianDescent.hilbertBurchCofactors318 M)) = I := by
  obtain ⟨c, hc⟩ := exists_cofactor_scalar_of_artinian_presentation010
    hdim I M a f hf hrow hgf
  have hunit := isUnit_cofactor_factor_of_artinian_presentation009
    hdim I M a c hI hg hgf hc
  exact (cofactorIdeal_eq_of_unit_factor009 M a c hc hunit).trans hI.symm

end AllCharacteristics.HilbertSurfaceDraft
