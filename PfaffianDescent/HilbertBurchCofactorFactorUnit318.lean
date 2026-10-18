import PfaffianDescent.HilbertBurchRowLocalization318
import PfaffianDescent.HilbertBurchFactorAndLowHeight318

/-!
The low-height localized cofactor ideals force the actual global cofactor
factor to be a unit, hence recover the original ideal exactly.
-/

noncomputable section

namespace AllCharacteristics.HilbertSurfaceDraft

/-- If a cofactor row generates the unit ideal, any common scalar factor
is a unit.  This statement does not require a local ring. -/
theorem isUnit_common_factor_of_cofactorIdeal_top009
    {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    (M : Matrix (Option ι) ι R) (a : Option ι → R) (c : R)
    (hfactor : ∀ i, PfaffianDescent.hilbertBurchCofactors318 M i = c * a i)
    (htop : Ideal.span (Set.range (PfaffianDescent.hilbertBurchCofactors318 M)) = ⊤) :
    IsUnit c := by
  have hle : Ideal.span (Set.range (PfaffianDescent.hilbertBurchCofactors318 M)) ≤
      Ideal.span ({c} : Set R) := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    rw [hfactor i]
    exact Ideal.mem_span_singleton.mpr ⟨a i, rfl⟩
  rw [htop] at hle
  exact Ideal.span_singleton_eq_top.mp (top_unique hle)

/-- For an actual finite-colength presentation, the common cofactor scalar
is forced to be a unit by low-height localization and the principal ideal
theorem. -/
theorem isUnit_cofactor_factor_of_artinian_presentation009
    {R ι : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [Fintype ι] [DecidableEq ι]
    (hdim : ringKrullDim R = 2)
    (I : Ideal R) [IsArtinianRing (R ⧸ I)]
    (M : Matrix (Option ι) ι R) (a : Option ι → R) (c : R)
    (hI : I = Ideal.span (Set.range a))
    (hg : Function.Injective M.mulVecLin)
    (hgf : LinearMap.range M.mulVecLin = LinearMap.ker (rowFunctional008 a))
    (hfactor : ∀ i, PfaffianDescent.hilbertBurchCofactors318 M i = c * a i) :
    IsUnit c := by
  apply isUnit_of_not_mem_prime_height_le_one c
  intro p hp hpheight hc
  letI : p.IsPrime := hp
  let π : R →+* Localization.AtPrime p := algebraMap R (Localization.AtPrime p)
  have htop := cofactorIdeal_localization_eq_top_at_lowHeight008
    hdim I M a hI hg hgf p hpheight
  have hfactorS (i : Option ι) :
      PfaffianDescent.hilbertBurchCofactors318 (M.map π) i = π c * π (a i) := by
    rw [← PfaffianDescent.hilbertBurchCofactors_map318 π M i, hfactor i, map_mul]
  have hunit : IsUnit (π c) :=
    isUnit_common_factor_of_cofactorIdeal_top009 (M.map π) (fun i ↦ π (a i))
      (π c) hfactorS htop
  have hnot := (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime p) p c).mp hunit
  exact hnot hc

/-- Multiplication by a unit changes neither the generated ideal nor any
of its non-lci structure. -/
theorem cofactorIdeal_eq_of_unit_factor009
    {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    (M : Matrix (Option ι) ι R) (a : Option ι → R) (c : R)
    (hfactor : ∀ i, PfaffianDescent.hilbertBurchCofactors318 M i = c * a i)
    (hc : IsUnit c) :
    Ideal.span (Set.range (PfaffianDescent.hilbertBurchCofactors318 M)) =
      Ideal.span (Set.range a) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    rw [hfactor i]
    exact Ideal.mul_mem_left _ c (Ideal.subset_span (Set.mem_range_self i))
  · obtain ⟨d, hd⟩ := hc.exists_left_inv
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change a i ∈ Ideal.span (Set.range (PfaffianDescent.hilbertBurchCofactors318 M))
    have hmem := Ideal.mul_mem_left
      (Ideal.span (Set.range (PfaffianDescent.hilbertBurchCofactors318 M))) d
      (Ideal.subset_span (Set.mem_range_self i))
    simpa only [hfactor i, ← mul_assoc, hd, one_mul] using hmem

end AllCharacteristics.HilbertSurfaceDraft
