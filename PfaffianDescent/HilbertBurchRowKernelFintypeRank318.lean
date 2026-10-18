import PfaffianDescent.HilbertBurchRowKernelLocalization318

/-!
Uniform syzygy rank for the actual global generator index, including
Option(Fin m), without reindexing its kernel or its matrices.
-/

noncomputable section

namespace AllCharacteristics.HilbertSurfaceDraft

theorem finrank_ker_add_one_of_surjective_nonzero_ideal_fintype015
    {R ι : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] [Fintype ι]
    (J : Ideal R) (hJ : J ≠ ⊥)
    (f : (ι → R) →ₗ[R] J) (hf : Function.Surjective f) :
    Module.finrank R (LinearMap.ker f) + 1 = Fintype.card ι := by
  have hJle : Module.finrank R J ≤ 1 := by simpa using J.finrank_le
  have hJpos : 0 < Module.finrank R J := by
    obtain ⟨x, hx⟩ := Submodule.nonzero_mem_of_bot_lt (bot_lt_iff_ne_bot.mpr hJ)
    exact Module.finrank_pos_iff_exists_ne_zero.mpr ⟨x, hx⟩
  have hJone : Module.finrank R J = 1 := by omega
  have hnull := (LinearMap.ker f).finrank_quotient_add_finrank
  rw [(f.quotKerEquivOfSurjective hf).finrank_eq, hJone] at hnull
  have hamb : Module.finrank R (ι → R) = Fintype.card ι := by simp
  omega

theorem finrank_localized_row_kernel_add_one_fintype015
    {R : Type*} [CommRing R]
    (P : Submonoid R) [IsRegularLocalRing (Localization P)]
    (hdim : ringKrullDim (Localization P) = 2)
    {ι : Type*} [Fintype ι] (a : ι → R)
    (hJ : Ideal.span (Set.range (fun i ↦ algebraMap R (Localization P) (a i))) ≠ ⊥) :
    Module.finrank (Localization P)
      (LocalizedModule P (LinearMap.ker (rowFunctional008 a))) + 1 = Fintype.card ι := by
  let L := Localization P
  let aL : ι → L := fun i ↦ algebraMap R L (a i)
  letI : IsDomain L := AllCharacteristics.isDomain_of_regularLocalRing L
  have h := finrank_ker_add_one_of_surjective_nonzero_ideal_fintype015
    (Ideal.span (Set.range aL)) hJ (rowIdealSurjection013 aL)
    (rowIdealSurjection013_surjective aL)
  rw [rowIdealSurjection013_ker] at h
  rw [(localizedRowKernelEquiv013 P a).finrank_eq]
  exact h

end AllCharacteristics.HilbertSurfaceDraft
