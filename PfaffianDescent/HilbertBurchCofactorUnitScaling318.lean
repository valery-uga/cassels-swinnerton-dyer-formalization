import PfaffianDescent.HilbertBurchCofactorFactorUnit318
import Mathlib.Algebra.GroupWithZero.Action.Units

/-!
Clearing a common denominator scales an entire rectangular matrix by a
unit after localization. The actual signed cofactor ideal and all
relations remain unchanged there, with no domain hypothesis.
-/

noncomputable section

namespace PfaffianDescent

open Matrix

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

theorem hilbertBurchCofactors_smul016
    (c : R) (M : Matrix (Option ι) ι R) (i : Option ι) :
    hilbertBurchCofactors318 (c • M) i = c ^ Fintype.card ι * hilbertBurchCofactors318 M i := by
  have haug : hilbertBurchAugment318 (c • M) = c • hilbertBurchAugment318 M := by
    ext j k
    cases k <;> simp [hilbertBurchAugment318, smul_eq_mul]
  unfold hilbertBurchCofactors318
  rw [haug, Matrix.adjugate_smul]
  simp [Fintype.card_option, smul_eq_mul]

end PfaffianDescent

namespace AllCharacteristics.HilbertSurfaceDraft

open Matrix

theorem range_unit_smul016
    {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) (c : R) (hc : IsUnit c) :
    LinearMap.range (c • f) = LinearMap.range f := by
  obtain ⟨u, rfl⟩ := hc
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    exact ⟨(u : R) • x, f.map_smul _ _⟩
  · rintro y ⟨x, rfl⟩
    refine ⟨(↑(u⁻¹) : R) • x, ?_⟩
    simp [LinearMap.smul_apply, map_smul, smul_smul]

theorem ker_unit_smul016
    {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) (c : R) (hc : IsUnit c) :
    LinearMap.ker (c • f) = LinearMap.ker f := by
  ext x
  simp only [LinearMap.mem_ker, LinearMap.smul_apply]
  exact hc.smul_eq_zero

theorem rowFunctional_coeff_mul016
    {R κ : Type*} [CommRing R] [Fintype κ] (c : R) (a : κ → R) :
    rowFunctional008 (fun i ↦ c * a i) = c • rowFunctional008 a := by
  apply LinearMap.ext
  intro z
  change (∑ i, (c * a i) * z i) = c * ∑ i, a i * z i
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ ↦ mul_assoc _ _ _)

theorem cofactorIdeal_unit_smul016
    {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    (c : R) (hc : IsUnit c) (M : Matrix (Option ι) ι R) :
    Ideal.span (Set.range (PfaffianDescent.hilbertBurchCofactors318 (c • M))) =
      Ideal.span (Set.range (PfaffianDescent.hilbertBurchCofactors318 M)) := by
  exact cofactorIdeal_eq_of_unit_factor009 (c • M)
    (PfaffianDescent.hilbertBurchCofactors318 M) (c ^ Fintype.card ι)
    (PfaffianDescent.hilbertBurchCofactors_smul016 c M) (hc.pow _)

theorem exact_cofactor_matrix_unit_smul016
    {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    (c : R) (hc : IsUnit c) (M : Matrix (Option ι) ι R) :
    Function.Exact (c • M).mulVecLin
      (rowFunctional008 (PfaffianDescent.hilbertBurchCofactors318 (c • M))) ↔
      Function.Exact M.mulVecLin
        (rowFunctional008 (PfaffianDescent.hilbertBurchCofactors318 M)) := by
  have hmap : (c • M).mulVecLin = c • M.mulVecLin := by
    apply LinearMap.ext
    intro z
    exact Matrix.smul_mulVec _ _ _
  have hrow : rowFunctional008 (PfaffianDescent.hilbertBurchCofactors318 (c • M)) =
      (c ^ Fintype.card ι) • rowFunctional008 (PfaffianDescent.hilbertBurchCofactors318 M) := by
    have hfun : PfaffianDescent.hilbertBurchCofactors318 (c • M) =
        (fun i ↦ c ^ Fintype.card ι * PfaffianDescent.hilbertBurchCofactors318 M i) :=
      funext (PfaffianDescent.hilbertBurchCofactors_smul016 c M)
    rw [hfun]
    exact rowFunctional_coeff_mul016 _ _
  simp only [LinearMap.exact_iff, hmap, hrow,
    ker_unit_smul016 _ _ (hc.pow _), range_unit_smul016 _ _ hc]

end AllCharacteristics.HilbertSurfaceDraft
