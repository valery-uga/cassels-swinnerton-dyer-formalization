import PfaffianDescent.FiniteSupportIdealMatrixSpreading
import PfaffianDescent.HilbertBurchExactComplexSpreading318
import PfaffianDescent.HilbertBurchCofactorUnitScaling318
import PfaffianDescent.HilbertBurchFiniteFlatLift318

/-!
Spread a simultaneous semilocal Hilbert--Burch presentation to one
principal open, retaining the whole ideal and every relation. The
neighborhood and its coefficient matrix are constructed from the
semilocal presentation. The original Artin-support construction supplies
that presentation in the geometric application.
-/

noncomputable section
namespace PfaffianDescent
open Matrix
open AllCharacteristics.HilbertSurfaceDraft
open scoped BigOperators
universe u v
set_option autoImplicit false

/-- The determinantal complex is a complex over the ORIGINAL ring,
before denominators or neighborhood exactness are considered. -/
theorem hilbertBurchCofactors_mulVec_zero001
    {R : Type u} [CommRing R] {ι : Type v} [Fintype ι] [DecidableEq ι]
    (N : Matrix (Option ι) ι R) (w : ι → R) :
    rowFunctional008 (hilbertBurchCofactors318 N) (N.mulVecLin w) = 0 := by
  change (∑ i, hilbertBurchCofactors318 N i * (∑ j, N i j * w j)) = 0
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [← mul_assoc, ← Finset.sum_mul, hilbertBurchCofactors_relation318,
    zero_mul]
  simp

/-- The actual semilocal matrix clears denominators and gives a genuine
whole-ideal cofactor presentation on a single original principal open.
Every further principal shrinking preserves the same presentation. -/
theorem semilocalMatrix_exists_principal_cofactorPresentation001
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (S : Submonoid R) {ι : Type v} [Fintype ι] [DecidableEq ι]
    (J : Ideal R) (M : Matrix (Option ι) ι (Localization S))
    (hJ : J.map (algebraMap R (Localization S)) =
      Ideal.span (Set.range (hilbertBurchCofactors318 M)))
    (hex : Function.Exact M.mulVecLin (rowFunctional008 (hilbertBurchCofactors318 M))) :
    ∃ (s : R) (N : Matrix (Option ι) ι R), s ∈ S ∧
      ∀ r : R, s ∣ r →
        J.map (algebraMap R (Localization.Away r)) =
          Ideal.span (Set.range (hilbertBurchCofactors318
            (N.map (algebraMap R (Localization.Away r))))) ∧
        Function.Exact (N.map (algebraMap R (Localization.Away r))).mulVecLin
          (rowFunctional008 (hilbertBurchCofactors318
            (N.map (algebraMap R (Localization.Away r))))) := by
  let L := Localization S
  obtain ⟨d, hd, N, hN⟩ := finiteMatrix_exists_commonDenominator001 S M
  let c := algebraMap R L d
  have hc : IsUnit c := IsLocalization.map_units L (⟨d, hd⟩ : S)
  have hNmap : N.map (algebraMap R L) = c • M := by
    ext i j
    exact hN i j
  have hrowmap : (fun i ↦ algebraMap R L (hilbertBurchCofactors318 N i)) =
      hilbertBurchCofactors318 (N.map (algebraMap R L)) :=
    funext (hilbertBurchCofactors_map318 (algebraMap R L) N)
  have hexN : Function.Exact (N.map (algebraMap R L)).mulVecLin
      (rowFunctional008 (fun i ↦ algebraMap R L (hilbertBurchCofactors318 N i))) := by
    rw [hrowmap, hNmap]
    exact (exact_cofactor_matrix_unit_smul016 c hc M).mpr hex
  let I := Ideal.span (Set.range (hilbertBurchCofactors318 N))
  have heq : J.map (algebraMap R L) = I.map (algebraMap R L) := by
    change J.map (algebraMap R L) =
      (Ideal.span (Set.range (hilbertBurchCofactors318 N))).map (algebraMap R L)
    rw [hilbertBurchCofactorIdeal_map318, hNmap, cofactorIdeal_unit_smul016 c hc M]
    exact hJ
  obtain ⟨sI, hsI, hI⟩ := wholeIdeal_exists_principal_eq_of_localized_eq001 S J I
    (IsNoetherian.noetherian J) (IsNoetherian.noetherian I) heq
  obtain ⟨sE, hsE, hE⟩ := exists_principal_exact_matrix_row_of_localized_exact014 S
    N (hilbertBurchCofactors318 N) (hilbertBurchCofactors_mulVec_zero001 N) hexN
  refine ⟨sI * sE, N, S.mul_mem hsI hsE, fun r hr ↦ ?_⟩
  have hIr := hI r (dvd_trans ⟨sE, rfl⟩ hr)
  have hEr := hE r (dvd_trans ⟨sI, mul_comm _ _⟩ hr)
  have hrowr : (fun i ↦ algebraMap R (Localization.Away r)
      (hilbertBurchCofactors318 N i)) =
      hilbertBurchCofactors318 (N.map (algebraMap R (Localization.Away r))) :=
    funext (hilbertBurchCofactors_map318 (algebraMap R (Localization.Away r)) N)
  constructor
  · exact hIr.trans (hilbertBurchCofactorIdeal_map318 _ N)
  · rw [hrowr] at hEr
    exact hEr

end PfaffianDescent
end
