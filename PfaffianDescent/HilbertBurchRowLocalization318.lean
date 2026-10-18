import Mathlib.RingTheory.Localization.AtPrime.Basic
import PfaffianDescent.HilbertBurchMatrixLocalization318
import PfaffianDescent.HilbertBurchCofactorSplitTop318
import PfaffianDescent.HilbertBurchArtinianLowHeight318

/-!
Combine coefficientwise matrix localization, low-height support exclusion,
and the split exact cofactor-ideal theorem. The localized matrix and its
exactness are obtained from the original presentation.
-/

noncomputable section

namespace AllCharacteristics.HilbertSurfaceDraft

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

def rowFunctional008 {ι : Type*} [Fintype ι] (a : ι → R) : (ι → R) →ₗ[R] R :=
  dotProductBilin R R a

@[simp] theorem rowFunctional008_apply {ι : Type*} [Fintype ι]
    (a z : ι → R) : rowFunctional008 a z = dotProduct a z := rfl

theorem localized_row_map008 (P : Submonoid R) [IsLocalization P S]
    {ι : Type*} [Fintype ι] (a : ι → R) :
    IsLocalizedModule.map P
      (coordinateScalarMap007 (R := R) (S := S) ι)
      (Algebra.linearMap R S) (rowFunctional008 a) =
      (rowFunctional008 (fun i ↦ algebraMap R S (a i))).restrictScalars R := by
  apply IsLocalizedModule.linearMap_ext P
    (coordinateScalarMap007 (R := R) (S := S) ι) (Algebra.linearMap R S)
  ext u
  rw [LinearMap.comp_apply, IsLocalizedModule.map_apply]
  change algebraMap R S (∑ i, a i * u i) =
    ∑ i, algebraMap R S (a i) * algebraMap R S (u i)
  simp only [map_sum, map_mul]

theorem exact_matrix_row_map_localization008
    (P : Submonoid R) [IsLocalization P S]
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (M : Matrix κ ι R) (a : κ → R)
    (hex : Function.Exact M.mulVecLin (rowFunctional008 a)) :
    Function.Exact (M.map (algebraMap R S)).mulVecLin
      (rowFunctional008 (fun i ↦ algebraMap R S (a i))) := by
  have h := IsLocalizedModule.map_exact P
    (coordinateScalarMap007 (R := R) (S := S) ι)
    (coordinateScalarMap007 (R := R) (S := S) κ)
    (Algebra.linearMap R S) M.mulVecLin (rowFunctional008 a) hex
  rw [localized_matrix_map007, localized_row_map008] at h
  exact h

/-- A generator outside a prime gives an explicit section of the localized
row, by putting its inverse in a single coordinate. -/
theorem exists_section_localized_row008
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : Ideal R) [p.IsPrime] [IsLocalization p.primeCompl S]
    (a : ι → R) (hnot : ¬ Ideal.span (Set.range a) ≤ p) :
    ∃ v : ι → S, rowFunctional008 (fun i ↦ algebraMap R S (a i)) v = 1 := by
  have hgen : ∃ i, a i ∉ p := by
    by_contra! h
    exact hnot (Ideal.span_le.mpr (Set.range_subset_iff.mpr h))
  obtain ⟨i, hi⟩ := hgen
  have hunit : IsUnit (algebraMap R S (a i)) :=
    IsLocalization.map_units S (⟨a i, hi⟩ : p.primeCompl)
  obtain ⟨u, hu⟩ := hunit
  refine ⟨Pi.single i (↑(u⁻¹) : S), ?_⟩
  rw [rowFunctional008_apply, dotProduct_single, ← hu]
  simp

/-- The actual cofactor ideal becomes the unit ideal at every prime of
height at most one, for any finite-colength ideal with an injective exact
matrix presentation on a local surface. -/
theorem cofactorIdeal_localization_eq_top_at_lowHeight008
    [IsLocalRing R] (hdim : ringKrullDim R = 2)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (I : Ideal R) [IsArtinianRing (R ⧸ I)]
    (M : Matrix (Option ι) ι R) (a : Option ι → R)
    (hI : I = Ideal.span (Set.range a))
    (hg : Function.Injective M.mulVecLin)
    (hgf : LinearMap.range M.mulVecLin = LinearMap.ker (rowFunctional008 a))
    (p : Ideal R) [p.IsPrime] (hpheight : p.height ≤ 1) :
    Ideal.span (Set.range (PfaffianDescent.hilbertBurchCofactors318
      (M.map (algebraMap R (Localization.AtPrime p))))) = ⊤ := by
  have hnot : ¬ Ideal.span (Set.range a) ≤ p := by
    rw [← hI]
    exact not_le_prime_height_le_one_of_artinian_quotient hdim I p hpheight
  obtain ⟨v, hv⟩ := exists_section_localized_row008
    (S := Localization.AtPrime p) p a hnot
  have hginj := injective_matrix_map_localization007 p.primeCompl
    (S := Localization.AtPrime p) M hg
  have hex := exact_matrix_row_map_localization008 p.primeCompl
    (S := Localization.AtPrime p) M a (LinearMap.exact_iff.mpr hgf.symm)
  exact PfaffianDescent.hilbertBurchCofactorIdeal_eq_top_of_split_exact006
    (M.map (algebraMap R (Localization.AtPrime p)))
    (rowFunctional008 (fun i ↦ algebraMap R (Localization.AtPrime p) (a i)))
    hginj hex.linearMap_ker_eq.symm v hv

end AllCharacteristics.HilbertSurfaceDraft
