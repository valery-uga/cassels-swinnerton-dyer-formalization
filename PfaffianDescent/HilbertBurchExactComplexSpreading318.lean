import PfaffianDescent.HilbertBurchRowLocalization318
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.Localization.Away.Basic

/-!
Spreads all relations of a finite matrix complex from an arbitrary
localization to one principal neighborhood. Whole-ideal equality alone
does not supply this exactness statement.
-/

noncomputable section

namespace AllCharacteristics.HilbertSurfaceDraft

section Submodules

variable {R T M N : Type*} [CommRing R] [CommRing T] [Algebra R T]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module T N] [IsScalarTower R T N]
    (P : Submonoid R) [IsLocalization P T]
    (f : M →ₗ[R] N) [IsLocalizedModule P f]

/-- One denominator controls containment of an entire finite generated
submodule after localization. The localization model f is arbitrary. -/
theorem exists_submodule_uniformMultiplier_of_localized_le014
    (U V : Submodule R M) (hU : U.FG)
    (hle : U.localized' T P f ≤ V.localized' T P f) :
    ∃ s : P, ∀ x ∈ U, (s : R) • x ∈ V := by
  letI : Module.Finite R U := Module.Finite.of_fg hU
  let q := V.toLocalizedQuotient' T P f
  let h : U →ₗ[R] M ⧸ V := V.mkQ.comp U.subtype
  have hzero : q.comp h = q.comp (0 : U →ₗ[R] M ⧸ V) := by
    apply LinearMap.ext
    intro u
    simp only [q, h, LinearMap.comp_apply, LinearMap.zero_apply, map_zero,
      Submodule.mkQ_apply, Submodule.toLocalizedQuotient'_mk]
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact hle (U.toLocalized' T P f u).property
  obtain ⟨s, hs⟩ := Module.Finite.exists_smul_of_comp_eq_of_isLocalizedModule P q h 0 hzero
  refine ⟨s, fun x hx ↦ ?_⟩
  have hsx := congrArg (fun l : U →ₗ[R] M ⧸ V ↦ l ⟨x, hx⟩) hs
  change s • V.mkQ x = s • (0 : M ⧸ V) at hsx
  have hsx' : (s : R) • V.mkQ x = 0 := by
    simpa only [Submonoid.smul_def, smul_zero] using hsx
  apply (Submodule.Quotient.mk_eq_zero V).mp
  change V.mkQ ((s : R) • x) = 0
  rw [map_smul]
  exact hsx'

/-- A uniform multiplier that becomes a unit gives whole localized
submodule containment, including all localization denominators. -/
theorem localized_submodule_le_of_uniformMultiplier014
    (U V : Submodule R M) (s : R) (hs : IsUnit (algebraMap R T s))
    (hmult : ∀ x ∈ U, s • x ∈ V) :
    U.localized' T P f ≤ V.localized' T P f := by
  rw [Submodule.localized'_eq_span]
  apply Submodule.span_le.mpr
  rintro _ ⟨x, hx, rfl⟩
  apply ((V.localized' T P f).smul_mem_iff_of_isUnit hs).mp
  have hmem := (V.toLocalized' T P f ⟨s • x, hmult x hx⟩).property
  change f (s • x) ∈ V.localized' T P f at hmem
  simpa only [IsScalarTower.algebraMap_smul, map_smul] using hmem

end Submodules

section Matrices

variable {R : Type*} [CommRing R]

theorem localized_row_kernel_eq014 (P : Submonoid R)
    {κ : Type*} [Fintype κ] (a : κ → R) :
    (LinearMap.ker (rowFunctional008 a)).localized' (Localization P) P
      (coordinateScalarMap007 (R := R) (S := Localization P) κ) =
      LinearMap.ker (rowFunctional008 (fun i ↦ algebraMap R (Localization P) (a i))) := by
  rw [LinearMap.localized'_ker_eq_ker_localizedMap (Localization P) P
    (coordinateScalarMap007 (R := R) (S := Localization P) κ)
    (Algebra.linearMap R (Localization P)) (rowFunctional008 a)]
  rw [localized_row_map008]
  rfl

theorem localized_matrix_range_eq014 (P : Submonoid R)
    {ι κ : Type*} [Fintype ι] [Fintype κ] (M : Matrix κ ι R) :
    (LinearMap.range M.mulVecLin).localized' (Localization P) P
      (coordinateScalarMap007 (R := R) (S := Localization P) κ) =
      LinearMap.range (M.map (algebraMap R (Localization P))).mulVecLin := by
  rw [LinearMap.localized'_range_eq_range_localizedMap (Localization P) P
    (coordinateScalarMap007 (R := R) (S := Localization P) ι)
    (coordinateScalarMap007 (R := R) (S := Localization P) κ) M.mulVecLin]
  rw [localized_matrix_map007]
  rfl

/-- A matrix complex exact over the finite-support localization is exact
on ONE principal open avoiding every support point, and on every further
principal shrinking. The complex relation itself is retained globally. -/
theorem exists_principal_exact_matrix_row_of_localized_exact014
    [IsNoetherianRing R] (P : Submonoid R)
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (M : Matrix κ ι R) (a : κ → R)
    (hcomplex : ∀ u, rowFunctional008 a (M.mulVecLin u) = 0)
    (hex : Function.Exact (M.map (algebraMap R (Localization P))).mulVecLin
      (rowFunctional008 (fun i ↦ algebraMap R (Localization P) (a i)))) :
    ∃ s : R, s ∈ P ∧ ∀ r : R, s ∣ r →
      Function.Exact (M.map (algebraMap R (Localization.Away r))).mulVecLin
        (rowFunctional008 (fun i ↦ algebraMap R (Localization.Away r) (a i))) := by
  let U := LinearMap.ker (rowFunctional008 a)
  let V := LinearMap.range M.mulVecLin
  have hloc : U.localized' (Localization P) P
      (coordinateScalarMap007 (R := R) (S := Localization P) κ) ≤
      V.localized' (Localization P) P
        (coordinateScalarMap007 (R := R) (S := Localization P) κ) := by
    rw [localized_row_kernel_eq014, localized_matrix_range_eq014]
    exact hex.linearMap_ker_eq.le
  obtain ⟨s, hs⟩ := exists_submodule_uniformMultiplier_of_localized_le014 P
    (coordinateScalarMap007 (R := R) (S := Localization P) κ) U V
    (IsNoetherian.noetherian U) hloc
  refine ⟨s, s.property, fun r hsr ↦ ?_⟩
  apply LinearMap.exact_iff.mpr
  rw [← localized_row_kernel_eq014 (Submonoid.powers r),
    ← localized_matrix_range_eq014 (Submonoid.powers r)]
  apply le_antisymm
  · apply localized_submodule_le_of_uniformMultiplier014 (Submonoid.powers r)
      (coordinateScalarMap007 (R := R) (S := Localization.Away r) κ) U V (s : R)
    · exact isUnit_of_dvd_unit (map_dvd (algebraMap R (Localization.Away r)) hsr)
        (IsLocalization.Away.algebraMap_isUnit r)
    · exact hs
  · intro y hy
    obtain ⟨x, hx, t, ht⟩ := hy
    refine ⟨x, ?_, t, ht⟩
    obtain ⟨u, rfl⟩ := hx
    exact hcomplex u

end Matrices

end AllCharacteristics.HilbertSurfaceDraft
