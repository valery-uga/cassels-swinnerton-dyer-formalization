import PfaffianDescent.HilbertBurchSurfaceResolution318
import PfaffianDescent.HilbertBurchRowLocalization318
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.RingTheory.LocalProperties.Projective

/-!
The actual kernel of one global generator row localizes to the actual
kernel of the mapped row. Regular local surface rings supply freeness,
and rank=n-1 is derived for that fixed row, regardless of varying minimal
numbers of local ideal generators.
-/

noncomputable section

namespace AllCharacteristics.HilbertSurfaceDraft

variable {R : Type*} [CommRing R]

def rowIdealSurjection013 {ι : Type*} [Fintype ι] (a : ι → R) :
    (ι → R) →ₗ[R] Ideal.span (Set.range a) :=
  (Fintype.linearCombination R a).codRestrict (Ideal.span (Set.range a))
    (fun z ↦ by
      change (∑ i, z i • a i) ∈ Ideal.span (Set.range a)
      exact Submodule.sum_mem _ (fun i _ ↦
        Submodule.smul_mem _ (z i) (Ideal.subset_span (Set.mem_range_self i))))

theorem rowIdealSurjection013_surjective {ι : Type*} [Fintype ι] (a : ι → R) :
    Function.Surjective (rowIdealSurjection013 a) := by
  intro z
  have hz : (z : R) ∈ LinearMap.range (Fintype.linearCombination R a) := by
    rw [Fintype.range_linearCombination]
    exact z.property
  obtain ⟨u, hu⟩ := hz
  exact ⟨u, Subtype.ext hu⟩

theorem rowIdealSurjection013_ker {ι : Type*} [Fintype ι] (a : ι → R) :
    LinearMap.ker (rowIdealSurjection013 a) = LinearMap.ker (rowFunctional008 a) := by
  have hrow : (Ideal.span (Set.range a)).subtype.comp (rowIdealSurjection013 a) =
      rowFunctional008 a := by
    apply LinearMap.ext
    intro z
    change (∑ i, z i * a i) = ∑ i, a i * z i
    exact Finset.sum_congr rfl (fun i _ ↦ mul_comm _ _)
  rw [← hrow, LinearMap.ker_comp, Submodule.ker_subtype]
  rfl

/-- Kernel localization in standard coordinates, including its actual
localization module structure rather than an assumed isomorphism. -/
def localizedRowKernelEquiv013 (P : Submonoid R)
    {ι : Type*} [Fintype ι] (a : ι → R) :
    LocalizedModule P (LinearMap.ker (rowFunctional008 a)) ≃ₗ[Localization P]
      LinearMap.ker (rowFunctional008 (fun i ↦ algebraMap R (Localization P) (a i))) := by
  let K := LinearMap.ker (rowFunctional008 a)
  let L := Localization P
  let f := coordinateScalarMap007 (R := R) (S := L) ι
  have hker : K.localized' L P f =
      LinearMap.ker (rowFunctional008 (fun i ↦ algebraMap R L (a i))) := by
    rw [LinearMap.localized'_ker_eq_ker_localizedMap L P f
      (Algebra.linearMap R L) (rowFunctional008 a)]
    rw [localized_row_map008]
    rfl
  let e := (IsLocalizedModule.linearEquiv P
    (LocalizedModule.mkLinearMap P K) (K.toLocalized' L P f)).extendScalarsOfIsLocalization P L
  exact e.trans (LinearEquiv.ofEq _ _ hker)

/-- Every localization of this fixed row kernel is free when the actual
localized coefficient ring is a regular local surface ring. -/
theorem free_localized_row_kernel_regular_surface013
    (P : Submonoid R) [IsRegularLocalRing (Localization P)]
    (hdim : ringKrullDim (Localization P) = 2)
    {ι : Type*} [Fintype ι] (a : ι → R) :
    Module.Free (Localization P) (LocalizedModule P (LinearMap.ker (rowFunctional008 a))) := by
  let L := Localization P
  let aL : ι → L := fun i ↦ algebraMap R L (a i)
  let J := Ideal.span (Set.range aL)
  let f := rowIdealSurjection013 aL
  letI : Module.Free L (LinearMap.ker f) :=
    free_ker_to_ideal_regularLocal_dim_two hdim J f
  letI : Module.Free L (LinearMap.ker (rowFunctional008 aL)) :=
    Module.Free.of_equiv (LinearEquiv.ofEq _ _ (rowIdealSurjection013_ker aL))
  exact Module.Free.of_equiv (localizedRowKernelEquiv013 P a).symm

/-- The rank is determined by the number n of GLOBAL generators.  It does
not vary with the minimal number needed at individual support points. -/
theorem finrank_localized_row_kernel_add_one013
    (P : Submonoid R) [IsRegularLocalRing (Localization P)]
    (hdim : ringKrullDim (Localization P) = 2)
    {n : ℕ} (a : Fin n → R)
    (hJ : Ideal.span (Set.range (fun i ↦ algebraMap R (Localization P) (a i))) ≠ ⊥) :
    Module.finrank (Localization P)
      (LocalizedModule P (LinearMap.ker (rowFunctional008 a))) + 1 = n := by
  let L := Localization P
  let aL : Fin n → L := fun i ↦ algebraMap R L (a i)
  letI : IsDomain L := isDomain_of_regularLocalRing L
  have h := finrank_ker_add_one_of_surjective_to_nonzero_ideal
    (Ideal.span (Set.range aL)) hJ (rowIdealSurjection013 aL)
    (rowIdealSurjection013_surjective aL)
  rw [rowIdealSurjection013_ker] at h
  rw [(localizedRowKernelEquiv013 P a).finrank_eq]
  exact h

/-- Local regularity of the actual maximal-local coefficient rings derives
projectivity of the original global row kernel.  It is not a presentation
or syzygy-flatness input. Applied after finite-support semilocalization,
this supplies the flatness needed by the semilocal basis construction. -/
theorem projective_row_kernel_of_regular_surface_maximal_localizations013
    [IsNoetherianRing R] {ι : Type*} [Fintype ι] (a : ι → R)
    (hreg : ∀ (p : Ideal R) (_ : p.IsMaximal),
      IsRegularLocalRing (Localization.AtPrime p))
    (hdim : ∀ (p : Ideal R) (_ : p.IsMaximal),
      ringKrullDim (Localization.AtPrime p) = 2) :
    Module.Projective R (LinearMap.ker (rowFunctional008 a)) := by
  let K := LinearMap.ker (rowFunctional008 a)
  letI : Module.FinitePresentation R K := Module.finitePresentation_of_finite R K
  apply Module.projective_of_localization_maximal
  intro p hp
  letI : p.IsMaximal := hp
  letI : IsRegularLocalRing (Localization.AtPrime p) := hreg p hp
  letI : Module.Free (Localization.AtPrime p) (LocalizedModule p.primeCompl K) :=
    free_localized_row_kernel_regular_surface013 p.primeCompl (hdim p hp) a
  infer_instance

end AllCharacteristics.HilbertSurfaceDraft
