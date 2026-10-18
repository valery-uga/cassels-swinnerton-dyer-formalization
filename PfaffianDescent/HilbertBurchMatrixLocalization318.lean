import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
Localization preserves exactness and injectivity of the actual coefficientwise
mapped matrices, in their standard coordinate modules.
-/

noncomputable section

namespace AllCharacteristics.HilbertSurfaceDraft

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- The standard coordinatewise scalar map for a finite free module. -/
def coordinateScalarMap007 (ι : Type*) : (ι → R) →ₗ[R] (ι → S) :=
  LinearMap.pi fun i ↦ (Algebra.linearMap R S).comp (LinearMap.proj i)

@[simp] theorem coordinateScalarMap007_apply (ι : Type*) (u : ι → R) (i : ι) :
    coordinateScalarMap007 (S := S) ι u i = algebraMap R S (u i) := rfl

variable (P : Submonoid R) [IsLocalization P S]

instance coordinateScalarMap007_isLocalized (ι : Type*) [Finite ι] :
    IsLocalizedModule P (coordinateScalarMap007 (R := R) (S := S) ι) := by
  dsimp only [coordinateScalarMap007]
  infer_instance

/-- The universal localized map is the map given by the coefficientwise
localized matrix.  This is proved by checking coordinatewise finite sums. -/
theorem localized_matrix_map007
    {ι κ : Type*} [Fintype ι] [Fintype κ] (M : Matrix κ ι R) :
    IsLocalizedModule.map P
      (coordinateScalarMap007 (R := R) (S := S) ι)
      (coordinateScalarMap007 (R := R) (S := S) κ) M.mulVecLin =
      ((M.map (algebraMap R S)).mulVecLin).restrictScalars R := by
  apply IsLocalizedModule.linearMap_ext P
    (coordinateScalarMap007 (R := R) (S := S) ι)
    (coordinateScalarMap007 (R := R) (S := S) κ)
  ext u i
  simp only [LinearMap.comp_apply, IsLocalizedModule.map_apply,
    coordinateScalarMap007_apply, Matrix.mulVecLin_apply, Matrix.mulVec,
    dotProduct, Matrix.map_apply, map_sum, map_mul, LinearMap.restrictScalars_apply]

/-- Exactness is preserved for the actual localized matrix maps.  The
right-hand matrix need not be surjective before or after localization. -/
theorem exact_matrix_map_localization007
    (P : Submonoid R) [IsLocalization P S]
    {ι κ ζ : Type*} [Fintype ι] [Fintype κ] [Fintype ζ]
    (M : Matrix κ ι R) (N : Matrix ζ κ R)
    (hex : Function.Exact M.mulVecLin N.mulVecLin) :
    Function.Exact (M.map (algebraMap R S)).mulVecLin
      (N.map (algebraMap R S)).mulVecLin := by
  have h := IsLocalizedModule.map_exact P
    (coordinateScalarMap007 (R := R) (S := S) ι)
    (coordinateScalarMap007 (R := R) (S := S) κ)
    (coordinateScalarMap007 (R := R) (S := S) ζ)
    M.mulVecLin N.mulVecLin hex
  rw [localized_matrix_map007, localized_matrix_map007] at h
  exact h

/-- Injectivity is preserved for the actual localized matrix. -/
theorem injective_matrix_map_localization007
    (P : Submonoid R) [IsLocalization P S]
    {ι κ : Type*} [Fintype ι] [Fintype κ] (M : Matrix κ ι R)
    (hinj : Function.Injective M.mulVecLin) :
    Function.Injective (M.map (algebraMap R S)).mulVecLin := by
  have h := IsLocalizedModule.map_injective P
    (coordinateScalarMap007 (R := R) (S := S) ι)
    (coordinateScalarMap007 (R := R) (S := S) κ) M.mulVecLin hinj
  rw [localized_matrix_map007] at h
  exact h

end AllCharacteristics.HilbertSurfaceDraft
