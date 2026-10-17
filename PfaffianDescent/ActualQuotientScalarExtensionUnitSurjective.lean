import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/- SOURCE ONLY / UNVERIFIED. A quotient ring gives an ACTUAL surjective
scalar-extension unit for every module, with no finite/free premise. -/
noncomputable section
namespace PfaffianDescent
open CategoryTheory ModuleCat TensorProduct
open scoped TensorProduct
universe u

theorem actualQuotientScalarExtension_oneTensor_surjective
    {R S M : Type u} [CommRing R] [CommRing S] [AddCommGroup M]
    [Module R M] [Algebra R S]
    (hquot : Function.Surjective (algebraMap R S)) :
    Function.Surjective (fun m : M => (1 : S) ⊗ₜ[R] m) := by
  intro z
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul s m =>
      obtain ⟨r, hr⟩ := hquot s
      refine ⟨r • m, ?_⟩
      rw [TensorProduct.tmul_smul, Algebra.smul_def, mul_one, hr]
  | add x y hx hy =>
      obtain ⟨m, hm⟩ := hx
      obtain ⟨n, hn⟩ := hy
      exact ⟨m + n, by rw [TensorProduct.tmul_add, hm, hn]⟩

theorem actualQuotientScalarExtension_adjunctionUnit_surjective
    {R S : Type u} [CommRing R] [CommRing S]
    (rho : R →+* S) (hquot : Function.Surjective rho) (M : ModuleCat R) :
    Function.Surjective ((ModuleCat.extendRestrictScalarsAdj rho).unit.app M) := by
  letI : Algebra R S := rho.toAlgebra
  simpa only [ModuleCat.extendRestrictScalarsAdj_unit_app_apply] using
    actualQuotientScalarExtension_oneTensor_surjective (M := M) hquot

theorem actualQuotientScalarExtension_adjunctionUnit_epi
    {R S : Type u} [CommRing R] [CommRing S]
    (rho : R →+* S) (hquot : Function.Surjective rho) (M : ModuleCat R) :
    Epi ((ModuleCat.extendRestrictScalarsAdj rho).unit.app M) :=
  (ModuleCat.epi_iff_surjective _).2
    (actualQuotientScalarExtension_adjunctionUnit_surjective rho hquot M)

end PfaffianDescent
