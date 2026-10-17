import PfaffianDescent.FrobeniusCoextension
import PfaffianDescent.CoextensionExact
import PfaffianDescent.PrincipalRingInjective

namespace PfaffianDescent
open ModuleCat CategoryTheory
universe u
section
variable {R A F : Type u} [CommRing R] [IsPrincipalIdealRing R]
    [CommRing A] [Algebra R A] [Module.Projective R A]
    [Field F] [Algebra R F] [FaithfulSMul R F]

include F in
/-- A projective Frobenius algebra over a principal ideal ring has self-injective
dimension at most one. The proof coextends the explicit sequence into a faithful
field algebra and its quotient. -/
theorem frobenius_self_injectiveDimensionLE_one (ell : Module.Dual R A)
    (hell : Function.Bijective (ringMultiplicationDual ell)) :
    HasInjectiveDimensionLE (ModuleCat.of A A) 1 := by
  let i : R →ₗ[R] F := Algebra.linearMap R F
  let S : ShortComplex (ModuleCat R) := ModuleCat.shortComplexOfCompEqZero
    i i.range.mkQ i.exact_map_mkQ_range.linearMap_comp_eq_zero
  have hi : Function.Injective i := FaithfulSMul.algebraMap_injective R F
  have hS : S.ShortExact := ModuleCat.shortComplex_shortExact S
    i.exact_map_mkQ_range hi (Submodule.mkQ_surjective _)
  letI : Module.Projective R ((restrictScalars (algebraMap R A)).obj (ModuleCat.of A A)) :=
    Module.Projective.of_equiv (restrictionRegularEquiv (R := R) (A := A)).symm
  letI : CategoryTheory.Injective (ModuleCat.of R F) :=
    (Module.injective_iff_injective_object R F).mp fieldModule_injective
  letI : CategoryTheory.Injective (ModuleCat.of R (F ⧸ i.range)) :=
    (Module.injective_iff_injective_object R (F ⧸ i.range)).mp
      (fieldModule_quotient_injective i.range)
  have hT := coextension_shortExact (algebraMap R A) S hS
  letI : CategoryTheory.Injective (S.map (coextendScalars (algebraMap R A))).X₂ :=
    coextension_injective (algebraMap R A) (ModuleCat.of R F) inferInstance
  letI : CategoryTheory.Injective (S.map (coextendScalars (algebraMap R A))).X₃ :=
    coextension_injective (algebraMap R A) (ModuleCat.of R (F ⧸ i.range)) inferInstance
  have hd : HasInjectiveDimensionLE
      ((coextendScalars (algebraMap R A)).obj (ModuleCat.of R R)) 1 :=
    hT.hasInjectiveDimensionLT_X₁ 1 inferInstance inferInstance
  exact (ModuleCat.hasInjectiveDimensionLE_iff_of_linearEquiv
    (frobeniusCoextensionEquiv ell hell) 1).mpr hd

end
end PfaffianDescent
