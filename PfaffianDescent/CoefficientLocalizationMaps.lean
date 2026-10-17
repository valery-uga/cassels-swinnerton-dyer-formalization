import PfaffianDescent.AlternatingGeneratorEquations
import PfaffianDescent.LocalizationKernelMaps
import Mathlib.RingTheory.Localization.BaseChange

namespace PfaffianDescent
open TensorProduct
section
variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] (ι : Type*) [Fintype ι] [DecidableEq ι]

noncomputable def coefficientFunctionLinearMap : (ι → R) →ₗ[R] (ι → S) :=
  (TensorProduct.piScalarRight R S S ι).toLinearMap.restrictScalars R |>.comp
    (TensorProduct.mk R S (ι → R) 1)

lemma coefficientFunctionLinearMap_apply (v : ι → R) :
    coefficientFunctionLinearMap R S ι v = algebraMap R S ∘ v := by
  funext i
  change TensorProduct.piScalarRight R S S ι (1 ⊗ₜ[R] v) i = algebraMap R S (v i)
  simp [Algebra.smul_def]

instance coefficientFunctionLinearMap_isLocalizedModule (U : Submonoid R) [IsLocalization U S] :
    IsLocalizedModule U (coefficientFunctionLinearMap R S ι) :=
  IsLocalizedModule.of_linearEquiv U (TensorProduct.mk R S (ι → R) 1)
    ((TensorProduct.piScalarRight R S S ι).restrictScalars R)

end
section
variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]

instance ambientAlternating_isScalarTower :
    IsScalarTower R S (AlternatingTwoForms S ((Fin 3 → S) × (Fin 3 → S))) where
  smul_assoc r s B := by
    ext v
    exact smul_assoc r s (B v)

noncomputable def ambientAlternatingLinearMap :
    AlternatingTwoForms R ((Fin 3 → R) × (Fin 3 → R)) →ₗ[R]
      AlternatingTwoForms S ((Fin 3 → S) × (Fin 3 → S)) :=
  (ambientAlternatingTensorEquiv R S).toLinearMap.restrictScalars R |>.comp
    (TensorProduct.mk R S (AlternatingTwoForms R ((Fin 3 → R) × (Fin 3 → R))) 1)

lemma ambientAlternatingLinearMap_apply
    (B : AlternatingTwoForms R ((Fin 3 → R) × (Fin 3 → R))) :
    ambientAlternatingLinearMap R S B = ambientAlternatingMap (algebraMap R S) B :=
  ambientAlternatingTensorEquiv_one_tmul R S B

instance ambientAlternatingLinearMap_isLocalizedModule (U : Submonoid R) [IsLocalization U S] :
    IsLocalizedModule U (ambientAlternatingLinearMap R S) :=
  IsLocalizedModule.of_linearEquiv U
    (TensorProduct.mk R S (AlternatingTwoForms R ((Fin 3 → R) × (Fin 3 → R))) 1)
    ((ambientAlternatingTensorEquiv R S).restrictScalars R)

lemma alternatingGeneratorEvaluation_localization_commute {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → (Fin 3 → R) × (Fin 3 → R)) :
    ((alternatingGeneratorEvaluation (graphCoefficientMap (algebraMap R S) ∘ v)).restrictScalars R).comp
      (ambientAlternatingLinearMap R S) =
    (coefficientFunctionLinearMap R S (ι × ι)).comp (alternatingGeneratorEvaluation v) := by
  apply LinearMap.ext
  intro B
  change alternatingGeneratorEvaluation (graphCoefficientMap (algebraMap R S) ∘ v)
    (ambientAlternatingLinearMap R S B) =
      coefficientFunctionLinearMap R S (ι × ι) (alternatingGeneratorEvaluation v B)
  rw [ambientAlternatingLinearMap_apply, coefficientFunctionLinearMap_apply]
  exact alternatingGeneratorEvaluation_map (algebraMap R S) v B

/-- The actual kernel coefficient map, viewed over the original ring. -/
noncomputable def ambientAlternatingKernelLinearMap
    (W : Submodule R ((Fin 3 → R) × (Fin 3 → R))) :
    (alternatingRestriction R _ W).ker →ₗ[R]
      (alternatingRestriction S _ (grassmannianSubmoduleBaseChange (algebraMap R S) W)).ker :=
  ((ambientAlternatingLinearMap R S).comp (alternatingRestriction R _ W).ker.subtype).codRestrict
    (((alternatingRestriction S _ (grassmannianSubmoduleBaseChange (algebraMap R S) W)).ker).restrictScalars R)
    (fun B => by
      change alternatingRestriction S _ (grassmannianSubmoduleBaseChange (algebraMap R S) W)
        (ambientAlternatingLinearMap R S B.1) = 0
      rw [ambientAlternatingLinearMap_apply]
      exact ambientAlternatingMap_restriction_zero (algebraMap R S) W B.1 B.2)

lemma ambientAlternatingKernelLinearMap_val
    (W : Submodule R ((Fin 3 → R) × (Fin 3 → R))) (B : (alternatingRestriction R _ W).ker) :
    (ambientAlternatingKernelLinearMap R S W B).1 = ambientAlternatingLinearMap R S B.1 := rfl

end
end PfaffianDescent
