import PfaffianDescent.P3HomogeneousGlobalSectionsLinear

/- SOURCE ONLY / UNVERIFIED. Morphism-valued raw homogeneous section
really is unitHomEquiv of the original compatible homogeneous section. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
set_option backward.isDefEq.respectTransparency false
attribute [local instance] MvPolynomial.gradedAlgebra

lemma p3HomogeneousGlobalSectionLinearMap_unitHom
    (K : Type u) [Field K] (m : ℕ)
    (a : MvPolynomial.homogeneousSubmodule (Fin 4) K m) :
    p3HomogeneousGlobalSectionLinearMap K m a =
      (positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) m).unitHomEquiv.symm
        (positiveGlobalSectionOfHomogeneous (MvPolynomial.homogeneousSubmodule (Fin 4) K) m a) := by
  let M := positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) m
  let s := positiveGlobalSectionOfHomogeneous
    (MvPolynomial.homogeneousSubmodule (Fin 4) K) m a
  change M.unitHomEquiv.symm
      ((schemeModuleSectionsEquivTop M).symm (schemeModuleSectionsEquivTop M s)) =
    M.unitHomEquiv.symm s
  exact congrArg M.unitHomEquiv.symm
    ((schemeModuleSectionsEquivTop M).symm_apply_apply s)

end PfaffianDescent
