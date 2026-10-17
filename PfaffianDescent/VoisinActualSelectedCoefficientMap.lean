import PfaffianDescent.VoisinGenericResidueChartLift
import PfaffianDescent.VoisinAffineCoefficientGenericEvaluation

/-! The selected ordered generic residue point evaluates the original
cubic coefficients through the regular affine chart coefficient map. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem selectedGeneric_coefficientMap_eq
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [IsIntegral (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 8).left]
    {U : Scheme.{u}} [IsIntegral U]
    (i : U ⟶ (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 8).left) [IsOpenImmersion i] :
    let O := (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 8).left
    let F := O.residueField (i (genericPoint U))
    let s := openImmersion_genericResidueLift i
    let f : Γ(U, ⊤) →+* F :=
      (Scheme.ΓSpecIso (.of F)).hom.hom.comp s.appTop.hom
    f.comp (affineFunctionHom (i ≫
      (orderedFamilyConfigurationOver
        (hypersurfaceToBase p hp) 8).hom)) =
      (Spec.preimage (s ≫ i ≫
        (orderedFamilyConfigurationOver
          (hypersurfaceToBase p hp) 8).hom)).hom := by
  dsimp only
  exact affineFunctionHom_genericFieldEvaluation U
    (openImmersion_genericResidueLift i)
    (i ≫ (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 8).hom)

end PfaffianDescent
