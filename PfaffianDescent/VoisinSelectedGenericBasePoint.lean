import PfaffianDescent.VoisinSelectedQuotientFunctionField

/-! The generic point of a compatible selected ordered chart lies over the
generic unordered cubic configuration. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem selectedOrderedChart_genericPoint_over_cubicGenericBase
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [IsIntegral (cubicConfigurationBase p hp 8)]
    {U Q : Scheme.{u}} [IsIntegral U] [IsIntegral Q]
    (i : U ⟶ (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 8).left)
    (j : Q ⟶ cubicConfigurationBase p hp 8) [IsOpenImmersion j]
    (r : U ⟶ Q) [Surjective r]
    (hcomm : i ≫ configurationQuotientMap (equationIdeal p hp) 8 =
      r ≫ j) :
    configurationQuotientMap (equationIdeal p hp) 8
        (i (genericPoint U)) =
      (cubicConfigurationBase p hp 8).fromSpecStalk
        (genericPoint (cubicConfigurationBase p hp 8))
        (IsLocalRing.closedPoint
          (cubicConfigurationBase p hp 8).functionField) := by
  have hmap : configurationQuotientMap (equationIdeal p hp) 8
        (i (genericPoint U)) = genericPoint (cubicConfigurationBase p hp 8) := by
    have hpt := congrArg (fun f => f (genericPoint U)) hcomm
    have hleft : configurationQuotientMap (equationIdeal p hp) 8
        (i (genericPoint U)) =
        (i ≫ configurationQuotientMap (equationIdeal p hp) 8)
          (genericPoint U) := rfl
    have hright : (r ≫ j) (genericPoint U) =
        j (r (genericPoint U)) := rfl
    exact hleft.trans (hpt.trans (hright.trans
      ((congrArg j (affineSurjectiveIntegral_genericPoint_map r)).trans
        (genericPoint_eq_of_isOpenImmersion j))))
  exact hmap.trans Scheme.fromSpecStalk_closedPoint.symm

end PfaffianDescent
