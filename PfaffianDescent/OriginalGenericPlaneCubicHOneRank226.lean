import PfaffianDescent.CorayActualGenericPlaneSectionH1RankOne

/-! Literal equation transport of the accepted native generic-section H1
rank, including its independently defined hypersurfaceToBase scalar action.
No scheme normalization or arbitrary genus certificate is substituted. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Equality of actual equations transports their actual native H1 and
original base action together. The homogeneous witnesses are proof-irrelevant. -/
theorem planeCubicEquation_unitHOne_finiteRank_transport226
    (p q : MvPolynomial (Fin 3) K) (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3)
    (heq : p = q) :
    (let X := hypersurface p hp
     letI : EnoughInjectives X.Modules := sheafOfModules_enoughInjectives X.ringCatSheaf
     letI : HasExt.{u} X.Modules :=
       CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} X.Modules
     letI : Linear K X.Modules := schemeModulesLinearOver (hypersurfaceToBase p hp)
     Module.Finite K (schemeModuleCohomology X (SheafOfModules.unit X.ringCatSheaf) 1) ∧
       Module.finrank K (schemeModuleCohomology X
         (SheafOfModules.unit X.ringCatSheaf) 1) = 1) →
    (let X := hypersurface q hq
     letI : EnoughInjectives X.Modules := sheafOfModules_enoughInjectives X.ringCatSheaf
     letI : HasExt.{u} X.Modules :=
       CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} X.Modules
     letI : Linear K X.Modules := schemeModulesLinearOver (hypersurfaceToBase q hq)
     Module.Finite K (schemeModuleCohomology X (SheafOfModules.unit X.ringCatSheaf) 1) ∧
       Module.finrank K (schemeModuleCohomology X
         (SheafOfModules.unit X.ringCatSheaf) 1) = 1) := by
  subst q
  exact fun h => h

/-- ORIGINAL smooth cubic inputs give rank-one H1 of the literal original
`genericPlaneCubic` with its own original parameter-field scalar action. -/
theorem smoothCubic_genericPlaneCubic_unit_cohomology_one_finite_finrank_eq_one226
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] :
    let L := GenericHyperplaneField K
    let q := genericPlaneCubic p
    let hq := genericPlaneCubic_isHomogeneous p hp
    let X := hypersurface q hq
    letI : EnoughInjectives X.Modules := sheafOfModules_enoughInjectives X.ringCatSheaf
    letI : HasExt.{u} X.Modules :=
      CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} X.Modules
    letI : Linear L X.Modules := schemeModulesLinearOver (hypersurfaceToBase q hq)
    Module.Finite L (schemeModuleCohomology X (SheafOfModules.unit X.ringCatSheaf) 1) ∧
      Module.finrank L (schemeModuleCohomology X
        (SheafOfModules.unit X.ringCatSheaf) 1) = 1 := by
  let L := GenericHyperplaneField K
  let q := PfaffianDescent.rectangularSubstitution
    (genericPlaneInclusionMatrix (K := K)) (p.map (algebraMap K L))
  let hq := PfaffianDescent.rectangularSubstitution_homogeneous
    (genericPlaneInclusionMatrix (K := K)) (hp.map (algebraMap K L))
  exact planeCubicEquation_unitHOne_finiteRank_transport226
    q (genericPlaneCubic p) hq (genericPlaneCubic_isHomogeneous p hp)
    (genericPlaneInclusionMatrix_restrictedEquation p)
    (smoothCubic_actualLinearGenericPlaneSection_unit_cohomology_one_finite_finrank_eq_one
      p hp hp0)

end PfaffianDescent.Coray
