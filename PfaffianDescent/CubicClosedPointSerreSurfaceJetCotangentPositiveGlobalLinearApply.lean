import PfaffianDescent.ProjectivePositiveGlobalSectionsLinear

noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
open ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

private theorem globalSectionLinearOfTop_eq_unitHom
    {K : Type u} [Field K] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of K)) (M : X.Modules) (s : M.sections) :
    (schemeModuleGlobalSectionsLinearEquivOpenTop p M).symm (s.val (Opposite.op ⊤)) =
      M.unitHomEquiv.symm s := by
  apply M.unitHomEquiv.injective
  rw [Equiv.apply_symm_apply]
  dsimp [schemeModuleGlobalSectionsLinearEquivOpenTop,
    schemeModuleGlobalSectionsAddEquivOpenTop, schemeModuleGlobalSectionsOverEquivSections]
  erw [Equiv.apply_symm_apply]
  change (schemeModuleSectionsEquivTop M).symm
    ((schemeModuleSectionsEquivTop M) s) = s
  exact (schemeModuleSectionsEquivTop M).symm_apply_apply s

/-- The native linear global cubic model is the literal morphism of its
checked compatible family of positive sections. -/
abbrev cubicClosedPointSerreSurfaceJetCotangent_positiveGlobalLinearApply
    {K : Type u} [Field K]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (q : grading I 3) :=
  globalSectionLinearOfTop_eq_unitHom (toBase I)
    (positiveSheafOfModules (grading I) 3)
    (positiveGlobalSectionOfHomogeneous (grading I) 3 q)

end PfaffianDescent
