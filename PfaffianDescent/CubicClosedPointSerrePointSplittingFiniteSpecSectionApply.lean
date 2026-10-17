import PfaffianDescent.CubicClosedPointSerrePointSplittingFiniteSpecSections

noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
open BundleSectionZeroLocus
universe u
set_option backward.isDefEq.respectTransparency false
attribute [local instance] isIso_pullbackUnitComparison

theorem pointSplittingGlobalSectionsOverBaseCongr_apply
    {F : Type u} [Field F] {D : Scheme.{u}}
    (p q : D ⟶ Spec (.of F)) (h : p = q) (N : D.Modules)
    (s : SchemeModuleGlobalSectionsOver p N) :
    (pointSplittingGlobalSectionsOverBaseCongr p q h N s :
      SheafOfModules.unit D.ringCatSheaf ⟶ N) = s := by
  subst q
  rfl

/-- The canonical finite-scheme Gamma comparison carries the SAME actual
section to its literal pullback on Spec Gamma(D), despite the base-action transport. -/
theorem pointSplittingFiniteSpecSectionsEquiv_section
    {F : Type u} [Field F] {X D : Scheme.{u}}
    (base : X ⟶ Spec (.of F)) (d : D ⟶ X) [IsFinite (d ≫ base)] [IsAffine D]
    (M : X.Modules)
    (s : SchemeModuleGlobalSectionsOver (d ≫ base) ((Scheme.Modules.pullback d).obj M)) :
    letI := finiteSchemeCoefficientAlgebra (d ≫ base)
    let N := (Scheme.Modules.pullback d).obj M
    let NA := (Scheme.Modules.pullback D.isoSpec.inv).obj N
    NA.unitHomEquiv (pointSplittingFiniteSpecSectionsEquiv base d M s) =
      pullbackSection D.isoSpec.inv N (isIso_pullbackUnitComparison _) (N.unitHomEquiv s) := by
  letI := finiteSchemeCoefficientAlgebra (d ≫ base)
  dsimp only [pointSplittingFiniteSpecSectionsEquiv, LinearEquiv.trans_apply]
  erw [pointSplittingGlobalSectionsOverBaseCongr_apply]
  apply ((Scheme.Modules.pullback D.isoSpec.inv).obj
    ((Scheme.Modules.pullback d).obj M)).unitHomEquiv.symm.injective
  rw [Equiv.symm_apply_apply, pullbackSection_unitHomEquiv_symm_eq_inv,
    Equiv.symm_apply_apply]
  rfl

end PfaffianDescent
