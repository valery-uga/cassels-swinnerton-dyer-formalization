import PfaffianDescent.VoisinFieldBaseChangeOpen

/-! # Actual pulled rank-two trivializations on inverse-image opens -/
noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
open BundleSectionZeroLocus
universe u
set_option backward.isDefEq.respectTransparency false

def serreIncidenceFreeOverIsoOfRestriction
    {X : Scheme.{u}} (M : X.Modules) (U : X.Opens) (I : Type u)
    (t : SheafOfModules.free (R := (U : Scheme.{u}).ringCatSheaf) I ≅ M.restrict U.ι) :
    SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U :=
  (Scheme.Modules.overEquiv U).unitIso.app _ ≪≫
    (Scheme.Modules.overEquiv U).inverse.mapIso
      ((overEquivFreeIso (X := X) U I).symm ≪≫ t ≪≫
        ((Scheme.Modules.overFunctorEquiv U).app M).symm) ≪≫
    ((Scheme.Modules.overEquiv U).unitIso.app (M.over U)).symm

def serreIncidenceFieldPulledFreeOverIso
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of K)) (M : X.Modules)
    (U : X.Opens) (I : Type u)
    (t : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U) :
    let g := schemeFieldBaseChangeToOriginal (L := L) base
    let V := g ⁻¹ᵁ U
    SheafOfModules.free (R := (schemeFieldBaseChange (L := L) base).ringCatSheaf.over V) I ≅
      ((Scheme.Modules.pullback g).obj M).over V :=
  serreIncidenceFreeOverIsoOfRestriction _ _ I
    (schemeFieldBaseChangeOpenRestrictedFreeIso (L := L) base M U I t)

end PfaffianDescent
