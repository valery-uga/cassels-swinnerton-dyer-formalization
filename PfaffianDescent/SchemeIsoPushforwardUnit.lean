import PfaffianDescent.VoisinStandardOpenExtVanishing
import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-!
# Pushing the structure sheaf across a scheme isomorphism

Restriction along a scheme isomorphism is an equivalence of module
categories.  Its right adjoint therefore carries the restricted structure
sheaf back to the original structure sheaf.  This small comparison is used
to transport finite-product decompositions through affine presentations.
-/

noncomputable section

namespace PfaffianDescent

open CategoryTheory AlgebraicGeometry

universe u

set_option linter.style.haveILetI false in
/-- Pushing the structure sheaf forward along a scheme isomorphism gives the
structure sheaf of the target. -/
noncomputable def schemeIsoPushforwardUnitIso
    {X Y : Scheme.{u}} (e : X ≅ Y) :
    (Scheme.Modules.pushforward e.hom).obj
        (SheafOfModules.unit X.ringCatSheaf) ≅
      SheafOfModules.unit Y.ringCatSheaf := by
  let E := schemeModulesEquivalenceOfIsoRestrict e.symm
  letI : (Scheme.Modules.restrictFunctor e.hom).IsEquivalence := by
    change E.functor.IsEquivalence
    infer_instance
  letI : (Scheme.Modules.restrictFunctor e.hom).Full :=
    Functor.IsEquivalence.full
  letI : (Scheme.Modules.restrictFunctor e.hom).Faithful :=
    Functor.IsEquivalence.faithful
  letI : IsIso (Adjunction.unit
      (Scheme.Modules.restrictAdjunction e.hom)) := by
    apply Adjunction.unit_isIso_of_L_fully_faithful
  letI : IsIso ((Scheme.Modules.restrictAdjunction e.hom).unit.app
      (SheafOfModules.unit Y.ringCatSheaf)) :=
    ((asIso (Adjunction.unit
      (Scheme.Modules.restrictAdjunction e.hom))).app
        (SheafOfModules.unit Y.ringCatSheaf)).isIso_hom
  exact
    (Scheme.Modules.pushforward e.hom).mapIso
        (Scheme.Modules.restrictUnitIso e.hom).symm ≪≫
      ((asIso ((Scheme.Modules.restrictAdjunction e.hom).unit.app
        (SheafOfModules.unit Y.ringCatSheaf))).symm)

end PfaffianDescent
