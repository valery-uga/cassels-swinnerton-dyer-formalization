import PfaffianDescent.SchemeModuleRestrictStalkLinear
import PfaffianDescent.CubicClosedPointSerreTensorStalkPullbackRestriction

noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

/-- An actual map invertible on an actual open is invertible on the native
module stalk at each point of that open. -/
theorem cubicClosedPointSerreTensorStalk_map_isIso_of_restrict
    {X : Scheme.{u}} (U : X.Opens) (x : U)
    {M N : X.Modules} (g : M ⟶ N)
    [IsIso ((Scheme.Modules.restrictFunctor U.ι).map g)] :
    IsIso ((schemeModuleStalkModuleFunctor X (U.ι x)).map g) := by
  let L := Scheme.Modules.restrictFunctor U.ι ⋙ schemeModuleStalkFunctor (U : Scheme) x
  let e := Scheme.Modules.restrictStalkNatIso U.ι x
  have hL : IsIso (L.map g) := by
    dsimp only [L, Functor.comp_map]
    infer_instance
  have hR : IsIso ((schemeModuleStalkFunctor X (U.ι x)).map g) :=
    (NatIso.isIso_map_iff e g).mp hL
  let F := forget₂ (ModuleCat (X.presheaf.stalk (U.ι x))) AddCommGrpCat
  let a := (schemeModuleStalkModuleFunctor X (U.ι x)).map g
  letI : IsIso (F.map a) := hR
  exact isIso_of_reflects_iso a F

end PfaffianDescent
