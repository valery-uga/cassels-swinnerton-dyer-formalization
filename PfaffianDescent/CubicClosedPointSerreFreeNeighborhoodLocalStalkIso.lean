import PfaffianDescent.CubicClosedPointSerreFreeNeighborhoodLocalStalk

/-! # Native ambient stalk isomorphisms detect the actual local stalk map -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

/-- Invertibility of the constructed ambient native stalk map implies
invertibility of the actual local-scheme stalk map. -/
theorem cubicClosedPointSerreFreeNeighborhood_local_stalk_isIso
    {X : Scheme.{u}} (U : X.Opens) (x : U) (M N : X.Modules)
    (p : M.restrict U.ι ⟶ N.restrict U.ι)
    [IsIso (cubicClosedPointSerreFreeNeighborhoodLocalStalkMap U x M N p)] :
    IsIso ((schemeModuleStalkModuleFunctor (U : Scheme) x).map p) := by
  let c := cubicClosedPointSerreFreeNeighborhoodLocalStalkMap U x M N p
  let F := forget₂ (ModuleCat (X.presheaf.stalk (U.ι x))) AddCommGrpCat
  let a := (Scheme.Modules.restrictStalkNatIso U.ι x).app M
  let b := (Scheme.Modules.restrictStalkNatIso U.ι x).app N
  let k := (schemeModuleStalkFunctor (U : Scheme) x).map p
  have hc : F.map c = a.inv ≫ k ≫ b.hom := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro m
    rfl
  have hcomp : IsIso ((a.inv ≫ k) ≫ b.hom) := by
    rw [Category.assoc, ← hc]
    exact Functor.map_isIso F c
  letI := hcomp
  have hleft : IsIso (a.inv ≫ k) := IsIso.of_isIso_comp_right _ b.hom
  letI := hleft
  have hk : IsIso k := IsIso.of_isIso_comp_left a.inv k
  have hh : IsIso ((forget₂ (ModuleCat ((U : Scheme).presheaf.stalk x)) AddCommGrpCat).map
      ((schemeModuleStalkModuleFunctor (U : Scheme) x).map p)) := by
    change IsIso k
    exact hk
  letI := hh
  exact isIso_of_reflects_iso _
    (forget₂ (ModuleCat ((U : Scheme).presheaf.stalk x)) AddCommGrpCat)

end PfaffianDescent
