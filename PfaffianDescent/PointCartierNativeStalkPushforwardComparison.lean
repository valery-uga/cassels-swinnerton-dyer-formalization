import PfaffianDescent.PointCartierNativeStalkPushforwardLinear
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-! # Pushforward followed by the actual module stalk is restriction of scalars

The comparison is the actual sheaf stalk-pushforward map. Its linearity is
proved on germs and its invertibility uses that the scheme map is inducing.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace PfaffianDescent

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Topology

universe u

def pointCartierNativeStalkPushforwardMap
    {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) (M : X.Modules) :
    (schemeModuleStalkModuleFunctor Y (f x)).obj ((Scheme.Modules.pushforward f).obj M) ⟶
      (ModuleCat.restrictScalars (f.stalkMap x).hom).obj
        ((schemeModuleStalkModuleFunctor X x).obj M) := by
  letI := schemeModuleStalkModule ((Scheme.Modules.pushforward f).obj M) (f x)
  letI := schemeModuleStalkModule M x
  letI : Module (Y.presheaf.stalk (f x)) (M.presheaf.stalk x) :=
    ((ModuleCat.restrictScalars (f.stalkMap x).hom).obj
      ((schemeModuleStalkModuleFunctor X x).obj M)).isModule
  exact ModuleCat.ofHom
    (X := (schemeModuleStalkModuleFunctor Y (f x)).obj ((Scheme.Modules.pushforward f).obj M))
    (Y := (ModuleCat.restrictScalars (f.stalkMap x).hom).obj
      ((schemeModuleStalkModuleFunctor X x).obj M))
    { toFun := (M.presheaf.stalkPushforward AddCommGrpCat f.base x).hom
      map_add' := (M.presheaf.stalkPushforward AddCommGrpCat f.base x).hom.map_add
      map_smul' := pointCartierNativeStalkPushforward_smul f x M }

def pointCartierNativeStalkPushforwardIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : IsInducing f.base) (x : X) (M : X.Modules) :
    (schemeModuleStalkModuleFunctor Y (f x)).obj ((Scheme.Modules.pushforward f).obj M) ≅
      (ModuleCat.restrictScalars (f.stalkMap x).hom).obj
        ((schemeModuleStalkModuleFunctor X x).obj M) := by
  letI : IsIso (M.presheaf.stalkPushforward AddCommGrpCat f.base x) :=
    TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
      AddCommGrpCat hf M.presheaf x
  exact (LinearEquiv.ofBijective (pointCartierNativeStalkPushforwardMap f x M).hom
    (ConcreteCategory.bijective_of_isIso
      (M.presheaf.stalkPushforward AddCommGrpCat f.base x))).toModuleIso

@[simp]
theorem pointCartierNativeStalkPushforwardIso_hom
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : IsInducing f.base) (x : X) (M : X.Modules) :
    (pointCartierNativeStalkPushforwardIso f hf x M).hom =
      pointCartierNativeStalkPushforwardMap f x M := rfl

/-- The native module-stalk functors commute with pushforward, with the
surface stalk regarded as an ambient module through the actual stalk ring map. -/
def pointCartierNativeStalkPushforwardNatIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : IsInducing f.base) (x : X) :
    Scheme.Modules.pushforward f ⋙ schemeModuleStalkModuleFunctor Y (f x) ≅
      schemeModuleStalkModuleFunctor X x ⋙ ModuleCat.restrictScalars (f.stalkMap x).hom := by
  refine NatIso.ofComponents (pointCartierNativeStalkPushforwardIso f hf x) ?_
  intro M N η
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  exact ConcreteCategory.congr_hom
    ((presheafStalkPushforwardNatTrans
      (C := AddCommGrpCat) f.base x).naturality
        ((Scheme.Modules.toPresheaf X).map η)) m

end PfaffianDescent
