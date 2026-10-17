import PfaffianDescent.SchemeModuleInternalHomRankOneInverse
import PfaffianDescent.SchemeModuleBaseLinearCategory

/-! Canonical unit-to-internal-Hom map from the SAME original module
morphism. Sections are actual over-site restrictions of that morphism;
their original scalar multiples define the actual module-sheaf map.
No rank-one, inverse, increment or comparison premise is needed here.
SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.SchemeModuleInternalHom
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X : Scheme.{u}} {M N : X.Modules}

/-- An original global O-linear morphism gives its ACTUAL local Hom
section on every open, by restriction on the actual over-site. -/
def homSection (j : M ⟶ N) (U : X.Opens) : (sheaf M N).val.obj (op U) :=
  (sectionsEquivOver M N U).symm (j.over U)

/-- This section has the SAME original component values. -/
theorem homSection_apply (j : M ⟶ N) (U : X.Opens) (V : Over U)
    (m : M.val.obj (op V.left)) :
    (homSection j U).1.app (op V) m = j.val.app (op V.left) m := rfl

/-- Genuine restriction compatibility of the original Hom sections. -/
theorem homSection_restrict (j : M ⟶ N) {U V : X.Opens} (f : V ⟶ U) :
    (sheaf M N).val.map f.op (homSection j U) = homSection j V := by
  apply Subtype.ext
  apply NatTrans.ext
  funext W
  apply AddCommGrpCat.hom_ext
  ext m
  rfl

/-- The canonical O_X→internalHom(M,N) attached to the SAME original
morphism j. Its section on U sends r to r times the ACTUAL restriction
of j, for the independently defined original section-ring action. -/
def unitToHom (j : M ⟶ N) : SheafOfModules.unit X.ringCatSheaf ⟶ sheaf M N where
  val :=
    { app := fun U => ModuleCat.ofHom
        { toFun := fun r => r • homSection j U.unop
          map_add' := fun r s => add_smul r s _
          map_smul' := by
            intro r s
            change (r * s) • homSection j U.unop = r • (s • homSection j U.unop)
            exact mul_smul r s _ }
      naturality := by
        intro U V f
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro r
        change X.presheaf.map f r • homSection j V.unop =
          (sheaf M N).val.map f (r • homSection j U.unop)
        calc
          _ = X.presheaf.map f r • (sheaf M N).val.map f (homSection j U.unop) :=
            congrArg (X.presheaf.map f r • ·) (homSection_restrict j f.unop).symm
          _ = _ := ((sheaf M N).val.map_smul f r (homSection j U.unop)).symm }

/-- The canonical map is the original scalar multiple of the SAME
restricted morphism. -/
theorem unitToHom_apply (j : M ⟶ N) (U : X.Opens) (r : Γ(X, U)) :
    (unitToHom j).val.app (op U) r = r • homSection j U := rfl

/-- Every smaller component retains original ring restriction and the
SAME input morphism value; no affine comparison or generator is substituted. -/
theorem unitToHom_apply_component (j : M ⟶ N) (U : X.Opens) (r : Γ(X, U))
    (V : Over U) (m : M.val.obj (op V.left)) :
    ((unitToHom j).val.app (op U) r).1.app (op V) m =
      X.presheaf.map V.hom.op r • j.val.app (op V.left) m := rfl

/-- In particular, the value of the canonical map at 1 is the SAME
original restricted morphism. -/
theorem unitToHom_one (j : M ⟶ N) (U : X.Opens) :
    (unitToHom j).val.app (op U) (1 : Γ(X, U)) = homSection j U := by
  rw [unitToHom_apply, one_smul]

/-- Original pi-induced constants act through the ORIGINAL section
ring on both sides of the SAME canonical map. No transported K-action
or comparison-linearity hypothesis is used. -/
theorem unitToHom_originalBaseConstant
    {K : Type u} [Field K] (pi : X ⟶ Spec (CommRingCat.of K))
    (j : M ⟶ N) (U : X.Opens) (c : K) (r : Γ(X, U)) :
    (unitToHom j).val.app (op U) (schemeOpenBaseRingHom pi U c * r) =
      schemeOpenBaseRingHom pi U c • (unitToHom j).val.app (op U) r :=
  ((unitToHom j).val.app (op U)).hom.map_smul (schemeOpenBaseRingHom pi U c) r

end PfaffianDescent.SchemeModuleInternalHom
