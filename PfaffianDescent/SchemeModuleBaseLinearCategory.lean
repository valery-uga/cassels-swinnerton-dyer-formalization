import PfaffianDescent.SchemeModuleCoverEqualizer
import PfaffianDescent.SectionRepresenterScalar
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear

/-! The actual base morphism induces actual pointwise K-linear Hom spaces.
No Hom/Ext scalar action is transported through a desired comparison.
The local section action is exactly the existing pi-induced action.
STATUS: UNVERIFIED source only. Root owns compiler checks.
-/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {K : Type u} [Field K] {X : Scheme.{u}}

/-- Actual base constants commute with actual restrictions on opens. -/
theorem schemeOpenBaseRingHom_restrict
    (pi : X ⟶ Spec (CommRingCat.of K)) {U V : X.Opens} (i : V ⟶ U) (c : K) :
    X.presheaf.map i.op (schemeOpenBaseRingHom pi U c) =
      schemeOpenBaseRingHom pi V c := by
  change X.presheaf.map i.op
      (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op (affineFunctionHom pi c)) =
    X.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op (affineFunctionHom pi c)
  have h := ConcreteCategory.congr_hom (X.presheaf.map_comp
    (homOfLE (show U ≤ ⊤ from le_top)).op i.op) (affineFunctionHom pi c)
  have hi : (homOfLE (show U ≤ ⊤ from le_top)).op ≫ i.op =
      (homOfLE (show V ≤ ⊤ from le_top)).op := Subsingleton.elim _ _
  rw [hi] at h
  exact h.symm

/-- Value-based extensionality for actual scheme-module morphisms, using
explicit installed Hom/ModuleCat/LinearMap extensionality projections. -/
theorem schemeModuleHom_ext_sections {M N : X.Modules} {f g : M ⟶ N}
    (h : ∀ (U : X.Opens) (s : M.val.obj (op U)),
      f.val.app (op U) s = g.val.app (op U) s) : f = g := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  exact h U.unop s

/-- Scalar multiplication of an actual module morphism by an actual base
field constant. Every component is the original local-ring-linear map
multiplied by the actual pi-induced local constant. -/
def schemeModuleHomBaseSmul (pi : X ⟶ Spec (CommRingCat.of K))
    {M N : X.Modules} (c : K) (f : M ⟶ N) : M ⟶ N where
  val :=
    { app := fun U => ModuleCat.ofHom
        { toFun := fun s => schemeOpenBaseRingHom pi U.unop c • f.val.app U s
          map_add' := by
            intro s t
            rw [(f.val.app U).hom.map_add, smul_add]
          map_smul' := by
            intro r s
            letI : CommRing ((X.ringCatSheaf.obj).obj U) :=
              inferInstanceAs (CommRing Γ(X, U.unop))
            rw [(f.val.app U).hom.map_smul]
            change (schemeOpenBaseRingHom pi U.unop c : (X.ringCatSheaf.obj).obj U) •
                (r • f.val.app U s) =
              r • ((schemeOpenBaseRingHom pi U.unop c : (X.ringCatSheaf.obj).obj U) •
                f.val.app U s)
            exact @smul_comm ((X.ringCatSheaf.obj).obj U)
              ((X.ringCatSheaf.obj).obj U) (N.val.obj U) _ _
              (smulCommClass_self ((X.ringCatSheaf.obj).obj U) (N.val.obj U))
              (schemeOpenBaseRingHom pi U.unop c) r (f.val.app U s) }
      naturality := by
        intro U V i
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro s
        change schemeOpenBaseRingHom pi V.unop c • f.val.app V (M.val.map i s) =
          N.val.map i (schemeOpenBaseRingHom pi U.unop c • f.val.app U s)
        rw [N.val.map_smul]
        change schemeOpenBaseRingHom pi V.unop c • f.val.app V (M.val.map i s) =
          X.presheaf.map i (schemeOpenBaseRingHom pi U.unop c) •
            N.val.map i (f.val.app U s)
        have hc : X.presheaf.map i (schemeOpenBaseRingHom pi U.unop c) =
            schemeOpenBaseRingHom pi V.unop c :=
          schemeOpenBaseRingHom_restrict pi i.unop c
        exact (congrArg (schemeOpenBaseRingHom pi V.unop c • ·)
          (PresheafOfModules.naturality_apply f.val i s)).trans
            (congrArg (fun a : Γ(X, V.unop) => a • N.val.map i (f.val.app U s)) hc.symm) }

/-- The actual constructed scalar morphism evaluates by the SAME existing
pi-induced scalar action on actual section values. -/
theorem schemeModuleHomBaseSmul_apply (pi : X ⟶ Spec (CommRingCat.of K))
    {M N : X.Modules} (c : K) (f : M ⟶ N) (U : X.Opens)
    (s : M.val.obj (op U)) :
    (schemeModuleHomBaseSmul pi c f).val.app (op U) s =
      schemeOpenBaseRingHom pi U c • f.val.app (op U) s := rfl

/-- The actual base-field module structure on actual Hom groups, proved
pointwise from the actual ring hom and original section module structures.
It is not defined by pulling back scalars along any comparison equivalence. -/
def schemeModuleHomModuleOver (pi : X ⟶ Spec (CommRingCat.of K))
    (M N : X.Modules) : Module K (M ⟶ N) where
  smul c f := schemeModuleHomBaseSmul pi c f
  one_smul f := by
    apply schemeModuleHom_ext_sections
    intro U s
    change schemeOpenBaseRingHom pi U 1 • f.val.app (op U) s = f.val.app (op U) s
    rw [map_one, one_smul]
  mul_smul c d f := by
    apply schemeModuleHom_ext_sections
    intro U s
    change schemeOpenBaseRingHom pi U (c * d) • f.val.app (op U) s =
      schemeOpenBaseRingHom pi U c • (schemeOpenBaseRingHom pi U d • f.val.app (op U) s)
    rw [map_mul, mul_smul]
  smul_zero c := by
    apply schemeModuleHom_ext_sections
    intro U s
    change schemeOpenBaseRingHom pi U c • (0 : N.val.obj (op U)) = 0
    exact smul_zero _
  smul_add c f g := by
    apply schemeModuleHom_ext_sections
    intro U s
    change schemeOpenBaseRingHom pi U c • (f.val.app (op U) s + g.val.app (op U) s) =
      schemeOpenBaseRingHom pi U c • f.val.app (op U) s +
        schemeOpenBaseRingHom pi U c • g.val.app (op U) s
    exact smul_add _ _ _
  add_smul c d f := by
    apply schemeModuleHom_ext_sections
    intro U s
    change schemeOpenBaseRingHom pi U (c + d) • f.val.app (op U) s =
      schemeOpenBaseRingHom pi U c • f.val.app (op U) s +
        schemeOpenBaseRingHom pi U d • f.val.app (op U) s
    rw [map_add, add_smul]
  zero_smul f := by
    apply schemeModuleHom_ext_sections
    intro U s
    change schemeOpenBaseRingHom pi U 0 • f.val.app (op U) s = 0
    rw [map_zero, zero_smul]

/-- Actual scheme-module composition is K-linear for the actual base
morphism. This explicit construction avoids a global instance ambiguity
when the same scheme is considered over different base morphisms. -/
def schemeModulesLinearOver (pi : X ⟶ Spec (CommRingCat.of K)) : Linear K X.Modules where
  homModule := schemeModuleHomModuleOver pi
  smul_comp M N P c f g := by
    apply schemeModuleHom_ext_sections
    intro U s
    change g.val.app (op U)
        (schemeOpenBaseRingHom pi U c • f.val.app (op U) s) =
      schemeOpenBaseRingHom pi U c • g.val.app (op U) (f.val.app (op U) s)
    exact (g.val.app (op U)).hom.map_smul _ _
  comp_smul M N P f c g := by
    apply schemeModuleHom_ext_sections
    intro U s
    rfl

/-- The actual categorical K-action agrees with the original base-field
action on each actual section value, rather than replacing that action. -/
theorem schemeModuleHom_smul_apply (pi : X ⟶ Spec (CommRingCat.of K))
    {M N : X.Modules} (c : K) (f : M ⟶ N) (U : X.Opens)
    (s : M.val.obj (op U)) :
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    (c • f).val.app (op U) s =
      c • (show SchemeModuleOpenSectionsOver pi N U from f.val.app (op U) s) := by
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  rfl

/-- Actual section-representer Yoneda is K-linear for the original base
morphism and the genuine original section action. -/
def schemeSectionRepresenterHomLinearEquiv (pi : X ⟶ Spec (CommRingCat.of K))
    (U : X.Opens) (M : X.Modules) :
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    ((show X.Modules from sectionRepresenter X.ringCatSheaf U) ⟶ M) ≃ₗ[K] SchemeModuleOpenSectionsOver pi M U := by
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  refine
    { toAddEquiv := sectionRepresenterHomAddEquiv X.ringCatSheaf U M
      map_smul' := ?_ }
  intro c f
  have hc : c • f = f ≫ (c • 𝟙 M) := by simp
  rw [hc]
  change sectionRepresenterHomEquiv X.ringCatSheaf U M (f ≫ (c • 𝟙 M)) = _
  rw [sectionRepresenterHomEquiv_postcomp]
  rfl

/-- The installed Ext-module is now available from the actual base-linear
category. Its scalar is the actual postcomposition by actual multiplication
on the coefficient module, not transport through a cohomology comparison. -/
theorem schemeModuleExt_smul_eq_actual_postcomp
    (pi : X ⟶ Spec (CommRingCat.of K)) [HasExt.{u} X.Modules]
    {M N : X.Modules} {n : ℕ} (z : Ext.{u} M N n) (c : K) :
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    c • z = z.comp (Ext.mk₀ (schemeModuleHomBaseSmul pi c (𝟙 N))) (add_zero n) := by
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  exact Ext.smul_eq_comp_mk₀ z c

end PfaffianDescent.Coray
