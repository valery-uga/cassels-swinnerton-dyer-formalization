import PfaffianDescent.SchemeModuleInternalHomUnitMap
import PfaffianDescent.SchemeModuleCoverEqualizer

/-! SOURCE ONLY. Genuine native module-Hom descent through the constructed
O-linear internal Hom sheaf. No global Hom/Iso certificate is presumed; whole
compatibility of actual local maps is the ordinary input to the sheaf axiom. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open SchemeModuleInternalHom
universe u
variable {X : Scheme.{u}} (M N : X.Modules)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private instance nativeWholeHomSectionModule (Q : X.Modules) (U : X.Opens) :
    Module Γ(X, U) (Q.val.obj (op U)) := (Q.val.obj (op U)).isModule

/-- An actual internal-Hom section on top defines an ACTUAL original-scalar
module-sheaf morphism. Every component uses the original top-over inclusion. -/
def schemeModuleHomOfActualInternalHomTopSection
    (a : Γ(SchemeModuleInternalHom.sheaf M N, ⊤)) : M ⟶ N where
  val :=
    { app := fun U => ModuleCat.ofHom
        { toFun := fun m => a.1.app (op (Over.mk (homOfLE (show U.unop ≤ ⊤ from le_top)))) m
          map_add' := fun m n =>
            (a.1.app (op (Over.mk (homOfLE (show U.unop ≤ ⊤ from le_top))))).hom.map_add m n
          map_smul' := fun r m =>
            a.2 (Over.mk (homOfLE (show U.unop ≤ ⊤ from le_top))) r m }
      naturality := by
        intro U V f
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro m
        let t : Over.mk (homOfLE (show V.unop ≤ ⊤ from le_top)) ⟶
            Over.mk (homOfLE (show U.unop ≤ ⊤ from le_top)) :=
          Over.homMk f.unop (Subsingleton.elim _ _)
        exact ConcreteCategory.congr_hom (a.1.naturality t.op) m }

/-- Literal native component values of the constructed morphism. -/
theorem schemeModuleHomOfActualInternalHomTopSection_apply
    (a : Γ(SchemeModuleInternalHom.sheaf M N, ⊤)) (U : X.Opens) (m : Γ(M, U)) :
    (schemeModuleHomOfActualInternalHomTopSection M N a).val.app (op U) m =
      a.1.app (op (Over.mk (homOfLE (show U ≤ ⊤ from le_top)))) m := rfl

/-- Constructing from the actual section of an original global morphism
recovers that SAME entire morphism, preserving every original component. -/
theorem schemeModuleHomOfActualInternalHomTopSection_homSection (f : M ⟶ N) :
    schemeModuleHomOfActualInternalHomTopSection M N (homSection f ⊤) = f := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  rfl

/-- Restricting the constructed original morphism to the top-over site
recovers the WHOLE original Hom section, not only its top-component value. -/
theorem homSection_schemeModuleHomOfActualInternalHomTopSection
    (a : Γ(SchemeModuleInternalHom.sheaf M N, ⊤)) :
    homSection (schemeModuleHomOfActualInternalHomTopSection M N a) ⊤ = a := by
  apply Subtype.ext
  apply NatTrans.ext
  funext V
  cases V with
  | op V =>
      rcases V with ⟨W, z, f⟩
      cases z
      have hf : f = homOfLE (show W ≤ (⊤ : X.Opens) from le_top) :=
        Subsingleton.elim _ _
      cases hf
      apply AddCommGrpCat.hom_ext
      ext m
      rfl

/-- Actual global Hom/top-section equivalence for the original Hom sheaf. -/
def schemeModuleActualInternalHomTopEquiv :
    Γ(SchemeModuleInternalHom.sheaf M N, ⊤) ≃ (M ⟶ N) where
  toFun := schemeModuleHomOfActualInternalHomTopSection M N
  invFun f := homSection f ⊤
  left_inv := homSection_schemeModuleHomOfActualInternalHomTopSection M N
  right_inv := schemeModuleHomOfActualInternalHomTopSection_homSection M N

/-- Compatible actual local morphisms glue by the GENUINE Hom sheaf axiom.
This helper will consume internally derived native chart maps and overlap
identities in the final parametrization caller; it is not that final caller. -/
def schemeModuleHomGlueOfActualCompatibleOverMorphisms
    {ι : Type u} (U : ι → X.Opens) (hcover : ⨆ i, U i = ⊤)
    (f : ∀ i, M.over (U i) ⟶ N.over (U i))
    (hcompat : ∀ i j,
      (SchemeModuleInternalHom.sheaf M N).val.map
          (homOfLE (show U i ⊓ U j ≤ U i from inf_le_left)).op
          ((sectionsEquivOver M N (U i)).symm (f i)) =
        (SchemeModuleInternalHom.sheaf M N).val.map
          (homOfLE (show U i ⊓ U j ≤ U j from inf_le_right)).op
          ((sectionsEquivOver M N (U j)).symm (f j))) : M ⟶ N :=
  schemeModuleHomOfActualInternalHomTopSection M N
    (schemeModuleCompatibleCoverSectionsGlue (SchemeModuleInternalHom.sheaf M N)
      ⊤ U (fun _ => le_top) hcover.ge
      ⟨fun i => (sectionsEquivOver M N (U i)).symm (f i), hcompat⟩)

/-- The glued ACTUAL morphism has exactly the original actual local maps
as WHOLE internal-Hom sections, retaining all smaller-open components. -/
theorem schemeModuleHomGlueOfActualCompatibleOverMorphisms_homSection
    {ι : Type u} (U : ι → X.Opens) (hcover : ⨆ i, U i = ⊤)
    (f : ∀ i, M.over (U i) ⟶ N.over (U i))
    (hcompat : ∀ i j,
      (SchemeModuleInternalHom.sheaf M N).val.map
          (homOfLE (show U i ⊓ U j ≤ U i from inf_le_left)).op
          ((sectionsEquivOver M N (U i)).symm (f i)) =
        (SchemeModuleInternalHom.sheaf M N).val.map
          (homOfLE (show U i ⊓ U j ≤ U j from inf_le_right)).op
          ((sectionsEquivOver M N (U j)).symm (f j))) (i : ι) :
    homSection (schemeModuleHomGlueOfActualCompatibleOverMorphisms M N U hcover f hcompat)
        (U i) = (sectionsEquivOver M N (U i)).symm (f i) := by
  rw [← homSection_restrict _ (homOfLE (show U i ≤ ⊤ from le_top))]
  unfold schemeModuleHomGlueOfActualCompatibleOverMorphisms
  rw [homSection_schemeModuleHomOfActualInternalHomTopSection]
  exact schemeModuleCompatibleCoverSectionsGlue_restrict
    (SchemeModuleInternalHom.sheaf M N) ⊤ U (fun _ => le_top) hcover.ge
    ⟨fun i => (sectionsEquivOver M N (U i)).symm (f i), hcompat⟩ i

end PfaffianDescent
