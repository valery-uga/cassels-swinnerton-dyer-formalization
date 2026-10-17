import PfaffianDescent.SchemeModuleRankOneGenericRestrictionInjective
import PfaffianDescent.SchemeModuleInternalHomRankOneEvaluation
import PfaffianDescent.SchemeModuleCoverEqualizer

/-! Actual original-pi function-field scalar and chart-to-function-field
section maps. The ground hom is ORIGINAL pi on global functions followed
by the original generic germ. It is independent of all module charts.
Primitive point callers construct the chart from actual ideal inclusion;
this generic helper keeps its ordinary actual local chart explicit.
SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
universe u
variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Original structure-map field hom: apply pi on top-open functions,
then the actual generic-point germ. No chart or comparison determines it. -/
def schemeFunctionFieldGroundRingHom (pi : X ⟶ Spec (CommRingCat.of K)) :
    K →+* X.functionField := by
  letI : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
  exact (X.germToFunctionField ⊤).hom.comp (affineFunctionHom pi)

/-- The actual function field carrying its original-pi scalar action. -/
def SchemeFunctionFieldOver (_pi : X ⟶ Spec (CommRingCat.of K)) := X.functionField

noncomputable instance schemeFunctionFieldOverAddCommGroup (pi : X ⟶ Spec (CommRingCat.of K)) :
    AddCommGroup (SchemeFunctionFieldOver pi) := inferInstanceAs (AddCommGroup X.functionField)

noncomputable instance schemeFunctionFieldOverModule (pi : X ⟶ Spec (CommRingCat.of K)) :
    Module K (SchemeFunctionFieldOver pi) :=
  Module.compHom X.functionField (schemeFunctionFieldGroundRingHom pi)

/-- Original-pi constants in the field are the same on every nonempty
open. This is the genuine original germ/restriction composition law. -/
theorem schemeFunctionFieldGroundRingHom_eq_openGerm
    (pi : X ⟶ Spec (CommRingCat.of K)) (U : X.Opens) [Nonempty U] (c : K) :
    schemeFunctionFieldGroundRingHom pi c =
      X.germToFunctionField U (schemeOpenBaseRingHom pi U c) := by
  have hgU : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using (inferInstance : Nonempty U))
  change X.presheaf.germ ⊤ (genericPoint X) trivial (affineFunctionHom pi c) =
    X.presheaf.germ U (genericPoint X) hgU
      (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op (affineFunctionHom pi c))
  exact (X.presheaf.germ_res_apply (homOfLE (show U ≤ ⊤ from le_top))
    (genericPoint X) hgU (affineFunctionHom pi c)).symm

/-- Actual O-linear chart coefficient followed by the actual function-field
germ, linear for independently existing original-pi scalars on both sides. -/
def schemeModuleChartSectionsToFunctionFieldLinearMap
    (pi : X ⟶ Spec (CommRingCat.of K)) (M : X.Modules)
    (U : X.Opens) [Nonempty U]
    (e : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U) :
    SchemeModuleOpenSectionsOver pi M U →ₗ[K] SchemeFunctionFieldOver pi where
  toFun s := X.germToFunctionField U (SchemeModuleInternalHom.overTopLinearEquiv M U e s)
  map_add' s t := by
    rw [(SchemeModuleInternalHom.overTopLinearEquiv M U e).map_add, map_add]
  map_smul' c s := by
    change M.val.obj (op U) at s
    let q := SchemeModuleInternalHom.overTopLinearEquiv M U e
    change X.germToFunctionField U (q (schemeOpenBaseRingHom pi U c • s)) =
      schemeFunctionFieldGroundRingHom pi c * X.germToFunctionField U (q s)
    rw [q.map_smul]
    change X.germToFunctionField U (schemeOpenBaseRingHom pi U c * q s) = _
    rw [map_mul, ← schemeFunctionFieldGroundRingHom_eq_openGerm pi U c]

/-- True injectivity on the actual chart sections. -/
theorem schemeModuleChartSectionsToFunctionFieldLinearMap_injective
    (pi : X ⟶ Spec (CommRingCat.of K)) (M : X.Modules)
    (U : X.Opens) [Nonempty U]
    (e : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U) :
    Function.Injective (schemeModuleChartSectionsToFunctionFieldLinearMap pi M U e) :=
  (X.germToFunctionField_injective U).comp
    (SchemeModuleInternalHom.overTopLinearEquiv M U e).injective

/-- ACTUAL top-open sections mapped through an actual generic-point chart;
restriction and both scalar laws are the existing original maps. -/
def schemeModuleTopSectionsToFunctionFieldLinearMap
    (pi : X ⟶ Spec (CommRingCat.of K)) (M : X.Modules)
    (U : X.Opens) (hgU : genericPoint X ∈ U)
    (e : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U) :
    SchemeModuleOpenSectionsOver pi M ⊤ →ₗ[K] SchemeFunctionFieldOver pi := by
  letI : Nonempty U := ⟨⟨genericPoint X, hgU⟩⟩
  exact (schemeModuleChartSectionsToFunctionFieldLinearMap pi M U e).comp
    (schemeModuleOpenSectionsRestrictionLinearMap pi M (show U ≤ ⊤ from le_top))

/-- Genuine global injectivity from integral/rank-one geometry and the
actual field/germ law; no restriction-injectivity certificate is supplied. -/
theorem schemeModuleTopSectionsToFunctionFieldLinearMap_injective
    (pi : X ⟶ Spec (CommRingCat.of K)) (M : X.Modules)
    (hM : schemeModuleLocallyRankOne M) (U : X.Opens) (hgU : genericPoint X ∈ U)
    (e : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U) :
    Function.Injective (schemeModuleTopSectionsToFunctionFieldLinearMap pi M U hgU e) := by
  letI : Nonempty U := ⟨⟨genericPoint X, hgU⟩⟩
  exact (schemeModuleChartSectionsToFunctionFieldLinearMap_injective pi M U e).comp
    (schemeModuleLocallyRankOne_topRestriction_injective M hM U hgU)

end PfaffianDescent
