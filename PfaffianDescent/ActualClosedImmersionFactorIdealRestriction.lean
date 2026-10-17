import PfaffianDescent.IdealSheafModule
import PfaffianDescent.BundleSectionZeroLocus
import PfaffianDescent.SchemeModuleGlobalSections

/- SOURCE ONLY / UNVERIFIED. Restrict the actual AMBIENT ideal of the
composite closed point to the original subscheme and factor it through
that subscheme's actual point ideal. No flatness, kernel equality or
comparison certificate is an input. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open BundleSectionZeroLocus IdealSheafDataModule
universe u
set_option backward.isDefEq.respectTransparency false

def actualClosedImmersionFactorPushforwardComparison
    {Y X Z : Scheme.{u}} (i : X ⟶ Y) (q : Z ⟶ X) :
    (Scheme.Modules.pullback i).obj
        ((Scheme.Modules.pushforward (q ≫ i)).obj (schemeModuleUnit Z)) ⟶
      (Scheme.Modules.pushforward q).obj (schemeModuleUnit Z) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction i).homEquiv _ _).symm
    ((Scheme.Modules.pushforwardComp q i).app (schemeModuleUnit Z)).inv

lemma actualClosedImmersionFactorPushforwardComparison_unit
    {Y X Z : Scheme.{u}} (i : X ⟶ Y) (q : Z ⟶ X) :
    (Scheme.Modules.pullback i).map
        (closedImmersionUnitToPushforwardUnit (q ≫ i)) ≫
      actualClosedImmersionFactorPushforwardComparison i q =
    pullbackUnitComparison i ≫ closedImmersionUnitToPushforwardUnit q := by
  let adj := Scheme.Modules.pullbackPushforwardAdjunction i
  let e := (Scheme.Modules.pushforwardComp q i).app (schemeModuleUnit Z)
  have hc : closedImmersionUnitToPushforwardUnit (q ≫ i) ≫ e.inv =
      closedImmersionUnitToPushforwardUnit i ≫
        (Scheme.Modules.pushforward i).map (closedImmersionUnitToPushforwardUnit q) := by
    have hcomp : closedImmersionUnitToPushforwardUnit (q ≫ i) =
        closedImmersionUnitToPushforwardUnit i ≫
          (Scheme.Modules.pushforward i).map (closedImmersionUnitToPushforwardUnit q) ≫
            e.hom := unitToPushforwardObjUnit_comp q i
    exact (congrArg (fun m : schemeModuleUnit Y ⟶
        (Scheme.Modules.pushforward (q ≫ i)).obj (schemeModuleUnit Z) => m ≫ e.inv)
      hcomp).trans (by
        simp only [Category.assoc, e.hom_inv_id]
        exact congrArg (fun m => closedImmersionUnitToPushforwardUnit i ≫ m)
          (Category.comp_id ((Scheme.Modules.pushforward i).map
            (closedImmersionUnitToPushforwardUnit q))))
  have hu : (adj.homEquiv _ _).symm (closedImmersionUnitToPushforwardUnit i) =
      pullbackUnitComparison i := by
    apply (adj.homEquiv _ _).injective
    rw [Equiv.apply_symm_apply]
    exact (SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
      i.toRingCatSheafHom).symm
  change (Scheme.Modules.pullback i).map
      (closedImmersionUnitToPushforwardUnit (q ≫ i)) ≫ (adj.homEquiv _ _).symm e.inv = _
  rw [← adj.homEquiv_naturality_left_symm, hc,
    adj.homEquiv_naturality_right_symm, hu]

def actualClosedImmersionFactorIdealRestriction
    {Y X Z : Scheme.{u}} (i : X ⟶ Y) (q : Z ⟶ X)
    [IsClosedImmersion q] [IsClosedImmersion (q ≫ i)] :
    (Scheme.Modules.pullback i).obj (closedImmersionModule (q ≫ i)) ⟶
      closedImmersionModule q := by
  let P := Scheme.Modules.pullback i
  letI : P.Additive := inferInstance
  let a := P.map (closedImmersionModuleToUnit (q ≫ i)) ≫ pullbackUnitComparison i
  have hz : a ≫ closedImmersionUnitToPushforwardUnit q = 0 := by
    have h0 : closedImmersionModuleToUnit (q ≫ i) ≫
        closedImmersionUnitToPushforwardUnit (q ≫ i) = 0 := by
      have hkernel : closedImmersionKernelModuleToUnit (q ≫ i) ≫
          closedImmersionUnitToPushforwardUnit (q ≫ i) = 0 := by
        change kernel.ι (closedImmersionUnitToPushforwardUnit (q ≫ i)) ≫
          closedImmersionUnitToPushforwardUnit (q ≫ i) = 0
        exact kernel.condition _
      calc
        _ = (closedImmersionModuleToKernel (q ≫ i) ≫
            closedImmersionKernelModuleToUnit (q ≫ i)) ≫
              closedImmersionUnitToPushforwardUnit (q ≫ i) :=
          congrArg (fun r => r ≫ closedImmersionUnitToPushforwardUnit (q ≫ i))
            (closedImmersionModuleToKernel_comp (q ≫ i)).symm
        _ = closedImmersionModuleToKernel (q ≫ i) ≫
            (closedImmersionKernelModuleToUnit (q ≫ i) ≫
              closedImmersionUnitToPushforwardUnit (q ≫ i)) := Category.assoc _ _ _
        _ = closedImmersionModuleToKernel (q ≫ i) ≫ 0 :=
          congrArg (fun r => closedImmersionModuleToKernel (q ≫ i) ≫ r) hkernel
        _ = 0 := comp_zero
    change P.map (closedImmersionModuleToUnit (q ≫ i)) ≫
      pullbackUnitComparison i ≫ closedImmersionUnitToPushforwardUnit q = 0
    rw [← actualClosedImmersionFactorPushforwardComparison_unit i q,
      ← Category.assoc, ← P.map_comp, h0, Functor.map_zero, zero_comp]
  exact kernel.lift (closedImmersionUnitToPushforwardUnit q) a hz ≫
    (closedImmersionModuleToKernelIso q).inv

lemma actualClosedImmersionFactorIdealRestriction_toUnit
    {Y X Z : Scheme.{u}} (i : X ⟶ Y) (q : Z ⟶ X)
    [IsClosedImmersion q] [IsClosedImmersion (q ≫ i)] :
    actualClosedImmersionFactorIdealRestriction i q ≫ closedImmersionModuleToUnit q =
      (Scheme.Modules.pullback i).map (closedImmersionModuleToUnit (q ≫ i)) ≫
        pullbackUnitComparison i := by
  have he : (closedImmersionModuleToKernelIso q).inv ≫ closedImmersionModuleToUnit q =
      kernel.ι (closedImmersionUnitToPushforwardUnit q) := by
    rw [← closedImmersionModuleToKernel_comp q]
    exact (closedImmersionModuleToKernelIso q).inv_hom_id_assoc _
  unfold actualClosedImmersionFactorIdealRestriction
  rw [Category.assoc, he, kernel.lift_ι]

end PfaffianDescent
