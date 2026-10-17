import PfaffianDescent.IdealSheafModule
import PfaffianDescent.BundleSectionZeroLocus
import PfaffianDescent.SchemeModuleTensor
import PfaffianDescent.SchemeModuleGlobalSections

/-! SOURCE ONLY / UNVERIFIED. The actual ambient ideal inclusion induced by
a factorization of closed subschemes. It is constructed from the genuine
quotient of structure sheaves, then tensorized; no polynomial inclusion or
assumed augmentation square is used. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open IdealSheafDataModule BundleSectionZeroLocus
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Actual ambient ideal-sheaf containment, with all nilpotents retained. -/
lemma actualAmbientClosedIdealFactor_ker_le
    {X Z P : Scheme.{u}} (i : Z ⟶ X) (r : P ⟶ Z) (q : P ⟶ X)
    (hfac : r ≫ i = q) : i.ker ≤ q.ker := by
  rw [← hfac]
  exact r.le_ker_comp i

/-- If the smaller subscheme `q` factors through `i`, its ambient ideal
contains the ambient ideal of `i`. This is the unique factor over O_X. -/
def actualAmbientClosedIdealFactorInclusion
    {X Z P : Scheme.{u}} (i : Z ⟶ X) (r : P ⟶ Z) (q : P ⟶ X)
    (hfac : r ≫ i = q) [IsClosedImmersion i] [IsClosedImmersion q] :
    closedImmersionModule i ⟶ closedImmersionModule q := by
  subst q
  let a := closedImmersionModuleToUnit i
  have hz : a ≫ closedImmersionUnitToPushforwardUnit (r ≫ i) = 0 := by
    have h0 : a ≫ closedImmersionUnitToPushforwardUnit i = 0 := by
      dsimp only [a]
      have hkernel : closedImmersionKernelModuleToUnit i ≫
          closedImmersionUnitToPushforwardUnit i = 0 := by
        change kernel.ι (closedImmersionUnitToPushforwardUnit i) ≫
          closedImmersionUnitToPushforwardUnit i = 0
        exact kernel.condition _
      calc
        _ = (closedImmersionModuleToKernel i ≫
            closedImmersionKernelModuleToUnit i) ≫
              closedImmersionUnitToPushforwardUnit i :=
          congrArg (fun m => m ≫ closedImmersionUnitToPushforwardUnit i)
            (closedImmersionModuleToKernel_comp i).symm
        _ = closedImmersionModuleToKernel i ≫
            (closedImmersionKernelModuleToUnit i ≫
              closedImmersionUnitToPushforwardUnit i) := Category.assoc _ _ _
        _ = closedImmersionModuleToKernel i ≫ 0 :=
          congrArg (fun m => closedImmersionModuleToKernel i ≫ m) hkernel
        _ = 0 := comp_zero
    let e := (Scheme.Modules.pushforwardComp r i).app (schemeModuleUnit P)
    have hcomp : closedImmersionUnitToPushforwardUnit (r ≫ i) =
        closedImmersionUnitToPushforwardUnit i ≫
          (Scheme.Modules.pushforward i).map (closedImmersionUnitToPushforwardUnit r) ≫
            e.hom := unitToPushforwardObjUnit_comp r i
    calc
      _ = a ≫ (closedImmersionUnitToPushforwardUnit i ≫
          (Scheme.Modules.pushforward i).map (closedImmersionUnitToPushforwardUnit r) ≫
            e.hom) :=
        congrArg (fun m : schemeModuleUnit X ⟶
          (Scheme.Modules.pushforward (r ≫ i)).obj (schemeModuleUnit P) => a ≫ m) hcomp
      _ = (a ≫ closedImmersionUnitToPushforwardUnit i) ≫
          ((Scheme.Modules.pushforward i).map (closedImmersionUnitToPushforwardUnit r) ≫
            e.hom) := (Category.assoc _ _ _).symm
      _ = 0 ≫ ((Scheme.Modules.pushforward i).map
          (closedImmersionUnitToPushforwardUnit r) ≫ e.hom) :=
        congrArg (fun m : closedImmersionModule i ⟶
          (Scheme.Modules.pushforward i).obj (schemeModuleUnit Z) =>
            m ≫ ((Scheme.Modules.pushforward i).map
              (closedImmersionUnitToPushforwardUnit r) ≫ e.hom)) h0
      _ = 0 := zero_comp
  exact kernel.lift (closedImmersionUnitToPushforwardUnit (r ≫ i)) a hz ≫
    (closedImmersionModuleToKernelIso (r ≫ i)).inv

lemma actualAmbientClosedIdealFactorInclusion_toUnit
    {X Z P : Scheme.{u}} (i : Z ⟶ X) (r : P ⟶ Z) (q : P ⟶ X)
    (hfac : r ≫ i = q) [IsClosedImmersion i] [IsClosedImmersion q] :
    actualAmbientClosedIdealFactorInclusion i r q hfac ≫
      closedImmersionModuleToUnit q = closedImmersionModuleToUnit i := by
  subst q
  have he : (closedImmersionModuleToKernelIso (r ≫ i)).inv ≫
      closedImmersionModuleToUnit (r ≫ i) =
      kernel.ι (closedImmersionUnitToPushforwardUnit (r ≫ i)) := by
    rw [← closedImmersionModuleToKernel_comp (r ≫ i)]
    exact (closedImmersionModuleToKernelIso (r ≫ i)).inv_hom_id_assoc _
  unfold actualAmbientClosedIdealFactorInclusion
  rw [Category.assoc, he, kernel.lift_ι]

/-- This is the canonical ambient ideal inclusion: every sheaf map over
the same structure sheaf equals the constructed one. -/
lemma actualAmbientClosedIdealFactorInclusion_unique
    {X Z P : Scheme.{u}} (i : Z ⟶ X) (r : P ⟶ Z) (q : P ⟶ X)
    (hfac : r ≫ i = q) [IsClosedImmersion i] [IsClosedImmersion q]
    (v : closedImmersionModule i ⟶ closedImmersionModule q)
    (hv : v ≫ closedImmersionModuleToUnit q = closedImmersionModuleToUnit i) :
    v = actualAmbientClosedIdealFactorInclusion i r q hfac := by
  letI : Mono (closedImmersionModuleToUnit q) := by
    change Mono (idealModuleToUnit q.ker)
    infer_instance
  apply (cancel_mono (closedImmersionModuleToUnit q)).mp
  exact hv.trans (actualAmbientClosedIdealFactorInclusion_toUnit i r q hfac).symm

/-- The actual augmentation I_i tensor T -> T. -/
def actualAmbientClosedIdealTwistAugmentation
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (T : X.Modules) :
    closedImmersionIdealTwist i T ⟶ T :=
  schemeModuleTensorMap (closedImmersionModuleToUnit i) (𝟙 T) ≫
    (schemeModuleTensorUnitLeftIso T).hom

def actualAmbientClosedIdealTwistFactorInclusion
    {X Z P : Scheme.{u}} (i : Z ⟶ X) (r : P ⟶ Z) (q : P ⟶ X)
    (hfac : r ≫ i = q) [IsClosedImmersion i] [IsClosedImmersion q]
    (T : X.Modules) : closedImmersionIdealTwist i T ⟶ closedImmersionIdealTwist q T :=
  schemeModuleTensorMap (actualAmbientClosedIdealFactorInclusion i r q hfac) (𝟙 T)

lemma actualAmbientClosedIdealTwistFactorInclusion_augmentation
    {X Z P : Scheme.{u}} (i : Z ⟶ X) (r : P ⟶ Z) (q : P ⟶ X)
    (hfac : r ≫ i = q) [IsClosedImmersion i] [IsClosedImmersion q]
    (T : X.Modules) :
    actualAmbientClosedIdealTwistFactorInclusion i r q hfac T ≫
      actualAmbientClosedIdealTwistAugmentation q T =
      actualAmbientClosedIdealTwistAugmentation i T := by
  unfold actualAmbientClosedIdealTwistFactorInclusion
    actualAmbientClosedIdealTwistAugmentation
  rw [← Category.assoc, schemeModuleTensorMap_comp,
    actualAmbientClosedIdealFactorInclusion_toUnit, Category.comp_id]

/-- Genuine induced H0 map, by postcomposition with the actual sheaf map. -/
def actualAmbientClosedIdealTwistHZeroFactorInclusion
    {K : Type u} [Field K] {X Z P : Scheme.{u}}
    (base : X ⟶ Spec (.of K))
    (i : Z ⟶ X) (r : P ⟶ Z) (q : P ⟶ X) (hfac : r ≫ i = q)
    [IsClosedImmersion i] [IsClosedImmersion q] (T : X.Modules) :
    SchemeModuleGlobalSectionsOver base (closedImmersionIdealTwist i T) →ₗ[K]
      SchemeModuleGlobalSectionsOver base (closedImmersionIdealTwist q T) :=
  schemeModuleGlobalSectionsMap base
    (actualAmbientClosedIdealTwistFactorInclusion i r q hfac T)

end PfaffianDescent
