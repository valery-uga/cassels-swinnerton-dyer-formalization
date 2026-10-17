import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentIdealUnitAutomorphism
import PfaffianDescent.FiniteProjectiveTwistTriviality

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
open IdealSheafDataModule BundleSectionZeroLocus
universe u
set_option backward.isDefEq.respectTransparency false

/-- The actual open-chart support isomorphism carries the actual ambient
quotient map to the literal closed-chart quotient, through the native unit iso. -/
theorem cubicClosedPointSerreSurfaceJetCotangent_closedQuotient_openRestriction
    {X U Z : Scheme.{u}} (f : U ⟶ X) [IsOpenImmersion f] (j : Z ⟶ U) :
    (Scheme.Modules.restrictFunctor f).map (closedImmersionUnitToPushforwardUnit (j ≫ f)) ≫
      (restrictPushforwardUnitFactorThroughOpenIso j f).hom =
    (Scheme.Modules.restrictUnitIso f).hom ≫ closedImmersionUnitToPushforwardUnit j := by
  let R := Scheme.Modules.restrictFunctor f
  let Q := Scheme.Modules.pushforward f
  let A := Scheme.Modules.restrictAdjunction f
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let u := (Scheme.Modules.restrictUnitIso f).hom
  let q := closedImmersionUnitToPushforwardUnit j
  let e := (Scheme.Modules.pushforwardComp j f).app (SheafOfModules.unit Z.ringCatSheaf)
  have hcomp : closedImmersionUnitToPushforwardUnit (j ≫ f) =
      closedImmersionUnitToPushforwardUnit f ≫ Q.map q ≫ e.hom :=
    unitToPushforwardObjUnit_comp j f
  have hf : closedImmersionUnitToPushforwardUnit f = A.unit.app O ≫ Q.map u :=
    unitToPushforwardObjUnit_eq_restrictAdjunction f
  have hnq := A.counit.naturality q
  have hnu := A.counit.naturality u
  simp only [Functor.comp_map, Functor.id_map] at hnq hnu
  have ht : R.map (A.unit.app O) ≫ A.counit.app (R.obj O) = 𝟙 (R.obj O) :=
    A.left_triangle_components O
  change R.map (closedImmersionUnitToPushforwardUnit (j ≫ f)) ≫
    R.map e.inv ≫ A.counit.app _ = u ≫ q
  calc
    R.map (closedImmersionUnitToPushforwardUnit (j ≫ f)) ≫
        R.map e.inv ≫ A.counit.app _ =
      R.map (closedImmersionUnitToPushforwardUnit (j ≫ f) ≫ e.inv) ≫
        A.counit.app _ := by rw [R.map_comp, Category.assoc]
    _ = R.map (closedImmersionUnitToPushforwardUnit f ≫ Q.map q) ≫
        A.counit.app _ := by rw [hcomp]; simp
    _ = R.map (closedImmersionUnitToPushforwardUnit f) ≫
        A.counit.app _ ≫ q := by rw [R.map_comp, Category.assoc, hnq]
    _ = R.map (A.unit.app O) ≫ R.map (Q.map u) ≫ A.counit.app _ ≫ q := by
      rw [hf, R.map_comp, Category.assoc]
    _ = R.map (A.unit.app O) ≫ A.counit.app (R.obj O) ≫ u ≫ q := by
      rw [← Category.assoc (R.map (Q.map u)), hnu, Category.assoc]
    _ = u ≫ q := by rw [← Category.assoc, ht]; simp

/-- Actual ideal restriction to an open containing its whole support equals
the ideal of the literal factor, with no affine kernel equality casts. -/
def cubicClosedPointSerreSurfaceJetCotangent_idealOpenRestrictionIso
    {X U Z : Scheme.{u}} (f : U ⟶ X) [IsOpenImmersion f] (j : Z ⟶ U)
    [IsClosedImmersion j] [IsClosedImmersion (j ≫ f)] :
    (Scheme.Modules.restrictFunctor f).obj (closedImmersionModule (j ≫ f)) ≅
      closedImmersionModule j := by
  let R := Scheme.Modules.restrictFunctor f
  letI : PreservesFiniteLimits R := restrictFunctor_preservesFiniteLimits f
  exact R.mapIso (closedImmersionModuleToKernelIso (j ≫ f)) ≪≫
    PreservesKernel.iso R (closedImmersionUnitToPushforwardUnit (j ≫ f)) ≪≫
    kernel.mapIso _ _ (Scheme.Modules.restrictUnitIso f)
      (restrictPushforwardUnitFactorThroughOpenIso j f)
      (cubicClosedPointSerreSurfaceJetCotangent_closedQuotient_openRestriction f j) ≪≫
    (closedImmersionModuleToKernelIso j).symm

end PfaffianDescent
