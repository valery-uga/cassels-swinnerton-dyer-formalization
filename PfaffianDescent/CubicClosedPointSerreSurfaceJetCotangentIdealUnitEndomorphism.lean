import PfaffianDescent.SerreExtensionFoundation

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
open IdealSheafDataModule BundleSectionZeroLocus
universe u
attribute [local instance] isIso_pullbackUnitComparison
set_option backward.isDefEq.respectTransparency false

/-- Actual unit endomorphisms descend to every actual closed subscheme. -/
theorem cubicClosedPointSerreSurfaceJetCotangent_unitEndomorphism_closed_quotient
    {X Z : Scheme.{u}} (i : Z ⟶ X)
    (a : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf) :
    a ≫ closedImmersionUnitToPushforwardUnit i =
      closedImmersionUnitToPushforwardUnit i ≫ (Scheme.Modules.pushforward i).map
        (inv (pullbackUnitComparison i) ≫ (Scheme.Modules.pullback i).map a ≫
          pullbackUnitComparison i) := by
  let P := Scheme.Modules.pullback i
  let Q := Scheme.Modules.pushforward i
  let A := Scheme.Modules.pullbackPushforwardAdjunction i
  let O := SheafOfModules.unit X.ringCatSheaf
  let u := pullbackUnitComparison i
  letI : IsIso u := isIso_pullbackUnitComparison i
  have hq : closedImmersionUnitToPushforwardUnit i = A.unit.app O ≫ Q.map u := by
    have h : A.homEquiv _ _ u = closedImmersionUnitToPushforwardUnit i := by
      exact SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _
    simpa only [Adjunction.homEquiv_unit] using h.symm
  have hn := A.unit.naturality a
  simp only [Functor.id_map, Functor.comp_map] at hn
  calc
    a ≫ closedImmersionUnitToPushforwardUnit i = a ≫ A.unit.app O ≫ Q.map u := by rw [hq]
    _ = A.unit.app O ≫ Q.map (P.map a) ≫ Q.map u := by rw [← Category.assoc, hn, Category.assoc]
    _ = A.unit.app O ≫ Q.map (P.map a ≫ u) := by rw [Functor.map_comp]
    _ = A.unit.app O ≫ Q.map (u ≫ inv u ≫ P.map a ≫ u) := by simp
    _ = closedImmersionUnitToPushforwardUnit i ≫ Q.map (inv u ≫ P.map a ≫ u) := by
      rw [hq, Functor.map_comp]
      simp only [Category.assoc]

/-- The SAME actual closed ideal carries the endomorphism induced by any
actual unit-coordinate change. This will correct the discrepancy between
two chart trivializations without imposing a tensor/unitor certificate. -/
def cubicClosedPointSerreSurfaceJetCotangent_idealUnitEndomorphism
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (a : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf) :
    closedImmersionModule i ⟶ closedImmersionModule i :=
  (closedImmersionModuleToKernelIso i).hom ≫
    kernel.map _ _ a ((Scheme.Modules.pushforward i).map
      (inv (pullbackUnitComparison i) ≫ (Scheme.Modules.pullback i).map a ≫
        pullbackUnitComparison i))
      (cubicClosedPointSerreSurfaceJetCotangent_unitEndomorphism_closed_quotient i a).symm ≫
    (closedImmersionModuleToKernelIso i).inv

/-- Literal inclusion square for the corrected actual ideal coordinates. -/
theorem cubicClosedPointSerreSurfaceJetCotangent_idealUnitEndomorphism_toUnit
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (a : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf) :
    cubicClosedPointSerreSurfaceJetCotangent_idealUnitEndomorphism i a ≫
      closedImmersionModuleToUnit i = closedImmersionModuleToUnit i ≫ a := by
  let e := closedImmersionModuleToKernelIso i
  have he : e.inv ≫ closedImmersionModuleToUnit i =
      kernel.ι (closedImmersionUnitToPushforwardUnit i) := by
    rw [← closedImmersionModuleToKernel_comp i]
    exact e.inv_hom_id_assoc _
  unfold cubicClosedPointSerreSurfaceJetCotangent_idealUnitEndomorphism
  rw [Category.assoc, Category.assoc, he, kernel.lift_ι]
  rw [← Category.assoc]
  exact congrArg (fun t => t ≫ a) (closedImmersionModuleToKernel_comp i)

end PfaffianDescent
