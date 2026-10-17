import PfaffianDescent.CubicClosedPointSerreFreeNeighborhoodBiprod
import PfaffianDescent.VoisinSheafStalk
import Mathlib.Algebra.Category.ModuleCat.Biproducts

/-! # Actual scalar coordinates on a rank-two free stalk

The pair coordinate isomorphism is obtained by applying the actual stalk
functor to the actual two-unit biproduct isomorphism. Its projections are
the stalks of the scalar coordinate maps used by the section zero ideal.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
open BundleSectionZeroLocus
universe u
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreFiniteZeroResidual_unitBiprod_hom
    (X : Scheme.{u}) :
    (cubicClosedPointSerreFreeNeighborhoodUnitBiprodIso X).hom =
      biprod.lift (freeCoordinateMap (X := X) (ULift.{u} (Fin 2)) (ULift.up 0))
        (freeCoordinateMap (X := X) (ULift.{u} (Fin 2)) (ULift.up 1)) := by
  apply Cofan.IsColimit.hom_ext
    (SheafOfModules.isColimitFreeCofan (ULift.{u} (Fin 2)))
  intro i
  obtain ⟨i⟩ := i
  change SheafOfModules.ιFree (ULift.up i) ≫ _ =
    SheafOfModules.ιFree (ULift.up i) ≫ _
  fin_cases i <;> apply biprod.hom_ext
  all_goals
    simp only [Category.assoc, biprod.lift_fst, biprod.lift_snd,
      iota_comp_freeCoordinateMap]
    simp [cubicClosedPointSerreFreeNeighborhoodUnitBiprodIso,
      SheafOfModules.ιFree]

def cubicClosedPointSerreFiniteZeroResidual_freeStalkPairIso
    (X : Scheme.{u}) (x : X) :
    (schemeModuleStalkModuleFunctor X x).obj
        (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin 2))) ≅
      ModuleCat.of (X.presheaf.stalk x)
        ((X.presheaf.stalk x) × (X.presheaf.stalk x)) := by
  let F := schemeModuleStalkModuleFunctor X x
  letI : F.Additive := inferInstanceAs (schemeModuleStalkModuleFunctor X x).Additive
  letI : PreservesFiniteLimits F :=
    inferInstanceAs (PreservesFiniteLimits (schemeModuleStalkModuleFunctor X x))
  letI : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBinaryProducts F
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let R := ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x)
  exact F.mapIso (cubicClosedPointSerreFreeNeighborhoodUnitBiprodIso X) ≪≫
    F.mapBiprod O O ≪≫ biprod.mapIso (schemeModuleUnitStalkIso X x)
      (schemeModuleUnitStalkIso X x) ≪≫ ModuleCat.biprodIsoProd R R

@[reassoc]
theorem cubicClosedPointSerreFiniteZeroResidual_freeStalkPairIso_fst
    (X : Scheme.{u}) (x : X) :
    (cubicClosedPointSerreFiniteZeroResidual_freeStalkPairIso X x).hom ≫
      ModuleCat.ofHom (LinearMap.fst (X.presheaf.stalk x)
        (X.presheaf.stalk x) (X.presheaf.stalk x)) =
    (schemeModuleStalkModuleFunctor X x).map
        (freeCoordinateMap (X := X) (ULift.{u} (Fin 2)) (ULift.up 0)) ≫
      (schemeModuleUnitStalkIso X x).hom := by
  let R := ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x)
  have hp : (ModuleCat.biprodIsoProd R R).hom ≫
      ModuleCat.ofHom (LinearMap.fst (X.presheaf.stalk x) R R) = biprod.fst := by
    rw [← ModuleCat.biprodIsoProd_inv_comp_fst, Iso.hom_inv_id_assoc]
  dsimp only [R] at hp
  unfold cubicClosedPointSerreFiniteZeroResidual_freeStalkPairIso
  simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc, hp, biprod.mapIso_hom, biprod.map_fst,
    Functor.mapBiprod_hom, biprod.lift_fst_assoc, ← Functor.map_comp]
  rw [cubicClosedPointSerreFiniteZeroResidual_unitBiprod_hom]
  rw [← Category.assoc, ← Functor.map_comp, biprod.lift_fst]

@[reassoc]
theorem cubicClosedPointSerreFiniteZeroResidual_freeStalkPairIso_snd
    (X : Scheme.{u}) (x : X) :
    (cubicClosedPointSerreFiniteZeroResidual_freeStalkPairIso X x).hom ≫
      ModuleCat.ofHom (LinearMap.snd (X.presheaf.stalk x)
        (X.presheaf.stalk x) (X.presheaf.stalk x)) =
    (schemeModuleStalkModuleFunctor X x).map
        (freeCoordinateMap (X := X) (ULift.{u} (Fin 2)) (ULift.up 1)) ≫
      (schemeModuleUnitStalkIso X x).hom := by
  let R := ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x)
  have hp : (ModuleCat.biprodIsoProd R R).hom ≫
      ModuleCat.ofHom (LinearMap.snd (X.presheaf.stalk x) R R) = biprod.snd := by
    rw [← ModuleCat.biprodIsoProd_inv_comp_snd, Iso.hom_inv_id_assoc]
  dsimp only [R] at hp
  unfold cubicClosedPointSerreFiniteZeroResidual_freeStalkPairIso
  simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc, hp, biprod.mapIso_hom, biprod.map_snd,
    Functor.mapBiprod_hom, biprod.lift_snd_assoc, ← Functor.map_comp]
  rw [cubicClosedPointSerreFiniteZeroResidual_unitBiprod_hom]
  rw [← Category.assoc, ← Functor.map_comp, biprod.lift_snd]

end PfaffianDescent
