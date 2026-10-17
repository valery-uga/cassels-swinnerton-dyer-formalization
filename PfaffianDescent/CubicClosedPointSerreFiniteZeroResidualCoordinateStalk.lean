import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualFreeStalk

/-! # Section coordinates are the actual coordinates of its stalk germ -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace PfaffianDescent
open BundleSectionZeroLocus
universe u
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreFiniteZeroResidual_freeCoordinate_eq_app
    {X : Scheme.{u}} (I : Type u)
    (s : (SheafOfModules.free (R := X.ringCatSheaf) I).sections) (i : I) :
    freeSectionCoordinate (X := X) I s i =
      (freeCoordinateMap (X := X) I i).val.app (Opposite.op ⊤)
        (s.val (Opposite.op ⊤)) := by
  unfold freeSectionCoordinate unitSectionAtTop
  rw [SheafOfModules.unitHomEquiv_comp_apply, Equiv.apply_symm_apply]
  rfl

theorem cubicClosedPointSerreFiniteZeroResidual_coordinate_eq_app
    {X : Scheme.{u}} {E : X.Modules} (I : Type u)
    (a : SheafOfModules.free (R := X.ringCatSheaf) I ≅ E)
    (s : E.sections) (i : I) :
    sectionCoordinateOfFreeIso I a s i =
      (a.inv ≫ freeCoordinateMap (X := X) I i).val.app (Opposite.op ⊤)
        (s.val (Opposite.op ⊤)) := by
  unfold sectionCoordinateOfFreeIso
  rw [cubicClosedPointSerreFiniteZeroResidual_freeCoordinate_eq_app]
  rfl

def cubicClosedPointSerreFiniteZeroResidual_stalkPairOfFreeIso
    {X : Scheme.{u}} {E : X.Modules}
    (a : SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin 2)) ≅ E)
    (x : X) :
    letI : Module (X.presheaf.stalk x) (E.presheaf.stalk x) :=
      schemeModuleStalkModule E x
    E.presheaf.stalk x ≃ₗ[X.presheaf.stalk x]
      ((X.presheaf.stalk x) × (X.presheaf.stalk x)) :=
  ((schemeModuleStalkModuleFunctor X x).mapIso a.symm ≪≫
    cubicClosedPointSerreFiniteZeroResidual_freeStalkPairIso X x).toLinearEquiv

theorem cubicClosedPointSerreFiniteZeroResidual_stalkPairOfFreeIso_fst_germ
    {X : Scheme.{u}} {E : X.Modules}
    (a : SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin 2)) ≅ E)
    (s : E.sections) (x : X) :
    letI : Module (X.presheaf.stalk x) (E.presheaf.stalk x) :=
      schemeModuleStalkModule E x
    (cubicClosedPointSerreFiniteZeroResidual_stalkPairOfFreeIso a x
      (E.presheaf.germ ⊤ x trivial (s.val (Opposite.op ⊤)))).1 =
      X.presheaf.germ ⊤ x trivial
        (sectionCoordinateOfFreeIso (ULift.{u} (Fin 2)) a s (ULift.up 0)) := by
  dsimp only
  letI : Module (X.presheaf.stalk x) (E.presheaf.stalk x) :=
    schemeModuleStalkModule E x
  let F := schemeModuleStalkModuleFunctor X x
  let m := E.presheaf.germ ⊤ x trivial (s.val (Opposite.op ⊤))
  have h := congrArg (fun f => f.hom (F.map a.inv m))
    (cubicClosedPointSerreFiniteZeroResidual_freeStalkPairIso_fst X x)
  have hc :
      (cubicClosedPointSerreFiniteZeroResidual_stalkPairOfFreeIso a x m).1 =
        schemeModuleStalkToRingLinearMap
          (a.inv ≫ freeCoordinateMap (X := X) (ULift.{u} (Fin 2)) (ULift.up 0)) x m := by
    change ((cubicClosedPointSerreFiniteZeroResidual_freeStalkPairIso X x).hom
      (F.map a.inv m)).1 = (schemeModuleUnitStalkIso X x).hom
        (F.map (a.inv ≫ freeCoordinateMap (X := X)
          (ULift.{u} (Fin 2)) (ULift.up 0)) m)
    rw [F.map_comp]
    exact h
  rw [hc, schemeModuleStalkToRingLinearMap_germ]
  rw [cubicClosedPointSerreFiniteZeroResidual_coordinate_eq_app]

theorem cubicClosedPointSerreFiniteZeroResidual_stalkPairOfFreeIso_snd_germ
    {X : Scheme.{u}} {E : X.Modules}
    (a : SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin 2)) ≅ E)
    (s : E.sections) (x : X) :
    letI : Module (X.presheaf.stalk x) (E.presheaf.stalk x) :=
      schemeModuleStalkModule E x
    (cubicClosedPointSerreFiniteZeroResidual_stalkPairOfFreeIso a x
      (E.presheaf.germ ⊤ x trivial (s.val (Opposite.op ⊤)))).2 =
      X.presheaf.germ ⊤ x trivial
        (sectionCoordinateOfFreeIso (ULift.{u} (Fin 2)) a s (ULift.up 1)) := by
  dsimp only
  letI : Module (X.presheaf.stalk x) (E.presheaf.stalk x) :=
    schemeModuleStalkModule E x
  let F := schemeModuleStalkModuleFunctor X x
  let m := E.presheaf.germ ⊤ x trivial (s.val (Opposite.op ⊤))
  have h := congrArg (fun f => f.hom (F.map a.inv m))
    (cubicClosedPointSerreFiniteZeroResidual_freeStalkPairIso_snd X x)
  have hc :
      (cubicClosedPointSerreFiniteZeroResidual_stalkPairOfFreeIso a x m).2 =
        schemeModuleStalkToRingLinearMap
          (a.inv ≫ freeCoordinateMap (X := X) (ULift.{u} (Fin 2)) (ULift.up 1)) x m := by
    change ((cubicClosedPointSerreFiniteZeroResidual_freeStalkPairIso X x).hom
      (F.map a.inv m)).2 = (schemeModuleUnitStalkIso X x).hom
        (F.map (a.inv ≫ freeCoordinateMap (X := X)
          (ULift.{u} (Fin 2)) (ULift.up 1)) m)
    rw [F.map_comp]
    exact h
  rw [hc, schemeModuleStalkToRingLinearMap_germ]
  rw [cubicClosedPointSerreFiniteZeroResidual_coordinate_eq_app]

end PfaffianDescent
