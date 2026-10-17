import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualOverSection
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualSectionGerm

/-! # Actual affine bundle coordinates and original surface stalk sections -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
open BundleSectionZeroLocus
universe u
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreFiniteZeroResidual_over_section_stalk
    {X : Scheme.{u}} (U : X.Opens) (x : U) (E : X.Modules) (s : E.sections) :
    (schemeModuleStalkModuleFunctor (U : Scheme) x).map
        ((Scheme.Modules.overFunctorEquiv U).app E).hom
        (((Scheme.Modules.overEquiv U).functor.obj (E.over U)).presheaf.germ
          ⊤ x trivial ((restrictSectionToOpen U s).val (Opposite.op ⊤))) =
      (Scheme.Modules.restrictStalkNatIso U.ι x).inv.app E
        (E.presheaf.germ U (U.ι x) x.2 (s.val (Opposite.op U))) := by
  have h := TopCat.Presheaf.stalkFunctor_map_germ_apply
    (X := (U : Scheme).toTopCat) (C := AddCommGrpCat.{u})
    ⊤ x trivial ((Scheme.Modules.toPresheaf (U : Scheme)).map
      ((Scheme.Modules.overFunctorEquiv U).app E).hom)
      ((restrictSectionToOpen U s).val (Opposite.op ⊤))
  change (schemeModuleStalkModuleFunctor (U : Scheme) x).map
      ((Scheme.Modules.overFunctorEquiv U).app E).hom
      (((Scheme.Modules.overEquiv U).functor.obj (E.over U)).presheaf.germ
        ⊤ x trivial ((restrictSectionToOpen U s).val (Opposite.op ⊤))) =
    (E.restrict U.ι).presheaf.germ ⊤ x trivial
      ((((Scheme.Modules.overFunctorEquiv U).app E).hom).val.app (Opposite.op ⊤)
        ((restrictSectionToOpen U s).val (Opposite.op ⊤))) at h
  rw [cubicClosedPointSerreFiniteZeroResidual_over_section_top] at h
  have hg := schemeModuleRestrictTopSectionIso_germ U x E (s.val (Opposite.op U))
  apply (ConcreteCategory.bijective_of_isIso
    ((Scheme.Modules.restrictStalkNatIso U.ι x).app E).hom).injective
  exact ((congrArg ((Scheme.Modules.restrictStalkNatIso U.ι x).hom.app E) h).trans hg).trans
    (Iso.inv_hom_id_apply ((Scheme.Modules.restrictStalkNatIso U.ι x).app E)
      (E.presheaf.germ U (U.ι x) x.2 (s.val (Opposite.op U)))).symm

def cubicClosedPointSerreFiniteZeroResidual_overStalkPair
    {X : Scheme.{u}} (U : X.Opens) (x : U) (E : X.Modules)
    (t : SheafOfModules.free (R := X.ringCatSheaf.over U) (ULift.{u} (Fin 2)) ≅ E.over U) :
    letI : Module ((U : Scheme).presheaf.stalk x) ((E.restrict U.ι).presheaf.stalk x) :=
      schemeModuleStalkModule (E.restrict U.ι) x
    (E.restrict U.ι).presheaf.stalk x ≃ₗ[(U : Scheme).presheaf.stalk x]
      (((U : Scheme).presheaf.stalk x) × ((U : Scheme).presheaf.stalk x)) := by
  letI := schemeModuleStalkModule (E.restrict U.ι) x
  let N := (Scheme.Modules.overEquiv U).functor.obj (E.over U)
  letI := schemeModuleStalkModule N x
  exact ((schemeModuleStalkModuleFunctor (U : Scheme) x).mapIso
    ((Scheme.Modules.overFunctorEquiv U).app E).symm).toLinearEquiv.trans
      (cubicClosedPointSerreFiniteZeroResidual_stalkPairOfFreeIso
        (localFreeIsoOfOver U (ULift.{u} (Fin 2)) t) x)

theorem cubicClosedPointSerreFiniteZeroResidual_overStalkPair_germ
    {X : Scheme.{u}} (U : X.Opens) (x : U) (E : X.Modules)
    (t : SheafOfModules.free (R := X.ringCatSheaf.over U) (ULift.{u} (Fin 2)) ≅ E.over U)
    (s : E.sections) :
    letI : Module ((U : Scheme).presheaf.stalk x) ((E.restrict U.ι).presheaf.stalk x) :=
      schemeModuleStalkModule (E.restrict U.ι) x
    cubicClosedPointSerreFiniteZeroResidual_overStalkPair U x E t
      ((Scheme.Modules.restrictStalkNatIso U.ι x).inv.app E
        (E.presheaf.germ U (U.ι x) x.2 (s.val (Opposite.op U)))) =
      ((U : Scheme).presheaf.germ ⊤ x trivial
          (sectionCoordinateOfFreeIso (ULift.{u} (Fin 2))
            (localFreeIsoOfOver U (ULift.{u} (Fin 2)) t)
            (restrictSectionToOpen U s) (ULift.up 0)),
        (U : Scheme).presheaf.germ ⊤ x trivial
          (sectionCoordinateOfFreeIso (ULift.{u} (Fin 2))
            (localFreeIsoOfOver U (ULift.{u} (Fin 2)) t)
            (restrictSectionToOpen U s) (ULift.up 1))) := by
  dsimp only
  letI := schemeModuleStalkModule (E.restrict U.ι) x
  let F := schemeModuleStalkModuleFunctor (U : Scheme) x
  let a := (Scheme.Modules.overFunctorEquiv U).app E
  let N := (Scheme.Modules.overEquiv U).functor.obj (E.over U)
  let m := N.presheaf.germ ⊤ x trivial
    ((restrictSectionToOpen U s).val (Opposite.op ⊤))
  have hm : F.map a.inv
      ((Scheme.Modules.restrictStalkNatIso U.ι x).inv.app E
        (E.presheaf.germ U (U.ι x) x.2 (s.val (Opposite.op U)))) = m := by
    rw [← cubicClosedPointSerreFiniteZeroResidual_over_section_stalk]
    exact Iso.hom_inv_id_apply (F.mapIso a) m
  change cubicClosedPointSerreFiniteZeroResidual_stalkPairOfFreeIso
    (localFreeIsoOfOver U (ULift.{u} (Fin 2)) t) x (F.map a.inv _) = _
  rw [hm]
  exact Prod.ext
    (cubicClosedPointSerreFiniteZeroResidual_stalkPairOfFreeIso_fst_germ
      (localFreeIsoOfOver U (ULift.{u} (Fin 2)) t) (restrictSectionToOpen U s) x)
    (cubicClosedPointSerreFiniteZeroResidual_stalkPairOfFreeIso_snd_germ
      (localFreeIsoOfOver U (ULift.{u} (Fin 2)) t) (restrictSectionToOpen U s) x)

end PfaffianDescent
