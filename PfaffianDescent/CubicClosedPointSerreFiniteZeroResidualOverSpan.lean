import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualOverStalk
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualBasisRestriction

/-! # The coordinate zero ideal under the actual original-to-open stalk map -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
open BundleSectionZeroLocus
universe u
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreFiniteZeroResidual_over_stalk_span
    {X : Scheme.{u}} (U : X.Opens) (x : U) (E : X.Modules)
    (t : SheafOfModules.free (R := X.ringCatSheaf.over U) (ULift.{u} (Fin 2)) ≅ E.over U)
    (s : E.sections) :
    letI : Module (X.presheaf.stalk (U.ι x)) (E.presheaf.stalk (U.ι x)) :=
      schemeModuleStalkModule E (U.ι x)
    letI : Module ((U : Scheme).presheaf.stalk x) ((E.restrict U.ι).presheaf.stalk x) :=
      schemeModuleStalkModule (E.restrict U.ι) x
    let a := cubicClosedPointSerreFiniteZeroResidual_restrictionBasis U x E
      (cubicClosedPointSerreFiniteZeroResidual_overStalkPair U x E t)
    let m := E.presheaf.germ U (U.ι x) x.2 (s.val (Opposite.op U))
    Ideal.map (U.ι.stalkMap x).hom
        (Ideal.span ({(a m).1, (a m).2} : Set (X.presheaf.stalk (U.ι x)))) =
      Ideal.span ({
        (U : Scheme).presheaf.germ ⊤ x trivial
          (sectionCoordinateOfFreeIso (ULift.{u} (Fin 2))
            (localFreeIsoOfOver U (ULift.{u} (Fin 2)) t)
            (restrictSectionToOpen U s) (ULift.up 0)),
        (U : Scheme).presheaf.germ ⊤ x trivial
          (sectionCoordinateOfFreeIso (ULift.{u} (Fin 2))
            (localFreeIsoOfOver U (ULift.{u} (Fin 2)) t)
            (restrictSectionToOpen U s) (ULift.up 1))} :
        Set ((U : Scheme).presheaf.stalk x)) := by
  dsimp only
  letI := schemeModuleStalkModule E (U.ι x)
  letI := schemeModuleStalkModule (E.restrict U.ι) x
  have h := cubicClosedPointSerreFiniteZeroResidual_restrictionBasis_span U x E
    (cubicClosedPointSerreFiniteZeroResidual_overStalkPair U x E t)
    (E.presheaf.germ U (U.ι x) x.2 (s.val (Opposite.op U)))
  have hg := cubicClosedPointSerreFiniteZeroResidual_overStalkPair_germ U x E t s
  exact h.trans (congrArg (fun z => Ideal.span ({z.1, z.2} :
    Set ((U : Scheme).presheaf.stalk x))) hg)

end PfaffianDescent
