import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualCanonicalRestriction
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualOverSpan
import PfaffianDescent.CubicClosedPointSerreZeroIdealStalkAwayNative

/-! # Actual affine coordinates of the original canonical Serre section -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent.ProjectiveNegativeTwist
open BundleSectionZeroLocus AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreFiniteZeroResidual_canonical_chart_span_at_point
    (K : Type u) [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] {L : Type u} [Field L]
    (i : Spec (.of L) ⟶ hypersurface p hp) [IsClosedImmersion i]
    [hExt : HasExt.{u} (hypersurface p hp).Modules]
    [hExtStalk : HasExt.{u + 1}
      (ModuleCat.{u} ((hypersurface p hp).presheaf.stalk (i default)))]
    (e : SerreExtensionData (hypersurface p hp)
      (closedImmersionIdealTwist i
        (positiveSheafOfModules (grading (equationIdeal p hp)) 3)))
    (hne :
      letI := quotientPositiveTwist_tensorRight_preservesFiniteLimits (equationIdeal p hp) 3
      letI := quotientPositiveTwist_tensorRight_preservesFiniteColimits (equationIdeal p hp) 3
      (closedImmersionIdealTwistSequence_shortExact i
        (positiveSheafOfModules (grading (equationIdeal p hp)) 3)).extClass.comp
        (@SerreExtensionSequenceData.extensionClass.{u} (hypersurface p hp) _ e.toSequenceData hExt)
        (show 1 + 1 = 2 by omega) ≠ 0)
    (U : (hypersurface p hp).Opens) (hx : i default ∈ U)
    (t : SheafOfModules.free (R := (hypersurface p hp).ringCatSheaf.over U)
      (ULift.{u} (Fin 2)) ≅ e.E.over U) :
    let x : U := ⟨i default, hx⟩
    Ideal.span ({
      (U : Scheme).presheaf.germ ⊤ x trivial
        (sectionCoordinateOfFreeIso (ULift.{u} (Fin 2))
          (localFreeIsoOfOver U (ULift.{u} (Fin 2)) t)
          (restrictSectionToOpen U e.canonicalSection) (ULift.up 0)),
      (U : Scheme).presheaf.germ ⊤ x trivial
        (sectionCoordinateOfFreeIso (ULift.{u} (Fin 2))
          (localFreeIsoOfOver U (ULift.{u} (Fin 2)) t)
          (restrictSectionToOpen U e.canonicalSection) (ULift.up 1))} :
      Set ((U : Scheme).presheaf.stalk x)) =
        IsLocalRing.maximalIdeal ((U : Scheme).presheaf.stalk x) := by
  dsimp only
  let x : U := ⟨i default, hx⟩
  let N : (hypersurface p hp).Modules := e.E
  letI := schemeModuleStalkModule N (i default)
  letI := schemeModuleStalkModule (N.restrict U.ι) x
  let a := cubicClosedPointSerreFiniteZeroResidual_overStalkPair U x N t
  have hcanon := cubicClosedPointSerreFiniteZeroResidual_canonical_stalk_eq_germ
    e U (i default) hx
  have hg := cubicClosedPointSerreFiniteZeroResidual_overStalkPair_germ
    U x N t e.canonicalSection
  have hc := congrArg (fun m => a ((Scheme.Modules.restrictStalkNatIso U.ι x).inv.app N m)) hcanon
  have hs := congrArg (fun z => Ideal.span ({z.1, z.2} :
    Set ((U : Scheme).presheaf.stalk x))) (hc.trans hg)
  have hn := cubicClosedPointSerreFiniteZeroResidual_canonical_restricted_stalk_span
    K p hp hp0 i e.toSequenceData hne U hx a
  exact hs.symm.trans hn

theorem cubicClosedPointSerreFiniteZeroResidual_canonical_chart_span_off_point
    (K : Type u) [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    {L : Type u} [Field L]
    (i : Spec (.of L) ⟶ hypersurface p hp) [IsClosedImmersion i]
    (e : SerreExtensionData (hypersurface p hp)
      (closedImmersionIdealTwist i
        (positiveSheafOfModules (grading (equationIdeal p hp)) 3)))
    (U : (hypersurface p hp).Opens) (x : U) (hx : U.ι x ≠ i default)
    (t : SheafOfModules.free (R := (hypersurface p hp).ringCatSheaf.over U)
      (ULift.{u} (Fin 2)) ≅ e.E.over U) :
    Ideal.span ({
      (U : Scheme).presheaf.germ ⊤ x trivial
        (sectionCoordinateOfFreeIso (ULift.{u} (Fin 2))
          (localFreeIsoOfOver U (ULift.{u} (Fin 2)) t)
          (restrictSectionToOpen U e.canonicalSection) (ULift.up 0)),
      (U : Scheme).presheaf.germ ⊤ x trivial
        (sectionCoordinateOfFreeIso (ULift.{u} (Fin 2))
          (localFreeIsoOfOver U (ULift.{u} (Fin 2)) t)
          (restrictSectionToOpen U e.canonicalSection) (ULift.up 1))} :
      Set ((U : Scheme).presheaf.stalk x)) = ⊤ := by
  let N : (hypersurface p hp).Modules := e.E
  letI := schemeModuleStalkModule N (U.ι x)
  letI := schemeModuleStalkModule (N.restrict U.ι) x
  let a := cubicClosedPointSerreFiniteZeroResidual_restrictionBasis U x N
    (cubicClosedPointSerreFiniteZeroResidual_overStalkPair U x N t)
  have hcanon := cubicClosedPointSerreFiniteZeroResidual_canonical_stalk_eq_germ
    e U (U.ι x) x.2
  have hc := congrArg (fun m => Ideal.span ({(a m).1, (a m).2} :
    Set ((hypersurface p hp).presheaf.stalk (U.ι x)))) hcanon
  have hn := cubicClosedPointSerreZeroIdealStalkAwayNative_span_eq_top
    K p hp i e.toSequenceData (U.ι x) hx a
  have ht := congrArg (Ideal.map (U.ι.stalkMap x).hom) (hc.symm.trans hn)
  have hg := cubicClosedPointSerreFiniteZeroResidual_over_stalk_span
    U x N t e.canonicalSection
  simpa only [Ideal.map_top] using hg.symm.trans ht

end PfaffianDescent.ProjectiveNegativeTwist
