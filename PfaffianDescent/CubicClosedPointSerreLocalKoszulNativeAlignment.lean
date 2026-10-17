import PfaffianDescent.CubicClosedPointSerreLocalKoszulStalkAlignment
import PfaffianDescent.CubicClosedPointSerreLocalFree

/-! # Native affine Koszul charts with an actual Serre-extension stalk lift

The globally nonzero actual connecting product supplies native stalk
freeness. The chart, ideal coordinate, free-source coordinate, and the
projection-compatible native stalk isomorphism are all constructed.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent.ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem cubicClosedPointSerreLocalKoszulNative_exists_stalk_lift
    (K : Type u) [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] {L : Type u} [Field L]
    (i : Spec (.of L) ⟶ hypersurface p hp) [IsClosedImmersion i]
    [hExt : HasExt.{u} (hypersurface p hp).Modules]
    [hExtStalk : HasExt.{u + 1}
      (ModuleCat.{u} ((hypersurface p hp).presheaf.stalk (i default)))]
    (e : SerreExtensionSequenceData (hypersurface p hp)
      (closedImmersionIdealTwist i
        (positiveSheafOfModules (grading (equationIdeal p hp)) 3)))
    (hne :
      letI := quotientPositiveTwist_tensorRight_preservesFiniteLimits (equationIdeal p hp) 3
      letI := quotientPositiveTwist_tensorRight_preservesFiniteColimits (equationIdeal p hp) 3
      (closedImmersionIdealTwistSequence_shortExact i
        (positiveSheafOfModules (grading (equationIdeal p hp)) 3)).extClass.comp
        (@SerreExtensionSequenceData.extensionClass.{u} (hypersurface p hp) _ e hExt)
        (show 1 + 1 = 2 by omega) ≠ 0) :
    ∃ d : CubicClosedPointSerreLocalKoszulChartData i
        (positiveSheafOfModules (grading (equationIdeal p hp)) 3),
      ∃ l : (schemeModuleStalkModuleFunctor (hypersurface p hp) (i default)).obj
          (SheafOfModules.free (R := (hypersurface p hp).ringCatSheaf) (ULift.{u} (Fin 2))) ≅
        (schemeModuleStalkModuleFunctor (hypersurface p hp) (i default)).obj e.E,
        l.hom ≫ (schemeModuleStalkModuleFunctor (hypersurface p hp) (i default)).map e.projection =
          cubicClosedPointSerreFreeNeighborhoodLocalStalkMap d.U ⟨i default, d.mem⟩
            (SheafOfModules.free (R := (hypersurface p hp).ringCatSheaf) (ULift.{u} (Fin 2)))
            (closedImmersionIdealTwist i
              (positiveSheafOfModules (grading (equationIdeal p hp)) 3))
            ((cubicClosedPointSerreFreeNeighborhoodLocalFreeToBiprodIso d.U).hom ≫
              d.sequence.last) := by
  let X := hypersurface p hp
  letI : HasExt.{u} X.Modules := hExt
  letI : HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf) := hExt
  let R := X.presheaf.stalk (i default)
  letI : HasExt.{u + 1} (ModuleCat.{u} R) := hExtStalk
  let P : X.Modules := positiveSheafOfModules (grading (equationIdeal p hp)) 3
  let d := Classical.choice (cubicClosedPointSerreLocalKoszulNative_exists_chart K p hp hp0 i)
  letI : Module.Free R ((schemeModuleStalkModuleFunctor X (i default)).obj e.E) := by
    exact cubicClosedPointSerreLocalFree_stalk_free K p hp hp0 i e hne
  obtain ⟨l, hl⟩ := @cubicClosedPointSerreLocalKoszul_exists_stalk_lift
    (hypersurface p hp) (Spec (.of L)) i inferInstance P
    d.U d.q d.f d.twist d.sequence ⟨i default, d.mem⟩ e
    (by exact cubicClosedPointSerreLocalFree_stalk_free K p hp hp0 i e hne)
    d.regular_first d.regular_second d.span_maximal
  exact ⟨d, l, hl⟩

end PfaffianDescent.ProjectiveNegativeTwist
