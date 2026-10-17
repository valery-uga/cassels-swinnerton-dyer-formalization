import PfaffianDescent.CubicClosedPointSerreLocalKoszulNativeAlignment

/-! # A constructed affine free neighborhood at the original closed point -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent.ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual nonzero connecting class constructs an actual rank-two
affine trivialization near the original closed field point. -/
theorem cubicClosedPointSerreFreeNeighborhood_native_exists_at_point
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
    ∃ (U : (hypersurface p hp).Opens), i default ∈ U ∧ IsAffineOpen U ∧
      Nonempty (SheafOfModules.free (R := (hypersurface p hp).ringCatSheaf.over U)
        (ULift.{u} (Fin 2)) ≅ e.E.over U) := by
  obtain ⟨d, l, hl⟩ := cubicClosedPointSerreLocalKoszulNative_exists_stalk_lift
    K p hp hp0 i e hne
  exact cubicClosedPointSerreFreeNeighborhood_exists_of_original_stalk_lift_iso
    e d.U (cubicClosedPointSerreLocalKoszulFirst d.U d.q d.f) d.sequence.last
    d.sequence.zero d.sequence.shortExact ⟨i default, d.mem⟩ l hl

end PfaffianDescent.ProjectiveNegativeTwist
