import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualBasisRestriction

/-! # The actual canonical ideal after restriction to an affine chart -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent.ProjectiveNegativeTwist
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreFiniteZeroResidual_canonical_restricted_stalk_span
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
        (show 1 + 1 = 2 by omega) ≠ 0)
    (U : (hypersurface p hp).Opens) (hx : i default ∈ U) :
    let X := hypersurface p hp
    let x : U := ⟨i default, hx⟩
    let N : X.Modules := e.E
    letI : Module (X.presheaf.stalk (i default)) (N.presheaf.stalk (i default)) :=
      schemeModuleStalkModule N (i default)
    letI : Module ((U : Scheme).presheaf.stalk x) ((N.restrict U.ι).presheaf.stalk x) :=
      schemeModuleStalkModule (N.restrict U.ι) x
    ∀ t : (N.restrict U.ι).presheaf.stalk x ≃ₗ[(U : Scheme).presheaf.stalk x]
        (((U : Scheme).presheaf.stalk x) × ((U : Scheme).presheaf.stalk x)),
      Ideal.span ({
        (t ((Scheme.Modules.restrictStalkNatIso U.ι x).inv.app N
          (serreExtensionStalkCanonicalSection e (i default) 1))).1,
        (t ((Scheme.Modules.restrictStalkNatIso U.ι x).inv.app N
          (serreExtensionStalkCanonicalSection e (i default) 1))).2} :
        Set ((U : Scheme).presheaf.stalk x)) =
        IsLocalRing.maximalIdeal ((U : Scheme).presheaf.stalk x) := by
  dsimp only
  intro t
  let x : U := ⟨i default, hx⟩
  let N : (hypersurface p hp).Modules := e.E
  letI := schemeModuleStalkModule N (i default)
  letI := schemeModuleStalkModule (N.restrict U.ι) x
  let t₀ := cubicClosedPointSerreFiniteZeroResidual_restrictionBasis U x N t
  have h := cubicClosedPointSerreFiniteZeroResidual_canonical_stalk_span
    K p hp hp0 i e hne t₀
  have hm := congrArg (Ideal.map (U.ι.stalkMap x).hom) h
  have ht := cubicClosedPointSerreFiniteZeroResidual_restrictionBasis_span U x N t
    (serreExtensionStalkCanonicalSection e (i default) 1)
  have h' := ht.symm.trans hm
  exact h'.trans (cubicClosedPointSerreFiniteZeroResidual_restriction_maximalIdeal U x)

end PfaffianDescent.ProjectiveNegativeTwist
