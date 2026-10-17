import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualSelectedRankEleven

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent.ProjectiveNegativeTwist
open BundleSectionZeroLocus AllCharacteristics.HomogeneousProjective SerreExtensionData
open PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreFiniteZeroResidual_selected_finite_datum_eleven
    (K : Type u) [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] {L : Type u} [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
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
    (hi : i ≫ hypersurfaceToBase p hp = Spec.map (CommRingCat.ofHom (algebraMap K L)))
    (hL : Module.finrank K L = 11)
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (hf : ((C.projectiveLineNormalizedLocalPencilZeroGluedToAmbient (hypersurfaceToBase p hp) seed ≫
      projectiveLineAmbientToLine K (hypersurfaceToBase p hp)) ⁻¹'
        {projectiveLineEndpoint K true (IsLocalRing.closedPoint K)}).Finite) :
    ∃ D : AllCharacteristics.FiniteSubschemeDatum (hypersurfaceToBase p hp) 11,
      D.val = (C.localPencilZeroGluedToAmbient e seed 0 (𝟙 _)).ker := by
  have H := cubicClosedPointSerreFiniteZeroResidual_selected_finite_rank_eleven
    K p hp hp0 i e hne hi hL C seed hf
  letI : IsFinite (C.localPencilZeroGluedToAmbient e seed 0 (𝟙 _) ≫ hypersurfaceToBase p hp) := H.1
  exact ⟨C.localPencilZeroFiniteSubschemeDatumOfGluing e (hypersurfaceToBase p hp)
    seed 0 (𝟙 _) 11 H.2, rfl⟩

end PfaffianDescent.ProjectiveNegativeTwist
