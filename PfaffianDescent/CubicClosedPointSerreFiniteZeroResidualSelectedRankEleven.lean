import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualActualGoodOpenRankEleven
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualNormalizedSelectedFinite

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent.ProjectiveNegativeTwist
open BundleSectionZeroLocus AllCharacteristics.HomogeneousProjective SerreExtensionData
open PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreFiniteZeroResidual_selected_finite_rank_eleven
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
    let c := C.localPencilZeroGluedToAmbient e seed 0 (𝟙 _) ≫ hypersurfaceToBase p hp
    IsFinite c ∧ (∀ x, c.finrank x = 11) := by
  let f := hypersurfaceToBase p hp
  let c := C.localPencilZeroGluedToAmbient e seed 0 (𝟙 _) ≫ f
  letI : IsFinite c := cubicClosedPointSerreFiniteZeroResidual_normalizedSelected_finite f C seed hf
  refine ⟨inferInstance, ?_⟩
  let iG := C.projectiveLineNormalizedLocalPencilZeroGluedToAmbient f seed
  let ep := cubicClosedPointSerreFiniteZeroResidual_normalizedEndpointAmbient f true
  let g := iG ≫ projectiveLineAmbientToLine K f
  letI : IsProper g := C.isProper_projectiveLineNormalizedLocalPencilZeroGluedToLine f seed
  letI : Flat (g ∣_ cubicClosedPointSerreFiniteZeroResidual_goodOpen g) :=
    cubicClosedPointSerreFiniteZeroResidual_normalizedGluedGoodOpen_flat p hp hp0 C seed
  let y := projectiveLineEndpoint K true (IsLocalRing.closedPoint K)
  have hm := cubicClosedPointSerreFiniteZeroResidual_mem_goodOpen_of_finite_fibre g y hf
  let cP := pullback.snd iG ep ≫ f
  have hcart : IsPullback (pullback.fst iG ep) cP g (projectiveLineEndpoint K true) :=
    (IsPullback.of_hasPullback iG ep).paste_vert
      (cubicClosedPointSerreFiniteZeroResidual_normalizedEndpointAmbient_isPullback f true)
  let a := cubicClosedPointSerreFiniteZeroResidual_normalizedInfinityEndpoint_iso f C seed
  have ha : a.hom ≫ c = cP := by
    dsimp only [c, cP]
    rw [← Category.assoc, cubicClosedPointSerreFiniteZeroResidual_normalizedInfinityEndpoint_iso_over]
  have hr := cubicClosedPointSerreFiniteZeroResidual_goodOpen_fieldPoint_rank
    g (projectiveLineEndpoint K true) (pullback.fst iG ep) cP hcart hm
  have h11 := cubicClosedPointSerreFiniteZeroResidual_actualGoodOpen_rank_eleven
    K p hp hp0 i e hne hi hL C seed y hf
  have hc : c.finrank (IsLocalRing.closedPoint K) = 11 := by
    rw [← ha, Scheme.Hom.finrank_comp_left_of_isIso] at hr
    exact hr.symm.trans h11
  intro x
  exact (congrArg c.finrank (Subsingleton.elim x (IsLocalRing.closedPoint K))).trans hc

end PfaffianDescent.ProjectiveNegativeTwist
