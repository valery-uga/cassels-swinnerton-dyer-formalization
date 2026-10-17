import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualCanonicalIdeal
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualKernelCover

/-! # The actual canonical glued zero has the actual original closed kernel -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent.ProjectiveNegativeTwist
open BundleSectionZeroLocus AllCharacteristics.HomogeneousProjective SerreExtensionData
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreFiniteZeroResidual_canonical_glued_kernel_eq
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
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e) :
    (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed (𝟙 _) 0).ker =
      i.ker := by
  let c := SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed (𝟙 _) 0
  letI : IsClosedImmersion c :=
    SerreExtensionRankTwoAffineCover.isClosedImmersion_localPencilZeroGluedToAmbient_of_localPencilZeroGluing
      e C seed (𝟙 _) 0
  apply cubicClosedPointSerreFiniteZeroResidual_kernel_eq_of_affine_pullbacks c i
    (fun k => ⟨C.U k, C.affine k⟩) C.covers
  intro k
  let v := SerreExtensionRankTwoAffineCover.localPencilZeroGluedTargetPullbackι
    e C seed k (𝟙 _) 0
  letI : IsIso v :=
    SerreExtensionRankTwoAffineCover.isIso_localPencilZeroGluedTargetPullbackι
      e C seed k (𝟙 _) 0
      (SerreExtensionRankTwoAffineCover.range_localPencilZeroGluedTargetPullbackι_eq_univ
        e C seed k (𝟙 _) 0)
  rw [← Scheme.Hom.ker_comp_of_isIso v (pullback.snd c (C.U k).ι)]
  rw [SerreExtensionRankTwoAffineCover.localPencilZeroGluedTargetPullbackι_comp_snd]
  rw [Scheme.IdealSheafData.ker_subschemeι,
    SerreExtensionRankTwoAffineCover.localPencilZeroIdeal_one_zero]
  exact cubicClosedPointSerreFiniteZeroResidual_canonical_chart_ideal_eq
    K p hp hp0 i e hne ⟨C.U k, C.affine k⟩ (C.trivialization k)

/-- The canonical endpoint is the actual original point, over the original cubic. -/
def cubicClosedPointSerreFiniteZeroResidual_canonical_glued_iso
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
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e) :
    Spec (.of L) ≅ SerreExtensionRankTwoAffineCover.localPencilZeroGluedScheme e C seed (𝟙 _) 0 := by
  let c := SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed (𝟙 _) 0
  letI : IsClosedImmersion c :=
    SerreExtensionRankTwoAffineCover.isClosedImmersion_localPencilZeroGluedToAmbient_of_localPencilZeroGluing
      e C seed (𝟙 _) 0
  let h := cubicClosedPointSerreFiniteZeroResidual_canonical_glued_kernel_eq
    K p hp hp0 i e hne C seed
  let w := IsClosedImmersion.lift c i h.le
  letI : IsIso w := IsClosedImmersion.isIso_lift c i h
  exact asIso w

@[reassoc]
theorem cubicClosedPointSerreFiniteZeroResidual_canonical_glued_iso_hom_comp
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
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e) :
    (cubicClosedPointSerreFiniteZeroResidual_canonical_glued_iso
      K p hp hp0 i e hne C seed).hom ≫
      SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed (𝟙 _) 0 = i := by
  letI : IsClosedImmersion
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed (𝟙 _) 0) :=
    SerreExtensionRankTwoAffineCover.isClosedImmersion_localPencilZeroGluedToAmbient_of_localPencilZeroGluing
      e C seed (𝟙 _) 0
  exact IsClosedImmersion.lift_fac _ _ _

end PfaffianDescent.ProjectiveNegativeTwist
