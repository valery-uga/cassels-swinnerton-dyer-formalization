import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualCanonicalFinite

/-! # The native rank-eleven canonical finite datum -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent.ProjectiveNegativeTwist
open BundleSectionZeroLocus AllCharacteristics.HomogeneousProjective SerreExtensionData
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreFiniteZeroResidual_exists_canonical_finite_etale_datum
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
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e) :
    ∃ D : AllCharacteristics.FiniteSubschemeDatum (hypersurfaceToBase p hp) 11,
      D.val = (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient
        e C seed (𝟙 _) 0).ker ∧ Etale (D.val.subschemeι ≫ hypersurfaceToBase p hp) := by
  let g := SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed (𝟙 _) 0 ≫
    hypersurfaceToBase p hp
  have H := cubicClosedPointSerreFiniteZeroResidual_canonical_finite_etale_rank_eleven
    K p hp hp0 i e hne hi hL C seed
  letI : IsFinite g := H.1
  letI : Etale g := H.2.1
  let D := SerreExtensionRankTwoAffineCover.localPencilZeroFiniteSubschemeDatumOfGluing
    e (hypersurfaceToBase p hp) C seed (𝟙 _) 0 11 H.2.2
  have hc : IsClosedImmersion
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed (𝟙 _) 0) :=
    SerreExtensionRankTwoAffineCover.isClosedImmersion_localPencilZeroGluedToAmbient_of_localPencilZeroGluing
      e C seed (𝟙 _) 0
  letI := hc
  refine ⟨D, rfl, ?_⟩
  let a := SerreExtensionRankTwoAffineCover.localPencilZeroFiniteSubschemeDatumOfGluingIso
    e (hypersurfaceToBase p hp) C seed (𝟙 _) 0 11 H.2.2
  have ha := SerreExtensionRankTwoAffineCover.localPencilZeroFiniteSubschemeDatumOfGluingIso_hom_ι
    e (hypersurfaceToBase p hp) C seed (𝟙 _) 0 11 H.2.2
  have he : D.val.subschemeι ≫ hypersurfaceToBase p hp = a.inv ≫ g := by
    rw [← cancel_epi a.hom, Iso.hom_inv_id_assoc, ← Category.assoc, ha]
  rw [he]
  infer_instance

end PfaffianDescent.ProjectiveNegativeTwist
