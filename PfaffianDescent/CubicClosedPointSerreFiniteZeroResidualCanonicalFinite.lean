import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualCanonicalKernel

/-! # Actual degree-eleven finite étale canonical section zero -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent.ProjectiveNegativeTwist
open BundleSectionZeroLocus AllCharacteristics.HomogeneousProjective SerreExtensionData
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreFiniteZeroResidual_canonical_finite_etale_rank_eleven
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
    let g := SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed (𝟙 _) 0 ≫
      hypersurfaceToBase p hp
    IsFinite g ∧ Etale g ∧ (∀ x, g.finrank x = 11) := by
  let c := SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed (𝟙 _) 0
  let g := c ≫ hypersurfaceToBase p hp
  let a := cubicClosedPointSerreFiniteZeroResidual_canonical_glued_iso K p hp hp0 i e hne C seed
  have ha : a.hom ≫ c = i :=
    cubicClosedPointSerreFiniteZeroResidual_canonical_glued_iso_hom_comp K p hp hp0 i e hne C seed
  letI : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap K L))) :=
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  letI : Module.FinitePresentation K L := Module.finitePresentation_of_finite K L
  letI : Algebra.Etale K L := {
    formallyEtale := Algebra.FormallyEtale.of_isSeparable K L
    finitePresentation := Algebra.FinitePresentation.of_finitePresentation K L
  }
  letI : Etale (Spec.map (CommRingCat.ofHom (algebraMap K L))) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
      (RingHom.etale_algebraMap.mpr inferInstance)
  have he : g = a.inv ≫ Spec.map (CommRingCat.ofHom (algebraMap K L)) := by
    rw [← cancel_epi a.hom]
    simp only [Iso.hom_inv_id_assoc]
    change a.hom ≫ (c ≫ hypersurfaceToBase p hp) = _
    rw [← Category.assoc, ha]
    exact hi
  letI : IsFinite g := by rw [he]; infer_instance
  letI : Etale g := by rw [he]; infer_instance
  refine ⟨inferInstance, inferInstance, ?_⟩
  intro x
  change g.finrank x = 11
  rw [he, Scheme.Hom.finrank_comp_left_of_isIso, Scheme.Hom.finrank_SpecMap_algebraMap]
  exact (congrFun (Module.rankAtStalk_eq_finrank_of_free (R := K) (M := L)) x).trans hL

end PfaffianDescent.ProjectiveNegativeTwist
