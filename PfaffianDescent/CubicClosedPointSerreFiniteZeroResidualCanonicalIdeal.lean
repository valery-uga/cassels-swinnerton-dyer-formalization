import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualCanonicalChart
import PfaffianDescent.CubicClosedPointSerreZeroIdealStalkPullback

/-! # The canonical section has the actual original point ideal on affine charts -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent.ProjectiveNegativeTwist
open BundleSectionZeroLocus AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreFiniteZeroResidual_canonical_chart_ideal_eq
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
    (U : (hypersurface p hp).affineOpens)
    (t : SheafOfModules.free (R := (hypersurface p hp).ringCatSheaf.over U.1)
      (ULift.{u} (Fin 2)) ≅ e.E.over U.1) :
    letI : IsAffine (U.1 : Scheme.{u}) := U.2
    localSectionZeroIdealOfOver U.1 (ULift.{u} (Fin 2)) t e.canonicalSection =
      (pullback.snd i U.1.ι).ker := by
  letI : IsAffine (U.1 : Scheme.{u}) := U.2
  let Y := (U.1 : Scheme.{u})
  let W : Y.affineOpens := ⟨⊤, isAffineOpen_top Y⟩
  let a := localFreeIsoOfOver U.1 (ULift.{u} (Fin 2)) t
  let s := restrictSectionToOpen U.1 e.canonicalSection
  let c₀ := sectionCoordinateOfFreeIso (ULift.{u} (Fin 2)) a s (ULift.up 0)
  let c₁ := sectionCoordinateOfFreeIso (ULift.{u} (Fin 2)) a s (ULift.up 1)
  have hg (y : Y) :
      (Ideal.span ({c₀, c₁} : Set Γ(Y, ⊤))).map
          (Y.presheaf.germ ⊤ y trivial).hom =
        ((pullback.snd i U.1.ι).ker.ideal W).map
          (Y.presheaf.germ ⊤ y trivial).hom := by
    rw [Ideal.map_span, Set.image_pair]
    by_cases hy : U.1.ι y = i default
    · have hx : i default ∈ U.1 := hy ▸ y.2
      have he : y = (⟨i default, hx⟩ : U.1) := Subtype.ext hy
      subst y
      exact (cubicClosedPointSerreFiniteZeroResidual_canonical_chart_span_at_point
        K p hp hp0 i e hne U.1 hx t).trans
        (cubicClosedPointSerreZeroIdealStalkPullback_map_eq_maximal i U hx).symm
    · exact (cubicClosedPointSerreFiniteZeroResidual_canonical_chart_span_off_point
        K p hp i e U.1 y hy t).trans
        (cubicClosedPointSerreZeroIdealStalkPullback_map_eq_top_off_point i U y hy).symm
  have hi : Ideal.span ({c₀, c₁} : Set Γ(Y, ⊤)) =
      (pullback.snd i U.1.ι).ker.ideal W := by
    ext f
    rw [(isAffineOpen_top Y).mem_ideal_iff, (isAffineOpen_top Y).mem_ideal_iff]
    simp only [hg]
  apply Scheme.IdealSheafData.ext_of_isAffine
  rw [localSectionZeroIdealOfOver, sectionZeroIdealOfFreeIso_ulift_fin_two_eq,
    Scheme.IdealSheafData.ofIdealTop_ideal]
  change Ideal.map (Y.presheaf.map (𝟙 _)).hom
    (Ideal.span ({c₀} : Set Γ(Y, ⊤)) ⊔ Ideal.span {c₁}) =
      (pullback.snd i U.1.ι).ker.ideal W
  simpa only [CategoryTheory.Functor.map_id, CommRingCat.hom_id,
    Ideal.map_id, ← Ideal.span_union, Set.singleton_union] using hi

end PfaffianDescent.ProjectiveNegativeTwist
