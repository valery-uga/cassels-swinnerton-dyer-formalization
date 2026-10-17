import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualCanonicalFinite
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualNormalizedGoodOpenRank
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualNormalizedCanonicalEndpointFinite
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualGoodOpenFieldPointRank

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent.ProjectiveNegativeTwist
open BundleSectionZeroLocus AllCharacteristics.HomogeneousProjective SerreExtensionData
open PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreFiniteZeroResidual_actualGoodOpen_rank_eleven
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
    letI := SerreExtensionRankTwoAffineCover.isProper_projectiveLineNormalizedLocalPencilZeroGluedToLine
      (hypersurfaceToBase p hp) C seed
    let g := C.projectiveLineNormalizedLocalPencilZeroGluedToAmbient (hypersurfaceToBase p hp) seed ≫
      projectiveLineAmbientToLine K (hypersurfaceToBase p hp)
    ∀ (y : projectiveLineProj K) (hy : (g ⁻¹' {y}).Finite),
    (g ∣_ cubicClosedPointSerreFiniteZeroResidual_goodOpen g).finrank
      ⟨y, cubicClosedPointSerreFiniteZeroResidual_mem_goodOpen_of_finite_fibre g y hy⟩ = 11 := by
  let f := hypersurfaceToBase p hp
  let c := C.localPencilZeroGluedToAmbient e seed (𝟙 _) 0 ≫ f
  have hd := cubicClosedPointSerreFiniteZeroResidual_canonical_finite_etale_rank_eleven
    K p hp hp0 i e hne hi hL C seed
  letI : IsFinite c := hd.1
  letI : Etale c := hd.2.1
  let iG := C.projectiveLineNormalizedLocalPencilZeroGluedToAmbient f seed
  let ep := cubicClosedPointSerreFiniteZeroResidual_normalizedEndpointAmbient f false
  let g := iG ≫ projectiveLineAmbientToLine K f
  letI : IsProper g := C.isProper_projectiveLineNormalizedLocalPencilZeroGluedToLine f seed
  letI : Flat (g ∣_ cubicClosedPointSerreFiniteZeroResidual_goodOpen g) :=
    cubicClosedPointSerreFiniteZeroResidual_normalizedGluedGoodOpen_flat p hp hp0 C seed
  let y₀ := projectiveLineEndpoint K false (IsLocalRing.closedPoint K)
  have h₀ : (g ⁻¹' {y₀}).Finite :=
    cubicClosedPointSerreFiniteZeroResidual_normalizedCanonicalEndpoint_finite f C seed
  have hm := cubicClosedPointSerreFiniteZeroResidual_mem_goodOpen_of_finite_fibre g y₀ h₀
  let cP := pullback.snd iG ep ≫ f
  have hcart : IsPullback (pullback.fst iG ep) cP g (projectiveLineEndpoint K false) :=
    (IsPullback.of_hasPullback iG ep).paste_vert
      (cubicClosedPointSerreFiniteZeroResidual_normalizedEndpointAmbient_isPullback f false)
  let a := cubicClosedPointSerreFiniteZeroResidual_normalizedEndpoint_iso f C seed
  have ha : a.hom ≫ c = cP := by
    dsimp only [c, cP]
    rw [← Category.assoc, cubicClosedPointSerreFiniteZeroResidual_normalizedEndpoint_iso_over]
  have hr : cP.finrank (IsLocalRing.closedPoint K) = 11 := by
    rw [← ha, Scheme.Hom.finrank_comp_left_of_isIso]
    exact hd.2.2 _
  have hr₀ := cubicClosedPointSerreFiniteZeroResidual_goodOpen_fieldPoint_rank
    g (projectiveLineEndpoint K false) (pullback.fst iG ep) cP hcart hm
  change ∀ (y : projectiveLineProj K) (hy : (g ⁻¹' {y}).Finite),
    (g ∣_ cubicClosedPointSerreFiniteZeroResidual_goodOpen g).finrank
      ⟨y, cubicClosedPointSerreFiniteZeroResidual_mem_goodOpen_of_finite_fibre g y hy⟩ = 11
  intro y hy
  have he := cubicClosedPointSerreFiniteZeroResidual_normalizedGluedGoodOpen_rank
    p hp hp0 C seed y y₀ hy h₀
  exact he.trans (hr₀.trans hr)

end PfaffianDescent.ProjectiveNegativeTwist
