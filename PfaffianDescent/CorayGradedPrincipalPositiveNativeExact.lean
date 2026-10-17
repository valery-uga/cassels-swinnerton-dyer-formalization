import PfaffianDescent.CorayGradedPrincipalPositiveFractionExact
import PfaffianDescent.ProjectiveClosedImmersion

/-! SOURCE ONLY. Bounded exactness transport for actual native positive
stalks of a graded principal quotient. The quotient need not be reduced. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopCat
open ProjectiveNegativeTwist
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Reflect exactness through a commuting function diagram. This proof
contains no scheme, module, localization, or quotient-ring conversions. -/
theorem exact_of_positiveNativeFractionDiagram
    {U V W U' V' W' : Type*} [Zero W] [Zero W']
    (fA : U → V) (gA : V → W) (F : U' → V') (G : V' → W')
    (tSource : U → U') (tMiddle : V → V') (tTarget : W → W')
    (htSourceSurj : Function.Surjective tSource)
    (htMiddleInj : Function.Injective tMiddle)
    (htTargetInj : Function.Injective tTarget)
    (htTargetZero : tTarget 0 = 0)
    (hfcomp : ∀ z, tMiddle (fA z) = F (tSource z))
    (hgcomp : ∀ z, tTarget (gA z) = G (tMiddle z))
    (hlocal : Function.Exact F G) : Function.Exact fA gA := by
  intro v
  constructor
  · intro hgv
    have hG : G (tMiddle v) = 0 := by
      calc
        _ = tTarget (gA v) := (hgcomp v).symm
        _ = tTarget 0 := congrArg tTarget hgv
        _ = 0 := htTargetZero
    obtain ⟨w, hw⟩ := (hlocal (tMiddle v)).mp hG
    obtain ⟨z, hz⟩ := htSourceSurj w
    refine ⟨z, htMiddleInj ?_⟩
    calc
      tMiddle (fA z) = F (tSource z) := hfcomp z
      _ = F w := congrArg F hz
      _ = tMiddle v := hw
  · rintro ⟨z, rfl⟩
    apply htTargetInj
    have hzero : G (F (tSource z)) = 0 :=
      (hlocal (F (tSource z))).mpr ⟨tSource z, rfl⟩
    calc
      tTarget (gA (fA z)) = G (tMiddle (fA z)) := hgcomp (fA z)
      _ = G (F (tSource z)) := congrArg G (hfcomp z)
      _ = 0 := hzero
      _ = tTarget 0 := htTargetZero.symm

/-- A surjective graded principal quotient gives exactness of its ACTUAL
native positive-stalk sequence at every point in its projective image.
The closed immersion and pushforward-stalk Iso are derived internally.
No native comparison, exactness, or IsIso hypothesis is supplied. -/
theorem gradedPrincipal_positiveNativeStalk_exact_image
    {A B σ τ : Type u} [CommRing A] [CommRing B]
    [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
    (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]
    (f : 𝒜 →+*ᵍ ℬ) (hf : Function.Surjective f)
    {d : ℕ} (s : 𝒜 d)
    (hker : RingHom.ker f.toRingHom = Ideal.span ({(s : A)} : Set A))
    (m : ℕ) (y : Proj ℬ) :
    Function.Exact
      (schemeModuleStalkLinearMap (positiveMulHomogeneous 𝒜 s m)
        (Proj.map f (gradedSurjective_irrelevant_le f hf) y))
      (schemeModuleStalkLinearMap
        (gradedRingHomPositiveTwistToPushforward 𝒜 ℬ f
          (gradedSurjective_irrelevant_le f hf) (m + d))
        (Proj.map f (gradedSurjective_irrelevant_le f hf) y)) := by
  let h := gradedSurjective_irrelevant_le f hf
  let i := Proj.map f h
  letI : IsClosedImmersion i := projectiveMap_closedImmersion_of_surjective f hf
  let x := i y
  let fA := schemeModuleStalkLinearMap (positiveMulHomogeneous 𝒜 s m) x
  let gA := schemeModuleStalkLinearMap
    (gradedRingHomPositiveTwistToPushforward 𝒜 ℬ f h (m + d)) x
  let tSource := positiveStalkToFractionModule 𝒜 m x
  let tMiddle := positiveStalkToFractionModule 𝒜 (m + d) x
  let push := TopCat.Presheaf.stalkPushforward AddCommGrpCat i.base
    (positiveSheafOfModules ℬ (m + d)).val.presheaf y
  let tTarget := fun z => positiveStalkToFractionModule ℬ (m + d) y (push z)
  let F := positiveMulHomogeneousStalk 𝒜 x.asHomogeneousIdeal.toIdeal s m
  let G := gradedRingHomPositiveTwistStalkMap 𝒜 ℬ f h (m + d) y
  letI : IsIso push :=
    TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
      AddCommGrpCat i.isClosedEmbedding.isInducing
      (positiveSheafOfModules ℬ (m + d)).val.presheaf y
  have htSourceSurj : Function.Surjective tSource :=
    positiveStalkToFractionModule_surjective 𝒜 m x
  have htMiddleInj : Function.Injective tMiddle :=
    positiveStalkToFractionModule_injective 𝒜 (m + d) x
  have htTargetInj : Function.Injective tTarget := by
    intro a b hab
    apply (ConcreteCategory.bijective_of_isIso push).injective
    apply positiveStalkToFractionModule_injective ℬ (m + d) y
    exact hab
  have htTargetZero : tTarget 0 = 0 := by
    change positiveStalkToFractionModule ℬ (m + d) y (push 0) = 0
    rw [map_zero, map_zero]
  have hlocal : Function.Exact F G :=
    gradedPrincipal_positiveFraction_exact 𝒜 ℬ f hf s hker m y
  have hfcomp (z) : tMiddle (fA z) = F (tSource z) :=
    positiveStalkToFractionModule_stalkMap 𝒜 s m x z
  have hgcomp (z) : tTarget (gA z) = G (tMiddle z) :=
    gradedRingHomPositiveTwistToPushforward_stalkMap_compat 𝒜 ℬ f h (m + d) y z
  exact exact_of_positiveNativeFractionDiagram fA gA F G tSource tMiddle tTarget
    htSourceSurj htMiddleInj htTargetInj htTargetZero hfcomp hgcomp hlocal

end PfaffianDescent.Coray
end
