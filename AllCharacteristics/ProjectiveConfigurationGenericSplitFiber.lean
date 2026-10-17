import AllCharacteristics.ProjectiveConfigurationFiberSubscheme
import AllCharacteristics.ProjectiveConfigurationFiberCycle

/-!
# Marked points of a split generic configuration fiber

An ordered lift of the generic unordered configuration splits its finite
incidence fiber into labeled components.  The component maps constructed in
`ProjectiveConfigurationFiberSubscheme` are shown here to recover exactly the
corresponding marked projective points.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace AllCharacteristics

universe u v

variable {A : Type u} [CommRing A] {σ : Type v} [SetLike σ A]
  [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable {K : Type u} [Field K]
variable (f : Proj 𝒜 ⟶ Spec (.of K)) [IsSeparated f]

/-- The generic finite-scheme/incidence-fiber identification preserves the
map to the original projective family. -/
@[reassoc]
lemma projectiveConfigurationGenericFiniteSubschemeIsoIncidenceFiber_hom_toProjective
    (n : ℕ)
    [IsIntegral (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme] :
    (projectiveConfigurationGenericFiniteSubschemeIsoIncidenceFiber 𝒜 f n).hom ≫
        pullback.fst (projectiveConfigurationIncidenceToBase 𝒜 f n)
          ((projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.fromSpecStalk
            (genericPoint (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme)) ≫
        projectiveConfigurationIncidenceToProjective 𝒜 f n =
      (projectiveConfigurationGenericFiniteSubscheme 𝒜 f n).val.subschemeι ≫
        pullback.fst
          (pullback.snd f (projectiveConfigurationQuotientToBase 𝒜 f n))
          ((projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.fromSpecStalk
            (genericPoint (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme)) ≫
        pullback.fst f (projectiveConfigurationQuotientToBase 𝒜 f n) := by
  let B := (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme
  let c := B.fromSpecStalk (genericPoint B)
  let q := projectiveConfigurationQuotientToBase 𝒜 f n
  let p := pullback.snd f q
  let U := projectiveConfigurationFiniteSubscheme 𝒜 f n
  let g := pullback.fst p c
  rw [← Category.assoc,
    projectiveConfigurationGenericFiniteSubschemeIsoIncidenceFiber_hom_fst]
  unfold projectiveConfigurationIncidenceToProjective
  change idealSubschemeBaseChangeMap U.val g ≫
      U.val.subschemeι ≫ pullback.fst f q =
    (U.val.comap g).subschemeι ≫ g ≫ pullback.fst f q
  simpa only [Category.assoc] using congrArg
    (fun t => t ≫ pullback.fst f q)
    (isPullback_idealSubschemeBaseChange U.val g).w.symm

/-- After identifying the actual generic finite scheme with the generic
incidence fiber, its `i`th split component maps to the `i`th marked projective
point of the ordered lift. -/
lemma projectiveConfigurationOrderedGenericComponentPoint_toProjective
    (n : ℕ)
    [IsIntegral (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme]
    {L : Type u} [Field L]
    (r : Spec (.of L) ⟶ (orderedFamilyConfigurationOver f n).left)
    (b : (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.functionField →+* L)
    (hb : Spec.map (CommRingCat.ofHom b) ≫
        (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.fromSpecStalk
          (genericPoint (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme) =
      r ≫ projectiveConfigurationQuotientMap 𝒜 f n)
    (i : Fin n) :
    projectiveConfigurationOrderedGenericComponentPoint 𝒜 f n r b hb i ≫
        (projectiveConfigurationGenericFiniteSubschemeIsoIncidenceFiber 𝒜 f n).hom ≫
        pullback.fst (projectiveConfigurationIncidenceToBase 𝒜 f n)
          ((projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.fromSpecStalk
            (genericPoint (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme)) ≫
        projectiveConfigurationIncidenceToProjective 𝒜 f n =
      r ≫ (orderedFamilyConfigurationOpen f n).ι ≫
        (orderedFamilyCoordinate f n i).left := by
  unfold projectiveConfigurationOrderedGenericComponentPoint
  unfold projectiveConfigurationOrderedGenericFiberToFiniteSubscheme
  simp only [Category.assoc]
  rw [Iso.inv_hom_id_assoc]
  rw [pullback.lift_fst_assoc]
  rw [Category.comp_id]
  rw [projectiveConfigurationIncidenceFiberIsoConstantCover_component_fst_assoc]
  exact congrArg (r ≫ ·)
    (projectiveConfigurationMarkedToIncidence_toProjective 𝒜 f n i)

/-- Each split component of the genuine generic finite subscheme maps under
its actual ambient closed immersion to the corresponding ordered marked
projective point. -/
lemma projectiveConfigurationOrderedGenericComponentPoint_toAmbientProjective
    (n : ℕ)
    [IsIntegral (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme]
    {L : Type u} [Field L]
    (r : Spec (.of L) ⟶ (orderedFamilyConfigurationOver f n).left)
    (b : (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.functionField →+* L)
    (hb : Spec.map (CommRingCat.ofHom b) ≫
        (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.fromSpecStalk
          (genericPoint (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme) =
      r ≫ projectiveConfigurationQuotientMap 𝒜 f n)
    (i : Fin n) :
    projectiveConfigurationOrderedGenericComponentPoint 𝒜 f n r b hb i ≫
        (projectiveConfigurationGenericFiniteSubscheme 𝒜 f n).val.subschemeι ≫
        pullback.fst
          (pullback.snd f (projectiveConfigurationQuotientToBase 𝒜 f n))
          ((projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.fromSpecStalk
            (genericPoint (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme)) ≫
        pullback.fst f (projectiveConfigurationQuotientToBase 𝒜 f n) =
      r ≫ (orderedFamilyConfigurationOpen f n).ι ≫
        (orderedFamilyCoordinate f n i).left := by
  let a := projectiveConfigurationOrderedGenericComponentPoint 𝒜 f n r b hb i
  have hambient :=
    projectiveConfigurationGenericFiniteSubschemeIsoIncidenceFiber_hom_toProjective
      𝒜 f n
  have htransport := congrArg (fun t => a ≫ t) hambient.symm
  calc
    a ≫ (projectiveConfigurationGenericFiniteSubscheme 𝒜 f n).val.subschemeι ≫
          pullback.fst
            (pullback.snd f (projectiveConfigurationQuotientToBase 𝒜 f n))
            ((projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.fromSpecStalk
              (genericPoint (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme)) ≫
          pullback.fst f (projectiveConfigurationQuotientToBase 𝒜 f n) =
        a ≫ (projectiveConfigurationGenericFiniteSubschemeIsoIncidenceFiber 𝒜 f n).hom ≫
          pullback.fst (projectiveConfigurationIncidenceToBase 𝒜 f n)
            ((projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.fromSpecStalk
              (genericPoint (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme)) ≫
          projectiveConfigurationIncidenceToProjective 𝒜 f n := by
            simpa only [Category.assoc] using htransport
    _ = _ := projectiveConfigurationOrderedGenericComponentPoint_toProjective
      𝒜 f n r b hb i

end AllCharacteristics
