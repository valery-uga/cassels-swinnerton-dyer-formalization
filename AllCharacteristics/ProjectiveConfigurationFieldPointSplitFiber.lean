import AllCharacteristics.ProjectiveConfigurationGenericSplitFiber

/-!
# Labeled components of a field-valued configuration finite scheme

At an ordered field-valued configuration, the split incidence fiber and the
actual finite subscheme have the same labeled maps to the ambient projective
scheme.  This is the field-point counterpart of the generic-fiber comparison.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace AllCharacteristics

universe u v

variable {A : Type u} [CommRing A] {σ : Type v} [SetLike σ A]
  [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable {K : Type u} [Field K]
variable (f : Proj 𝒜 ⟶ Spec (.of K)) [IsSeparated f]

@[reassoc]
lemma projectiveConfigurationFiberFiniteSubschemeIsoIncidenceFiber_hom_fst
    (n : ℕ)
    (c : Spec (.of K) ⟶ (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme) :
    (projectiveConfigurationFiberFiniteSubschemeIsoIncidenceFiber 𝒜 f n c).hom ≫
      pullback.fst (projectiveConfigurationIncidenceToBase 𝒜 f n) c =
    idealSubschemeBaseChangeMap (projectiveConfigurationFiniteSubscheme 𝒜 f n).val
      (pullback.fst
        (pullback.snd f (projectiveConfigurationQuotientToBase 𝒜 f n)) c) := by
  let p := pullback.snd f (projectiveConfigurationQuotientToBase 𝒜 f n)
  let D := projectiveConfigurationFiniteSubscheme 𝒜 f n
  exact (isPullback_idealSubschemeFamily D.val (pullback.fst p c)
    (pullback.snd p c) p c (IsPullback.of_hasPullback p c)).isoPullback_hom_fst

/-- The finite-subschema/incidence-fiber isomorphism over any field point
preserves the map to the original projective scheme. -/
@[reassoc]
lemma projectiveConfigurationFiberFiniteSubschemeIsoIncidenceFiber_hom_toProjective
    (n : ℕ)
    (c : Spec (.of K) ⟶ (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme) :
    (projectiveConfigurationFiberFiniteSubschemeIsoIncidenceFiber 𝒜 f n c).hom ≫
        pullback.fst (projectiveConfigurationIncidenceToBase 𝒜 f n) c ≫
        projectiveConfigurationIncidenceToProjective 𝒜 f n =
      (projectiveConfigurationFiberFiniteSubscheme 𝒜 f n c).val.subschemeι ≫
        pullback.fst
          (pullback.snd f (projectiveConfigurationQuotientToBase 𝒜 f n)) c ≫
        pullback.fst f (projectiveConfigurationQuotientToBase 𝒜 f n) := by
  let q := projectiveConfigurationQuotientToBase 𝒜 f n
  let p := pullback.snd f q
  let U := projectiveConfigurationFiniteSubscheme 𝒜 f n
  let g := pullback.fst p c
  rw [← Category.assoc,
    projectiveConfigurationFiberFiniteSubschemeIsoIncidenceFiber_hom_fst]
  change idealSubschemeBaseChangeMap U.val g ≫
      U.val.subschemeι ≫ pullback.fst f q =
    (U.val.comap g).subschemeι ≫ g ≫ pullback.fst f q
  simpa only [Category.assoc] using congrArg
    (fun t => t ≫ pullback.fst f q)
    (isPullback_idealSubschemeBaseChange U.val g).w.symm

/-- Each labeled component of the pulled-back finite subscheme maps to
the corresponding marked projective point of the ordered configuration. -/
lemma projectiveConfigurationOrderedFiberFiniteSubscheme_component_toProjective
    (n : ℕ)
    (r : Spec (.of K) ⟶ (orderedFamilyConfigurationOver f n).left)
    (i : Fin n) :
    Sigma.ι (fun _ : ULift.{u} (Fin n) ↦ Spec (.of K)) (ULift.up i) ≫
        (projectiveConfigurationOrderedFiberFiniteSubschemeIsoConstantCover
          𝒜 f n r).hom ≫
        (projectiveConfigurationFiberFiniteSubscheme 𝒜 f n
          (r ≫ projectiveConfigurationQuotientMap 𝒜 f n)).val.subschemeι ≫
        pullback.fst
          (pullback.snd f (projectiveConfigurationQuotientToBase 𝒜 f n))
          (r ≫ projectiveConfigurationQuotientMap 𝒜 f n) ≫
        pullback.fst f (projectiveConfigurationQuotientToBase 𝒜 f n) =
      r ≫ (orderedFamilyConfigurationOpen f n).ι ≫
        (orderedFamilyCoordinate f n i).left := by
  let c := r ≫ projectiveConfigurationQuotientMap 𝒜 f n
  let e := projectiveConfigurationFiberFiniteSubschemeIsoIncidenceFiber 𝒜 f n c
  let s := projectiveConfigurationIncidenceFiberIsoConstantCover 𝒜 f n r
  have he := projectiveConfigurationFiberFiniteSubschemeIsoIncidenceFiber_hom_toProjective
    𝒜 f n c
  have htransport : e.inv ≫
      (projectiveConfigurationFiberFiniteSubscheme 𝒜 f n c).val.subschemeι ≫
      pullback.fst
        (pullback.snd f (projectiveConfigurationQuotientToBase 𝒜 f n)) c ≫
      pullback.fst f (projectiveConfigurationQuotientToBase 𝒜 f n) =
      pullback.fst (projectiveConfigurationIncidenceToBase 𝒜 f n) c ≫
      projectiveConfigurationIncidenceToProjective 𝒜 f n := by
    calc
      e.inv ≫ _ = e.inv ≫ (e.hom ≫
          pullback.fst (projectiveConfigurationIncidenceToBase 𝒜 f n) c ≫
          projectiveConfigurationIncidenceToProjective 𝒜 f n) := by
            rw [he]
      _ = _ := by simp [Category.assoc]
  change Sigma.ι (fun _ : ULift.{u} (Fin n) ↦ Spec (.of K)) (ULift.up i) ≫
    s.hom ≫ e.inv ≫
      (projectiveConfigurationFiberFiniteSubscheme 𝒜 f n c).val.subschemeι ≫
      pullback.fst
        (pullback.snd f (projectiveConfigurationQuotientToBase 𝒜 f n)) c ≫
      pullback.fst f (projectiveConfigurationQuotientToBase 𝒜 f n) =
    r ≫ (orderedFamilyConfigurationOpen f n).ι ≫
      (orderedFamilyCoordinate f n i).left
  conv_lhs => simp only [Category.assoc]
  rw [htransport]
  rw [projectiveConfigurationIncidenceFiberIsoConstantCover_component_fst_assoc]
  exact congrArg (r ≫ ·)
    (projectiveConfigurationMarkedToIncidence_toProjective 𝒜 f n i)

/-- The labeled splitting of the finite subscheme on the original
projective scheme recovers precisely the ordered marked points. -/
lemma projectiveConfigurationFiniteSubschemeAtIsoConstantCover_component_toProjective
    (n : ℕ)
    (r : Spec (.of K) ⟶ (orderedFamilyConfigurationOver f n).left)
    (hc : (r ≫ projectiveConfigurationQuotientMap 𝒜 f n) ≫
      projectiveConfigurationQuotientToBase 𝒜 f n = 𝟙 _)
    (k : Fin n) :
    Sigma.ι (fun _ : ULift.{u} (Fin n) ↦ Spec (.of K)) (ULift.up k) ≫
        (projectiveConfigurationFiniteSubschemeAtIsoConstantCover
          𝒜 f n r hc).hom ≫
        (projectiveConfigurationFiniteSubschemeAt 𝒜 f n
          (r ≫ projectiveConfigurationQuotientMap 𝒜 f n) hc).val.subschemeι =
      r ≫ (orderedFamilyConfigurationOpen f n).ι ≫
        (orderedFamilyCoordinate f n k).left := by
  let c := r ≫ projectiveConfigurationQuotientMap 𝒜 f n
  let q := projectiveConfigurationQuotientToBase 𝒜 f n
  let g := pullback.snd f q
  let D := projectiveConfigurationFiberFiniteSubscheme 𝒜 f n c
  let e := pullbackLeftPullbackSndIso f q c
  let m := pullback.fst f (c ≫ q)
  let j := D.val.subschemeι ≫ e.hom ≫ m
  haveI : IsIso m := by
    dsimp [m]
    rw [hc]
    infer_instance
  haveI : IsClosedImmersion j := by
    dsimp [j]
    infer_instance
  have htoImage :
      (projectiveConfigurationFiniteSubschemeAtIsoConstantCover 𝒜 f n r hc).hom ≫
        (projectiveConfigurationFiniteSubschemeAt 𝒜 f n c hc).val.subschemeι =
      (projectiveConfigurationOrderedFiberFiniteSubschemeIsoConstantCover
        𝒜 f n r).hom ≫ j := by
    change ((projectiveConfigurationOrderedFiberFiniteSubschemeIsoConstantCover
      𝒜 f n r ≪≫ asIso j.toImage).hom ≫ j.ker.subschemeι) = _
    have hj : (asIso j.toImage).hom ≫ j.ker.subschemeι = j := by
      change j.toImage ≫ j.imageι = j
      exact j.toImage_imageι
    simpa only [Iso.trans_hom, Category.assoc] using
      congrArg
        (fun t => (projectiveConfigurationOrderedFiberFiniteSubschemeIsoConstantCover
          𝒜 f n r).hom ≫ t) hj
  have hem : e.hom ≫ m =
      pullback.fst g c ≫ pullback.fst f q := by
    dsimp [e, m, g]
    exact pullbackLeftPullbackSndIso_hom_fst f q c
  calc
    Sigma.ι (fun _ : ULift.{u} (Fin n) ↦ Spec (.of K)) (ULift.up k) ≫
        (projectiveConfigurationFiniteSubschemeAtIsoConstantCover
          𝒜 f n r hc).hom ≫
        (projectiveConfigurationFiniteSubschemeAt 𝒜 f n c hc).val.subschemeι =
      Sigma.ι (fun _ : ULift.{u} (Fin n) ↦ Spec (.of K)) (ULift.up k) ≫
        (projectiveConfigurationOrderedFiberFiniteSubschemeIsoConstantCover
          𝒜 f n r).hom ≫ j := by
            simpa only [Category.assoc] using
              congrArg
                (fun t => Sigma.ι
                  (fun _ : ULift.{u} (Fin n) ↦ Spec (.of K)) (ULift.up k) ≫ t)
                htoImage
    _ = Sigma.ι (fun _ : ULift.{u} (Fin n) ↦ Spec (.of K)) (ULift.up k) ≫
        (projectiveConfigurationOrderedFiberFiniteSubschemeIsoConstantCover
          𝒜 f n r).hom ≫ D.val.subschemeι ≫
        pullback.fst g c ≫ pullback.fst f q := by
          simp only [j, Category.assoc]
          rw [hem]
    _ = _ := projectiveConfigurationOrderedFiberFiniteSubscheme_component_toProjective
      𝒜 f n r k

end AllCharacteristics
