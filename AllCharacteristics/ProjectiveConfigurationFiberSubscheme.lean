import AllCharacteristics.ProjectiveConfigurationIncidenceFiniteEtale
import AllCharacteristics.FiniteSubschemeRank
import AllCharacteristics.FiniteSubschemeFromImmersion
import AllCharacteristics.FiniteSubschemeTransport

/-!
# Finite subschemes at projective configuration points

The universal finite étale incidence subscheme can be pulled back to a
field-valued configuration point.  This gives an actual finite-subscheme
datum on the corresponding projective fiber, retaining more information than
the associated fundamental zero-cycle.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open TopologicalSpace

namespace AllCharacteristics

universe u v

variable {A : Type u} [CommRing A] {σ : Type v} [SetLike σ A]
  [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable {K : Type u} [Field K]
variable (f : Proj 𝒜 ⟶ Spec (.of K)) [IsSeparated f]

/-- Pulling the universal unordered configuration subscheme back to a
field-valued configuration point over any extension field gives a rank-`n`
datum on the corresponding fiber of the projective family. -/
noncomputable def projectiveConfigurationFiberFiniteSubscheme
    {L : Type u} [CommRing L] (n : ℕ)
    (c : Spec (.of L) ⟶ (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme) :
    FiniteSubschemeDatum
      (pullback.snd
        (pullback.snd f (projectiveConfigurationQuotientToBase 𝒜 f n)) c) n :=
  FiniteSubschemeDatum.baseChange
    (pullback.fst (pullback.snd f (projectiveConfigurationQuotientToBase 𝒜 f n)) c)
    c
    (IsPullback.of_hasPullback
      (pullback.snd f (projectiveConfigurationQuotientToBase 𝒜 f n)) c)
    (projectiveConfigurationFiniteSubscheme 𝒜 f n)

/-- At any configuration point, the ideal-defined finite subscheme is
canonically the fiber of the universal incidence scheme. -/
noncomputable def projectiveConfigurationFiberFiniteSubschemeIsoIncidenceFiber
    {L : Type u} [CommRing L] (n : ℕ)
    (c : Spec (.of L) ⟶ (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme) :
    (projectiveConfigurationFiberFiniteSubscheme 𝒜 f n c).val.subscheme ≅
      pullback (projectiveConfigurationIncidenceToBase 𝒜 f n) c := by
  let p := pullback.snd f (projectiveConfigurationQuotientToBase 𝒜 f n)
  let D := projectiveConfigurationFiniteSubscheme 𝒜 f n
  exact (isPullback_idealSubschemeFamily D.val (pullback.fst p c)
    (pullback.snd p c) p c (IsPullback.of_hasPullback p c)).isoPullback

/-- An ordered configuration point splits the actual pulled-back finite
subscheme into its labeled field-valued components. -/
noncomputable def projectiveConfigurationOrderedFiberFiniteSubschemeIsoConstantCover
    {L : Type u} [Field L] (n : ℕ)
    (r : Spec (.of L) ⟶ (orderedFamilyConfigurationOver f n).left) :
    (∐ fun _ : ULift.{u} (Fin n) ↦ Spec (.of L)) ≅
      (projectiveConfigurationFiberFiniteSubscheme 𝒜 f n
        (r ≫ projectiveConfigurationQuotientMap 𝒜 f n)).val.subscheme :=
  projectiveConfigurationIncidenceFiberIsoConstantCover 𝒜 f n r ≪≫
    (projectiveConfigurationFiberFiniteSubschemeIsoIncidenceFiber 𝒜 f n
      (r ≫ projectiveConfigurationQuotientMap 𝒜 f n)).symm

/-- The universal configuration datum at the generic point of the unordered
configuration space.  This is the actual finite scheme over the parameter
space's function field used by Voisin's generic movement argument; no
Hilbert-scheme representability is postulated here. -/
noncomputable def projectiveConfigurationGenericFiniteSubscheme
    (n : ℕ)
    [IsIntegral (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme] :
    FiniteSubschemeDatum
      (pullback.snd
        (pullback.snd f (projectiveConfigurationQuotientToBase 𝒜 f n))
        ((projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.fromSpecStalk
          (genericPoint (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme))) n :=
  projectiveConfigurationFiberFiniteSubscheme 𝒜 f n
    ((projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.fromSpecStalk
      (genericPoint (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme))

/-- The scheme underlying the generic finite configuration is canonically
the incidence fiber over the generic point. -/
noncomputable def projectiveConfigurationGenericFiniteSubschemeIsoIncidenceFiber
    (n : ℕ)
    [IsIntegral (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme] :
    (projectiveConfigurationGenericFiniteSubscheme 𝒜 f n).val.subscheme ≅
      pullback (projectiveConfigurationIncidenceToBase 𝒜 f n)
        ((projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.fromSpecStalk
          (genericPoint (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme)) := by
  let B := (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme
  let c := B.fromSpecStalk (genericPoint B)
  let p := pullback.snd f (projectiveConfigurationQuotientToBase 𝒜 f n)
  let D := projectiveConfigurationFiniteSubscheme 𝒜 f n
  exact (isPullback_idealSubschemeFamily D.val (pullback.fst p c)
    (pullback.snd p c) p c (IsPullback.of_hasPullback p c)).isoPullback

/-- The generic finite-scheme/incidence-fiber isomorphism respects the maps
to the universal incidence subscheme. -/
@[reassoc]
lemma projectiveConfigurationGenericFiniteSubschemeIsoIncidenceFiber_hom_fst
    (n : ℕ)
    [IsIntegral (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme] :
    (projectiveConfigurationGenericFiniteSubschemeIsoIncidenceFiber 𝒜 f n).hom ≫
        pullback.fst (projectiveConfigurationIncidenceToBase 𝒜 f n)
          ((projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.fromSpecStalk
            (genericPoint (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme)) =
      idealSubschemeBaseChangeMap
        (projectiveConfigurationFiniteSubscheme 𝒜 f n).val
        (pullback.fst
          (pullback.snd f (projectiveConfigurationQuotientToBase 𝒜 f n))
          ((projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.fromSpecStalk
            (genericPoint (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme))) := by
  let B := (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme
  let c := B.fromSpecStalk (genericPoint B)
  let p := pullback.snd f (projectiveConfigurationQuotientToBase 𝒜 f n)
  let D := projectiveConfigurationFiniteSubscheme 𝒜 f n
  exact (isPullback_idealSubschemeFamily D.val (pullback.fst p c)
    (pullback.snd p c) p c (IsPullback.of_hasPullback p c)).isoPullback_hom_fst

/-- The generic finite-scheme/incidence-fiber isomorphism respects the maps
to the generic coefficient field. -/
lemma projectiveConfigurationGenericFiniteSubschemeIsoIncidenceFiber_hom_snd
    (n : ℕ)
    [IsIntegral (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme] :
    (projectiveConfigurationGenericFiniteSubschemeIsoIncidenceFiber 𝒜 f n).hom ≫
        pullback.snd (projectiveConfigurationIncidenceToBase 𝒜 f n)
          ((projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.fromSpecStalk
            (genericPoint (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme)) =
      (projectiveConfigurationGenericFiniteSubscheme 𝒜 f n).val.subschemeι ≫
        pullback.snd
          (pullback.snd f (projectiveConfigurationQuotientToBase 𝒜 f n))
          ((projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.fromSpecStalk
            (genericPoint (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme)) := by
  let B := (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme
  let c := B.fromSpecStalk (genericPoint B)
  let p := pullback.snd f (projectiveConfigurationQuotientToBase 𝒜 f n)
  let D := projectiveConfigurationFiniteSubscheme 𝒜 f n
  exact (isPullback_idealSubschemeFamily D.val (pullback.fst p c)
    (pullback.snd p c) p c (IsPullback.of_hasPullback p c)).isoPullback_hom_snd

/-- The inverse incidence-fiber identification also respects the generic
coefficient-field maps. -/
lemma projectiveConfigurationGenericFiniteSubschemeIsoIncidenceFiber_inv_toBase
    (n : ℕ)
    [IsIntegral (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme] :
    (projectiveConfigurationGenericFiniteSubschemeIsoIncidenceFiber 𝒜 f n).inv ≫
        (projectiveConfigurationGenericFiniteSubscheme 𝒜 f n).val.subschemeι ≫
        pullback.snd
          (pullback.snd f (projectiveConfigurationQuotientToBase 𝒜 f n))
          ((projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.fromSpecStalk
            (genericPoint (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme)) =
      pullback.snd (projectiveConfigurationIncidenceToBase 𝒜 f n)
        ((projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.fromSpecStalk
          (genericPoint (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme)) := by
  calc
    (projectiveConfigurationGenericFiniteSubschemeIsoIncidenceFiber 𝒜 f n).inv ≫
        ((projectiveConfigurationGenericFiniteSubscheme 𝒜 f n).val.subschemeι ≫
          pullback.snd
            (pullback.snd f (projectiveConfigurationQuotientToBase 𝒜 f n))
            ((projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.fromSpecStalk
              (genericPoint (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme))) =
      (projectiveConfigurationGenericFiniteSubschemeIsoIncidenceFiber 𝒜 f n).inv ≫
        ((projectiveConfigurationGenericFiniteSubschemeIsoIncidenceFiber 𝒜 f n).hom ≫
          pullback.snd (projectiveConfigurationIncidenceToBase 𝒜 f n)
            ((projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.fromSpecStalk
              (genericPoint (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme))) :=
        congrArg
          ((projectiveConfigurationGenericFiniteSubschemeIsoIncidenceFiber 𝒜 f n).inv ≫ ·)
          (projectiveConfigurationGenericFiniteSubschemeIsoIncidenceFiber_hom_snd
            𝒜 f n).symm
    _ = _ := by simp

/-- A factorization of an ordered field-valued configuration through the
generic point maps its incidence fiber to the actual generic finite
subscheme. -/
noncomputable def projectiveConfigurationOrderedGenericFiberToFiniteSubscheme
    (n : ℕ)
    [IsIntegral (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme]
    {L : Type u} [Field L]
    (r : Spec (.of L) ⟶ (orderedFamilyConfigurationOver f n).left)
    (b : (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.functionField →+* L)
    (hb : Spec.map (CommRingCat.ofHom b) ≫
        (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.fromSpecStalk
          (genericPoint (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme) =
      r ≫ projectiveConfigurationQuotientMap 𝒜 f n) :
    pullback (projectiveConfigurationIncidenceToBase 𝒜 f n)
        (r ≫ projectiveConfigurationQuotientMap 𝒜 f n) ⟶
      (projectiveConfigurationGenericFiniteSubscheme 𝒜 f n).val.subscheme :=
  pullback.map
      (projectiveConfigurationIncidenceToBase 𝒜 f n)
      (r ≫ projectiveConfigurationQuotientMap 𝒜 f n)
      (projectiveConfigurationIncidenceToBase 𝒜 f n)
      ((projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.fromSpecStalk
      (genericPoint (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme))
      (𝟙 _) (Spec.map (CommRingCat.ofHom b)) (𝟙 _)
      (by simp) (by exact hb.symm) ≫
    (projectiveConfigurationGenericFiniteSubschemeIsoIncidenceFiber 𝒜 f n).inv

/-- The ordered generic-fiber map respects its structure map to the
configuration function field. -/
lemma projectiveConfigurationOrderedGenericFiberToFiniteSubscheme_toBase
    (n : ℕ)
    [IsIntegral (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme]
    {L : Type u} [Field L]
    (r : Spec (.of L) ⟶ (orderedFamilyConfigurationOver f n).left)
    (b : (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.functionField →+* L)
    (hb : Spec.map (CommRingCat.ofHom b) ≫
        (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.fromSpecStalk
          (genericPoint (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme) =
      r ≫ projectiveConfigurationQuotientMap 𝒜 f n) :
    projectiveConfigurationOrderedGenericFiberToFiniteSubscheme 𝒜 f n r b hb ≫
        (projectiveConfigurationGenericFiniteSubscheme 𝒜 f n).val.subschemeι ≫
        pullback.snd
          (pullback.snd f (projectiveConfigurationQuotientToBase 𝒜 f n))
          ((projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.fromSpecStalk
            (genericPoint (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme)) =
      pullback.snd (projectiveConfigurationIncidenceToBase 𝒜 f n)
          (r ≫ projectiveConfigurationQuotientMap 𝒜 f n) ≫
        Spec.map (CommRingCat.ofHom b) := by
  unfold projectiveConfigurationOrderedGenericFiberToFiniteSubscheme
  rw [Category.assoc,
    projectiveConfigurationGenericFiniteSubschemeIsoIncidenceFiber_inv_toBase]
  exact pullback.lift_snd _ _ _

/-- Each label of an ordered generic lift gives a field-valued point of the
actual generic finite configuration scheme. -/
noncomputable def projectiveConfigurationOrderedGenericComponentPoint
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
    Spec (.of L) ⟶
      (projectiveConfigurationGenericFiniteSubscheme 𝒜 f n).val.subscheme :=
  Sigma.ι (fun _ : ULift.{u} (Fin n) ↦ Spec (.of L)) (ULift.up i) ≫
    (projectiveConfigurationIncidenceFiberIsoConstantCover 𝒜 f n r).hom ≫
    projectiveConfigurationOrderedGenericFiberToFiniteSubscheme 𝒜 f n r b hb

/-- The component points are defined over the function-field embedding
induced by the ordered generic lift. -/
lemma projectiveConfigurationOrderedGenericComponentPoint_toBase
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
        pullback.snd
          (pullback.snd f (projectiveConfigurationQuotientToBase 𝒜 f n))
          ((projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.fromSpecStalk
            (genericPoint (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme)) =
      Spec.map (CommRingCat.ofHom b) := by
  unfold projectiveConfigurationOrderedGenericComponentPoint
  simp only [Category.assoc]
  rw [projectiveConfigurationOrderedGenericFiberToFiniteSubscheme_toBase]
  rw [projectiveConfigurationIncidenceFiberIsoConstantCover_hom_snd_assoc]
  rw [constantCoverToBase, Sigma.ι_desc_assoc, Category.id_comp]

/-- The universal configuration datum remains étale after any field-valued
base change.  Thus its generic fiber is a reduced finite scheme in the
characteristic-zero applications, retaining the separability needed by the
first complete-intersection residual. -/
theorem etale_projectiveConfigurationFiberFiniteSubscheme_toBase
    {L : Type u} [CommRing L] (n : ℕ)
    (c : Spec (.of L) ⟶ (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme) :
    Etale
      ((projectiveConfigurationFiberFiniteSubscheme 𝒜 f n c).val.subschemeι ≫
        pullback.snd
          (pullback.snd f (projectiveConfigurationQuotientToBase 𝒜 f n)) c) := by
  let q := projectiveConfigurationQuotientToBase 𝒜 f n
  let p := pullback.snd f q
  let g := pullback.fst p c
  let U := projectiveConfigurationFiniteSubscheme 𝒜 f n
  let h : IsPullback g (pullback.snd p c) p c := IsPullback.of_hasPullback p c
  change Etale ((FiniteSubschemeDatum.baseChange g c h U).val.subschemeι ≫
    pullback.snd p c)
  exact MorphismProperty.of_isPullback (P := @Etale.{u})
    (isPullback_idealSubschemeFamily U.val g (pullback.snd p c) p c h)
    (by
      change Etale (projectiveConfigurationIncidenceToBase 𝒜 f n)
      infer_instance)

/-- In particular, the finite subscheme over the generic configuration point
is étale over that point's function field. -/
theorem etale_projectiveConfigurationGenericFiniteSubscheme_toBase
    (n : ℕ) [IsIntegral (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme] :
    Etale
      ((projectiveConfigurationGenericFiniteSubscheme 𝒜 f n).val.subschemeι ≫
        pullback.snd
          (pullback.snd f (projectiveConfigurationQuotientToBase 𝒜 f n))
          ((projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.fromSpecStalk
            (genericPoint (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme))) :=
  etale_projectiveConfigurationFiberFiniteSubscheme_toBase 𝒜 f n
    ((projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.fromSpecStalk
      (genericPoint (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme))

/-- The iterated pullback that carries the generic incidence datum is
canonically the usual generic fiber of the projective family. -/
noncomputable def projectiveConfigurationGenericFiberAmbientIso
    (n : ℕ) [IsIntegral (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme] :
    pullback
        (pullback.snd f (projectiveConfigurationQuotientToBase 𝒜 f n))
        ((projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.fromSpecStalk
          (genericPoint (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme)) ≅
      pullback f
        (((projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.fromSpecStalk
          (genericPoint (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme)) ≫
          projectiveConfigurationQuotientToBase 𝒜 f n) :=
  pullbackLeftPullbackSndIso f (projectiveConfigurationQuotientToBase 𝒜 f n)
    ((projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.fromSpecStalk
      (genericPoint (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme))

/-- The inverse generic-fiber isomorphism is the Cartesian square that
transports the incidence ideal to the canonical generic cubic. -/
theorem projectiveConfigurationGenericFiberAmbientIsPullback
    (n : ℕ) [IsIntegral (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme] :
    IsPullback (projectiveConfigurationGenericFiberAmbientIso 𝒜 f n).inv
      (pullback.snd f
        (((projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.fromSpecStalk
          (genericPoint (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme)) ≫
          projectiveConfigurationQuotientToBase 𝒜 f n))
      (pullback.snd
        (pullback.snd f (projectiveConfigurationQuotientToBase 𝒜 f n))
        ((projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.fromSpecStalk
          (genericPoint (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme)))
      (𝟙 _) := by
  apply IsPullback.of_horiz_isIso
  refine ⟨?_⟩
  apply (cancel_epi (projectiveConfigurationGenericFiberAmbientIso 𝒜 f n).hom).1
  simpa [projectiveConfigurationGenericFiberAmbientIso] using
    (pullbackLeftPullbackSndIso_hom_snd f
      (projectiveConfigurationQuotientToBase 𝒜 f n)
      ((projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.fromSpecStalk
        (genericPoint (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme))).symm

/-- The generic configuration now supplies a finite subscheme of the
canonical generic fiber of the cubic family. -/
noncomputable def projectiveConfigurationGenericFiberFiniteSubscheme
    (n : ℕ) [IsIntegral (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme] :
    FiniteSubschemeDatum
      (pullback.snd f
        (((projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.fromSpecStalk
          (genericPoint (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme)) ≫
          projectiveConfigurationQuotientToBase 𝒜 f n)) n :=
  FiniteSubschemeDatum.baseChange
    (projectiveConfigurationGenericFiberAmbientIso 𝒜 f n).inv (𝟙 _)
    (projectiveConfigurationGenericFiberAmbientIsPullback 𝒜 f n)
    (projectiveConfigurationGenericFiniteSubscheme 𝒜 f n)

/-- The finite scheme on the canonical generic fiber is canonically the
original generic incidence finite scheme. -/
noncomputable def projectiveConfigurationGenericFiberFiniteSubschemeIso
    (n : ℕ) [IsIntegral (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme] :
    (projectiveConfigurationGenericFiberFiniteSubscheme 𝒜 f n).val.subscheme ≅
      (projectiveConfigurationGenericFiniteSubscheme 𝒜 f n).val.subscheme :=
  FiniteSubschemeDatum.baseChangeSubschemeIso
    (projectiveConfigurationGenericFiberAmbientIso 𝒜 f n).inv (𝟙 _)
    (projectiveConfigurationGenericFiberAmbientIsPullback 𝒜 f n)
    (projectiveConfigurationGenericFiniteSubscheme 𝒜 f n)

/-- Transporting the original generic finite scheme to the canonical generic
fiber preserves its map to the original projective family. -/
@[reassoc]
theorem projectiveConfigurationGenericFiberFiniteSubschemeIso_inv_toProjective
    (n : ℕ) [IsIntegral (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme] :
    (projectiveConfigurationGenericFiberFiniteSubschemeIso 𝒜 f n).inv ≫
        (projectiveConfigurationGenericFiberFiniteSubscheme 𝒜 f n).val.subschemeι ≫
        pullback.fst f
          (((projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.fromSpecStalk
            (genericPoint (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme)) ≫
            projectiveConfigurationQuotientToBase 𝒜 f n) =
      (projectiveConfigurationGenericFiniteSubscheme 𝒜 f n).val.subschemeι ≫
        pullback.fst
          (pullback.snd f (projectiveConfigurationQuotientToBase 𝒜 f n))
          ((projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.fromSpecStalk
            (genericPoint (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme)) ≫
        pullback.fst f (projectiveConfigurationQuotientToBase 𝒜 f n) := by
  let g := (projectiveConfigurationGenericFiberAmbientIso 𝒜 f n).inv
  let h := projectiveConfigurationGenericFiberAmbientIsPullback 𝒜 f n
  let D := projectiveConfigurationGenericFiniteSubscheme 𝒜 f n
  change (FiniteSubschemeDatum.baseChangeSubschemeIso g (𝟙 _) h D).inv ≫
      (FiniteSubschemeDatum.baseChange g (𝟙 _) h D).val.subschemeι ≫
        pullback.fst f
          (((projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.fromSpecStalk
            (genericPoint (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme)) ≫
            projectiveConfigurationQuotientToBase 𝒜 f n) = _
  rw [FiniteSubschemeDatum.baseChangeSubschemeIso_inv_ι_assoc]
  dsimp only [D, g]
  have hinv : inv (projectiveConfigurationGenericFiberAmbientIso 𝒜 f n).inv =
      (projectiveConfigurationGenericFiberAmbientIso 𝒜 f n).hom := by
    exact IsIso.inv_eq_of_hom_inv_id
      (projectiveConfigurationGenericFiberAmbientIso 𝒜 f n).inv_hom_id
  rw [hinv]
  have hfst := pullbackLeftPullbackSndIso_hom_fst f
    (projectiveConfigurationQuotientToBase 𝒜 f n)
    ((projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.fromSpecStalk
      (genericPoint (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme))
  simpa only [projectiveConfigurationGenericFiberAmbientIso, Category.assoc] using
    congrArg
      (fun t ↦ (projectiveConfigurationGenericFiniteSubscheme 𝒜 f n).val.subschemeι ≫ t)
      hfst

/-- Transporting the original generic incidence scheme to the canonical
generic fiber preserves its structure morphism to the function field. -/
@[reassoc]
theorem projectiveConfigurationGenericFiberFiniteSubschemeIso_inv_toBase
    (n : ℕ) [IsIntegral (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme] :
    (projectiveConfigurationGenericFiberFiniteSubschemeIso 𝒜 f n).inv ≫
        (projectiveConfigurationGenericFiberFiniteSubscheme 𝒜 f n).val.subschemeι ≫
        pullback.snd f
          (((projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.fromSpecStalk
            (genericPoint (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme)) ≫
            projectiveConfigurationQuotientToBase 𝒜 f n) =
      (projectiveConfigurationGenericFiniteSubscheme 𝒜 f n).val.subschemeι ≫
        pullback.snd
          (pullback.snd f (projectiveConfigurationQuotientToBase 𝒜 f n))
          ((projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.fromSpecStalk
            (genericPoint (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme)) := by
  let g := (projectiveConfigurationGenericFiberAmbientIso 𝒜 f n).inv
  let h := projectiveConfigurationGenericFiberAmbientIsPullback 𝒜 f n
  let D := projectiveConfigurationGenericFiniteSubscheme 𝒜 f n
  change (FiniteSubschemeDatum.baseChangeSubschemeIso g (𝟙 _) h D).inv ≫
      (FiniteSubschemeDatum.baseChange g (𝟙 _) h D).val.subschemeι ≫
        pullback.snd f
          (((projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.fromSpecStalk
            (genericPoint (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme)) ≫
            projectiveConfigurationQuotientToBase 𝒜 f n) = _
  simpa only [Category.comp_id] using
    FiniteSubschemeDatum.baseChangeSubschemeIso_inv_toBase g (𝟙 _) h D

/-- A chosen affine presentation of the generic map to the ground field
places the generic configuration datum over an explicit coefficient field.
This is the form required to replace a cubic by its coefficient-changed
equation before invoking the complete-intersection construction. -/
noncomputable def projectiveConfigurationGenericFiniteSubschemeAtBaseMap
    (n : ℕ) [IsIntegral (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.functionField)
    (ha : Spec.map a =
      (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.fromSpecStalk
          (genericPoint (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme) ≫
        projectiveConfigurationQuotientToBase 𝒜 f n) :
    FiniteSubschemeDatum
      (pullback.snd f (Spec.map a)) n := by
  let b :=
    (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.fromSpecStalk
      (genericPoint (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme) ≫
      projectiveConfigurationQuotientToBase 𝒜 f n
  let e : pullback f (Spec.map a) ≅ pullback f b := pullback.congrHom rfl ha
  have he : e.hom ≫ pullback.snd f b = pullback.snd f (Spec.map a) := by
    dsimp [e]
    rw [pullback.congrHom_hom]
    exact pullback.lift_snd _ _ _
  exact FiniteSubschemeDatum.transportAlongAmbientIso
    (pullback.snd f (Spec.map a)) (pullback.snd f b) e he
    (projectiveConfigurationGenericFiberFiniteSubscheme 𝒜 f n)

/-- Choosing a ring-homomorphism presentation of the generic base map
changes only the ambient presentation of the generic finite scheme. -/
noncomputable def projectiveConfigurationGenericFiniteSubschemeAtBaseMapIso
    (n : ℕ) [IsIntegral (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.functionField)
    (ha : Spec.map a =
      (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.fromSpecStalk
          (genericPoint (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme) ≫
        projectiveConfigurationQuotientToBase 𝒜 f n) :
    (projectiveConfigurationGenericFiniteSubschemeAtBaseMap 𝒜 f n a ha).val.subscheme ≅
      (projectiveConfigurationGenericFiberFiniteSubscheme 𝒜 f n).val.subscheme := by
  let b :=
    (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.fromSpecStalk
      (genericPoint (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme) ≫
      projectiveConfigurationQuotientToBase 𝒜 f n
  let e : pullback f (Spec.map a) ≅ pullback f b := pullback.congrHom rfl ha
  have he : e.hom ≫ pullback.snd f b = pullback.snd f (Spec.map a) := by
    dsimp [e]
    rw [pullback.congrHom_hom]
    exact pullback.lift_snd _ _ _
  exact FiniteSubschemeDatum.transportAlongAmbientIsoSubschemeIso
    (pullback.snd f (Spec.map a)) (pullback.snd f b) e he
    (projectiveConfigurationGenericFiberFiniteSubscheme 𝒜 f n)

/-- The base-map presentation isomorphism preserves the first projection to
the original projective family. -/
@[reassoc]
theorem projectiveConfigurationGenericFiniteSubschemeAtBaseMapIso_inv_toProjective
    (n : ℕ) [IsIntegral (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.functionField)
    (ha : Spec.map a =
      (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.fromSpecStalk
          (genericPoint (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme) ≫
        projectiveConfigurationQuotientToBase 𝒜 f n) :
    (projectiveConfigurationGenericFiniteSubschemeAtBaseMapIso 𝒜 f n a ha).inv ≫
        (projectiveConfigurationGenericFiniteSubschemeAtBaseMap 𝒜 f n a ha).val.subschemeι ≫
        pullback.fst f (Spec.map a) =
      (projectiveConfigurationGenericFiberFiniteSubscheme 𝒜 f n).val.subschemeι ≫
        pullback.fst f
          (((projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.fromSpecStalk
            (genericPoint (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme)) ≫
            projectiveConfigurationQuotientToBase 𝒜 f n) := by
  let b :=
    (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.fromSpecStalk
      (genericPoint (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme) ≫
      projectiveConfigurationQuotientToBase 𝒜 f n
  let e : pullback f (Spec.map a) ≅ pullback f b := pullback.congrHom rfl ha
  have he : e.hom ≫ pullback.snd f b = pullback.snd f (Spec.map a) := by
    dsimp [e]
    rw [pullback.congrHom_hom]
    exact pullback.lift_snd _ _ _
  change (FiniteSubschemeDatum.transportAlongAmbientIsoSubschemeIso
      (pullback.snd f (Spec.map a)) (pullback.snd f b) e he
      (projectiveConfigurationGenericFiberFiniteSubscheme 𝒜 f n)).inv ≫
    (FiniteSubschemeDatum.transportAlongAmbientIso
      (pullback.snd f (Spec.map a)) (pullback.snd f b) e he
      (projectiveConfigurationGenericFiberFiniteSubscheme 𝒜 f n)).val.subschemeι ≫
      pullback.fst f (Spec.map a) = _
  rw [FiniteSubschemeDatum.transportAlongAmbientIsoSubschemeIso_inv_ι_assoc]
  have hfst : e.inv ≫ pullback.fst f (Spec.map a) = pullback.fst f b := by
    apply (cancel_epi e.hom).1
    rw [Iso.hom_inv_id_assoc]
    symm
    dsimp only [e]
    rw [pullback.congrHom_hom]
    exact pullback.lift_fst _ _ _
  rw [hfst]

/-- Changing the chosen presentation of the generic base map preserves the
finite scheme's structure morphism to the function field. -/
@[reassoc]
theorem projectiveConfigurationGenericFiniteSubschemeAtBaseMapIso_inv_toBase
    (n : ℕ) [IsIntegral (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.functionField)
    (ha : Spec.map a =
      (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.fromSpecStalk
          (genericPoint (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme) ≫
        projectiveConfigurationQuotientToBase 𝒜 f n) :
    (projectiveConfigurationGenericFiniteSubschemeAtBaseMapIso 𝒜 f n a ha).inv ≫
        (projectiveConfigurationGenericFiniteSubschemeAtBaseMap
          𝒜 f n a ha).val.subschemeι ≫
        pullback.snd f (Spec.map a) =
      (projectiveConfigurationGenericFiberFiniteSubscheme 𝒜 f n).val.subschemeι ≫
        pullback.snd f
          (((projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.fromSpecStalk
            (genericPoint (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme)) ≫
            projectiveConfigurationQuotientToBase 𝒜 f n) := by
  let b :=
    (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.fromSpecStalk
      (genericPoint (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme) ≫
      projectiveConfigurationQuotientToBase 𝒜 f n
  let e : pullback f (Spec.map a) ≅ pullback f b := pullback.congrHom rfl ha
  have he : e.hom ≫ pullback.snd f b = pullback.snd f (Spec.map a) := by
    dsimp [e]
    rw [pullback.congrHom_hom]
    exact pullback.lift_snd _ _ _
  change (FiniteSubschemeDatum.transportAlongAmbientIsoSubschemeIso
      (pullback.snd f (Spec.map a)) (pullback.snd f b) e he
      (projectiveConfigurationGenericFiberFiniteSubscheme 𝒜 f n)).inv ≫
    (FiniteSubschemeDatum.transportAlongAmbientIso
      (pullback.snd f (Spec.map a)) (pullback.snd f b) e he
      (projectiveConfigurationGenericFiberFiniteSubscheme 𝒜 f n)).val.subschemeι ≫
      pullback.snd f (Spec.map a) = _
  exact FiniteSubschemeDatum.transportAlongAmbientIsoSubschemeIso_inv_toBase
    (pullback.snd f (Spec.map a)) (pullback.snd f b) e he
    (projectiveConfigurationGenericFiberFiniteSubscheme 𝒜 f n)

/-- The explicit base-map presentation and the original generic incidence
finite scheme have canonically isomorphic underlying schemes. -/
noncomputable def projectiveConfigurationGenericFiniteSubschemeAtBaseMapIsoGeneric
    (n : ℕ) [IsIntegral (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.functionField)
    (ha : Spec.map a =
      (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.fromSpecStalk
          (genericPoint (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme) ≫
        projectiveConfigurationQuotientToBase 𝒜 f n) :
    (projectiveConfigurationGenericFiniteSubschemeAtBaseMap 𝒜 f n a ha).val.subscheme ≅
      (projectiveConfigurationGenericFiniteSubscheme 𝒜 f n).val.subscheme :=
  projectiveConfigurationGenericFiniteSubschemeAtBaseMapIso 𝒜 f n a ha ≪≫
    projectiveConfigurationGenericFiberFiniteSubschemeIso 𝒜 f n

/-- The composite identification with the original generic incidence scheme
preserves the map to the original projective family. -/
@[reassoc]
theorem projectiveConfigurationGenericFiniteSubschemeAtBaseMapIsoGeneric_inv_toProjective
    (n : ℕ) [IsIntegral (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.functionField)
    (ha : Spec.map a =
      (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.fromSpecStalk
          (genericPoint (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme) ≫
        projectiveConfigurationQuotientToBase 𝒜 f n) :
    (projectiveConfigurationGenericFiniteSubschemeAtBaseMapIsoGeneric
        𝒜 f n a ha).inv ≫
        (projectiveConfigurationGenericFiniteSubschemeAtBaseMap
          𝒜 f n a ha).val.subschemeι ≫
        pullback.fst f (Spec.map a) =
      (projectiveConfigurationGenericFiniteSubscheme 𝒜 f n).val.subschemeι ≫
        pullback.fst
          (pullback.snd f (projectiveConfigurationQuotientToBase 𝒜 f n))
          ((projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.fromSpecStalk
            (genericPoint (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme)) ≫
        pullback.fst f (projectiveConfigurationQuotientToBase 𝒜 f n) := by
  rw [projectiveConfigurationGenericFiniteSubschemeAtBaseMapIsoGeneric]
  simp only [Iso.trans_inv, Category.assoc]
  let e := projectiveConfigurationGenericFiberFiniteSubschemeIso 𝒜 f n
  have hfirst :=
    projectiveConfigurationGenericFiniteSubschemeAtBaseMapIso_inv_toProjective
      𝒜 f n a ha
  have hfirst' := congrArg (fun t ↦ e.inv ≫ t) hfirst
  calc
    _ = e.inv ≫
        (projectiveConfigurationGenericFiberFiniteSubscheme 𝒜 f n).val.subschemeι ≫
        pullback.fst f
          (((projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.fromSpecStalk
            (genericPoint (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme)) ≫
            projectiveConfigurationQuotientToBase 𝒜 f n) := by
          simpa only [e, Category.assoc] using hfirst'
    _ = _ := projectiveConfigurationGenericFiberFiniteSubschemeIso_inv_toProjective
      𝒜 f n

/-- The composite identification with the original generic incidence scheme
preserves the structure morphism to the configuration function field. -/
@[reassoc]
theorem projectiveConfigurationGenericFiniteSubschemeAtBaseMapIsoGeneric_inv_toBase
    (n : ℕ) [IsIntegral (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.functionField)
    (ha : Spec.map a =
      (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.fromSpecStalk
          (genericPoint (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme) ≫
        projectiveConfigurationQuotientToBase 𝒜 f n) :
    (projectiveConfigurationGenericFiniteSubschemeAtBaseMapIsoGeneric
        𝒜 f n a ha).inv ≫
        (projectiveConfigurationGenericFiniteSubschemeAtBaseMap
          𝒜 f n a ha).val.subschemeι ≫
        pullback.snd f (Spec.map a) =
      (projectiveConfigurationGenericFiniteSubscheme 𝒜 f n).val.subschemeι ≫
        pullback.snd
          (pullback.snd f (projectiveConfigurationQuotientToBase 𝒜 f n))
          ((projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.fromSpecStalk
            (genericPoint (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme)) := by
  rw [projectiveConfigurationGenericFiniteSubschemeAtBaseMapIsoGeneric]
  simp only [Iso.trans_inv, Category.assoc]
  let e := projectiveConfigurationGenericFiberFiniteSubschemeIso 𝒜 f n
  have hfirst :=
    projectiveConfigurationGenericFiniteSubschemeAtBaseMapIso_inv_toBase
      𝒜 f n a ha
  have hfirst' := congrArg (fun t ↦ e.inv ≫ t) hfirst
  calc
    _ = e.inv ≫
        (projectiveConfigurationGenericFiberFiniteSubscheme 𝒜 f n).val.subschemeι ≫
        pullback.snd f
          (((projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.fromSpecStalk
            (genericPoint (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme)) ≫
            projectiveConfigurationQuotientToBase 𝒜 f n) := by
          simpa only [e, Category.assoc] using hfirst'
    _ = _ := projectiveConfigurationGenericFiberFiniteSubschemeIso_inv_toBase
      𝒜 f n

/-- The generic map to the original field admits an affine presentation by
a homomorphism into the configuration function field. -/
theorem exists_projectiveConfigurationGenericBaseMap
    (n : ℕ) [IsIntegral (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme] :
    ∃ a : CommRingCat.of K ⟶ CommRingCat.of
        (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.functionField,
      Spec.map a =
        (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.fromSpecStalk
          (genericPoint (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme) ≫
        projectiveConfigurationQuotientToBase 𝒜 f n := by
  exact Spec.map_surjective _

/-- This canonical generic-fiber datum remains finite étale over the
configuration function field. -/
theorem etale_projectiveConfigurationGenericFiberFiniteSubscheme_toBase
    (n : ℕ) [IsIntegral (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme] :
    Etale
      ((projectiveConfigurationGenericFiberFiniteSubscheme 𝒜 f n).val.subschemeι ≫
        pullback.snd f
          (((projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.fromSpecStalk
            (genericPoint (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme)) ≫
            projectiveConfigurationQuotientToBase 𝒜 f n)) := by
  let e := projectiveConfigurationGenericFiberAmbientIso 𝒜 f n
  let p := pullback.snd f
    (((projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.fromSpecStalk
      (genericPoint (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme)) ≫
      projectiveConfigurationQuotientToBase 𝒜 f n)
  let q := pullback.snd
    (pullback.snd f (projectiveConfigurationQuotientToBase 𝒜 f n))
    ((projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.fromSpecStalk
      (genericPoint (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme))
  let D := projectiveConfigurationGenericFiniteSubscheme 𝒜 f n
  let h : IsPullback e.inv p q (𝟙 _) :=
    projectiveConfigurationGenericFiberAmbientIsPullback 𝒜 f n
  change Etale ((FiniteSubschemeDatum.baseChange e.inv (𝟙 _) h D).val.subschemeι ≫ p)
  exact MorphismProperty.of_isPullback (P := @Etale.{u})
    (isPullback_idealSubschemeFamily D.val e.inv p q (𝟙 _) h)
    (by
      change Etale (D.val.subschemeι ≫ q)
      exact etale_projectiveConfigurationGenericFiniteSubscheme_toBase 𝒜 f n)

/-- The explicit coefficient-field presentation of the generic configuration
datum is finite étale over the configuration function field. -/
theorem etale_projectiveConfigurationGenericFiniteSubschemeAtBaseMap_toBase
    (n : ℕ) [IsIntegral (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.functionField)
    (ha : Spec.map a =
      (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.fromSpecStalk
          (genericPoint (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme) ≫
        projectiveConfigurationQuotientToBase 𝒜 f n) :
    Etale
      ((projectiveConfigurationGenericFiniteSubschemeAtBaseMap 𝒜 f n a ha).val.subschemeι ≫
        pullback.snd f (Spec.map a)) := by
  unfold projectiveConfigurationGenericFiniteSubschemeAtBaseMap
  dsimp
  letI : Etale
      ((projectiveConfigurationGenericFiberFiniteSubscheme 𝒜 f n).val.subschemeι ≫
        pullback.snd f
          (((projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.fromSpecStalk
            (genericPoint (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme)) ≫
              projectiveConfigurationQuotientToBase 𝒜 f n)) :=
    etale_projectiveConfigurationGenericFiberFiniteSubscheme_toBase 𝒜 f n
  exact FiniteSubschemeDatum.transportAlongAmbientIso_toBase_etale _ _ _ _ _

/-- On the canonical generic cubic, the incidence datum has exactly its
prescribed rank.  In particular the `n = 16` instance is the genuine
length-sixteen starting datum for Voisin's first residual construction. -/
theorem finiteSchemeRank_projectiveConfigurationGenericFiberFiniteSubscheme
    (n : ℕ) [IsIntegral (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme] :
    let g := pullback.snd f
      (((projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.fromSpecStalk
        (genericPoint (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme)) ≫
        projectiveConfigurationQuotientToBase 𝒜 f n)
    let D := projectiveConfigurationGenericFiberFiniteSubscheme 𝒜 f n
    letI : IsFinite (D.val.subschemeι ≫ g) := D.property.1
    finiteSchemeRank (D.val.subschemeι ≫ g) = n := by
  let g := pullback.snd f
    (((projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.fromSpecStalk
      (genericPoint (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme)) ≫
      projectiveConfigurationQuotientToBase 𝒜 f n)
  let D := projectiveConfigurationGenericFiberFiniteSubscheme 𝒜 f n
  letI : IsFinite (D.val.subschemeι ≫ g) := D.property.1
  exact finiteSubschemeDatum_finiteSchemeRank g D

/-- A configuration point lying over the chosen ground field determines an
actual rank-`n` finite subscheme of the original projective scheme. -/
noncomputable def projectiveConfigurationFiniteSubschemeAt
    (n : ℕ)
    (c : Spec (.of K) ⟶ (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme)
    (hc : c ≫ projectiveConfigurationQuotientToBase 𝒜 f n = 𝟙 _) :
    FiniteSubschemeDatum f n := by
  let q := projectiveConfigurationQuotientToBase 𝒜 f n
  let g := pullback.snd f q
  let D := projectiveConfigurationFiberFiniteSubscheme 𝒜 f n c
  let e := pullbackLeftPullbackSndIso f q c
  let m := pullback.fst f (c ≫ q)
  let i := D.val.subschemeι ≫ e.hom ≫ m
  haveI : IsIso m := by
    dsimp [m]
    rw [hc]
    infer_instance
  haveI : IsClosedImmersion i := by
    dsimp [i]
    infer_instance
  have hem : e.hom ≫ m =
      pullback.fst g c ≫ pullback.fst f q := by
    dsimp [e, m, g]
    exact pullbackLeftPullbackSndIso_hom_fst f q c
  have hbase : i ≫ f = D.val.subschemeι ≫ pullback.snd g c := by
    calc
      i ≫ f = D.val.subschemeι ≫ (e.hom ≫ m) ≫ f := by
        simp only [i, Category.assoc]
      _ = D.val.subschemeι ≫ (pullback.fst g c ≫ pullback.fst f q) ≫ f := by
        rw [hem]
      _ = D.val.subschemeι ≫ pullback.fst g c ≫
          (pullback.fst f q ≫ f) := by rw [Category.assoc]
      _ = D.val.subschemeι ≫ pullback.fst g c ≫ (g ≫ q) := by
        rw [pullback.condition]
      _ = D.val.subschemeι ≫ (pullback.fst g c ≫ g) ≫ q := by
        rw [Category.assoc]
      _ = D.val.subschemeι ≫ (pullback.snd g c ≫ c) ≫ q := by
        rw [pullback.condition]
      _ = (D.val.subschemeι ≫ pullback.snd g c) ≫ (c ≫ q) := by
        rw [Category.assoc, Category.assoc]
      _ = D.val.subschemeι ≫ pullback.snd g c := by rw [hc, Category.comp_id]
  haveI : IsFinite (i ≫ f) := by
    rw [hbase]
    exact D.property.1
  haveI : Flat (i ≫ f) := by
    rw [hbase]
    exact D.property.2.1
  haveI : LocallyOfFinitePresentation (i ≫ f) := by
    rw [hbase]
    exact D.property.2.2.1
  exact finiteSubschemeDatumOfClosedImmersion i f n (fun s ↦ by
    have hs : s = IsLocalRing.closedPoint K := Subsingleton.elim _ _
    subst s
    simpa only [hbase] using D.property.2.2.2 (IsLocalRing.closedPoint K))

/-- At a field-valued ordered configuration, the actual finite subscheme
of the original projective scheme is the disjoint union of its labeled
field points. -/
noncomputable def projectiveConfigurationFiniteSubschemeAtIsoConstantCover
    (n : ℕ)
    (r : Spec (.of K) ⟶ (orderedFamilyConfigurationOver f n).left)
    (hc : (r ≫ projectiveConfigurationQuotientMap 𝒜 f n) ≫
      projectiveConfigurationQuotientToBase 𝒜 f n = 𝟙 _) :
    (∐ fun _ : ULift.{u} (Fin n) ↦ Spec (.of K)) ≅
      (projectiveConfigurationFiniteSubschemeAt 𝒜 f n
        (r ≫ projectiveConfigurationQuotientMap 𝒜 f n) hc).val.subscheme := by
  let c := r ≫ projectiveConfigurationQuotientMap 𝒜 f n
  let q := projectiveConfigurationQuotientToBase 𝒜 f n
  let g := pullback.snd f q
  let D := projectiveConfigurationFiberFiniteSubscheme 𝒜 f n c
  let e := pullbackLeftPullbackSndIso f q c
  let m := pullback.fst f (c ≫ q)
  let i := D.val.subschemeι ≫ e.hom ≫ m
  haveI : IsIso m := by
    dsimp [m]
    rw [hc]
    infer_instance
  haveI : IsClosedImmersion i := by
    dsimp [i]
    infer_instance
  change (∐ fun _ : ULift.{u} (Fin n) ↦ Spec (.of K)) ≅ i.ker.subscheme
  exact projectiveConfigurationOrderedFiberFiniteSubschemeIsoConstantCover 𝒜 f n r ≪≫
    asIso i.toImage

/-- The finite subscheme of the original projective scheme obtained from a
field-valued configuration is étale over the ground field. -/
theorem projectiveConfigurationFiniteSubschemeAt_toBase_etale
    (n : ℕ)
    (c : Spec (.of K) ⟶ (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme)
    (hc : c ≫ projectiveConfigurationQuotientToBase 𝒜 f n = 𝟙 _) :
    Etale ((projectiveConfigurationFiniteSubschemeAt 𝒜 f n c hc).val.subschemeι ≫ f) := by
  let q := projectiveConfigurationQuotientToBase 𝒜 f n
  let g := pullback.snd f q
  let D := projectiveConfigurationFiberFiniteSubscheme 𝒜 f n c
  let e := pullbackLeftPullbackSndIso f q c
  let m := pullback.fst f (c ≫ q)
  let i := D.val.subschemeι ≫ e.hom ≫ m
  haveI : IsIso m := by
    dsimp [m]
    rw [hc]
    infer_instance
  have hi : i ≫ f = D.val.subschemeι ≫ pullback.snd g c := by
    have hem : e.hom ≫ m =
        pullback.fst g c ≫ pullback.fst f q := by
      dsimp [e, m, g]
      exact pullbackLeftPullbackSndIso_hom_fst f q c
    calc
      i ≫ f = D.val.subschemeι ≫ (e.hom ≫ m) ≫ f := by
        simp only [i, Category.assoc]
      _ = D.val.subschemeι ≫ (pullback.fst g c ≫ pullback.fst f q) ≫ f := by
        rw [hem]
      _ = D.val.subschemeι ≫ pullback.fst g c ≫
          (pullback.fst f q ≫ f) := by rw [Category.assoc]
      _ = D.val.subschemeι ≫ pullback.fst g c ≫ (g ≫ q) := by
        rw [pullback.condition]
      _ = D.val.subschemeι ≫ (pullback.fst g c ≫ g) ≫ q := by
        rw [Category.assoc]
      _ = D.val.subschemeι ≫ (pullback.snd g c ≫ c) ≫ q := by
        rw [pullback.condition]
      _ = (D.val.subschemeι ≫ pullback.snd g c) ≫ (c ≫ q) := by
        rw [Category.assoc, Category.assoc]
      _ = D.val.subschemeι ≫ pullback.snd g c := by rw [hc, Category.comp_id]
  haveI : Etale (i ≫ f) := by
    rw [hi]
    exact etale_projectiveConfigurationFiberFiniteSubscheme_toBase 𝒜 f n c
  haveI : IsClosedImmersion i := by
    dsimp [i]
    infer_instance
  haveI : IsFinite (i ≫ f) := by rw [hi]; exact D.property.1
  haveI : Flat (i ≫ f) := by rw [hi]; exact D.property.2.1
  haveI : LocallyOfFinitePresentation (i ≫ f) := by rw [hi]; exact D.property.2.2.1
  change Etale ((finiteSubschemeDatumOfClosedImmersion i f n
    (fun s ↦ by
      have hs : s = IsLocalRing.closedPoint K := Subsingleton.elim _ _
      subst s
      simpa only [hi] using D.property.2.2.2 (IsLocalRing.closedPoint K))).val.subschemeι ≫ f)
  exact finiteSubschemeDatumOfClosedImmersion_toBase_etale i f n _

end AllCharacteristics
