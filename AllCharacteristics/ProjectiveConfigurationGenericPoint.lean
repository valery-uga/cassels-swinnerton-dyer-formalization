import AllCharacteristics.ProjectiveConfigurationIncidenceFiniteEtale
import AllCharacteristics.ProjectiveConfigurationIntegrality
import AllCharacteristics.ProjectiveConfigurationFiberSubscheme
import AllCharacteristics.FiniteSubschemeTransport
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.RingTheory.Unramified.Field

/-!
# The generic unordered configuration is one closed point

Choosing one label on the ordered configuration gives a surjection onto the
unordered incidence scheme: permutations move any mark to the chosen label.
Thus an irreducible ordered configuration has irreducible incidence. This
is the geometric transitivity input in Voisin's fixed-component argument.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open TopologicalSpace

namespace AllCharacteristics

universe u v

section Incidence

variable {A : Type u} [CommRing A] {σ : Type v} [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable {S : Scheme.{u}} [IsAffine S] (f : Proj 𝒜 ⟶ S) (n : ℕ)

/-- Forget all labels except one, retaining its point in the unordered
incidence scheme. -/
noncomputable def projectiveConfigurationSingleMarkToIncidence (i : Fin n) :
    (orderedFamilyConfigurationOver f n).left ⟶ projectiveConfigurationIncidence 𝒜 f n :=
  Sigma.ι (fun _ : ULift.{u} (Fin n) => (orderedFamilyConfigurationOver f n).left) ⟨i⟩ ≫
    projectiveConfigurationMarkedToIncidence 𝒜 f n

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
theorem projectiveConfigurationSingleMarkToIncidence_ι (i : Fin n) :
    projectiveConfigurationSingleMarkToIncidence 𝒜 f n i ≫
      projectiveConfigurationIncidenceι 𝒜 f n =
    orderedConfigurationSection f n i ≫ projectiveConfigurationFamilyMap 𝒜 f n := by
  rw [projectiveConfigurationSingleMarkToIncidence, Category.assoc,
    projectiveConfigurationMarkedToIncidence_ι]
  change _ ≫ (orderedConfigurationUnionMap f n ≫ _) = _
  rw [← Category.assoc]
  exact congrArg (fun h => h ≫ projectiveConfigurationFamilyMap 𝒜 f n)
    (Sigma.ι_desc _ (ULift.up i))

/-- Relabeling changes the chosen mark and leaves the resulting unordered
incidence point unchanged. -/
@[reassoc]
theorem projectiveConfigurationSingleMarkToIncidence_action
    (g : Equiv.Perm (Fin n)) (i : Fin n) :
    configurationRightAction f n g ≫ projectiveConfigurationSingleMarkToIncidence 𝒜 f n i =
      projectiveConfigurationSingleMarkToIncidence 𝒜 f n (g i) := by
  apply (cancel_mono (projectiveConfigurationIncidenceι 𝒜 f n)).mp
  rw [Category.assoc, projectiveConfigurationSingleMarkToIncidence_ι,
    projectiveConfigurationSingleMarkToIncidence_ι]
  have h := orderedConfigurationSection_rightAction f n g (g i)
  simp only [Equiv.symm_apply_apply] at h
  rw [← Category.assoc, ← h, Category.assoc, projectiveConfigurationFamilyMap_invariant]

/-- A single chosen label already surjects onto the entire incidence, because
the permutation action is transitive on the labels. -/
instance surjective_projectiveConfigurationSingleMarkToIncidence (i : Fin n) :
    Surjective (projectiveConfigurationSingleMarkToIncidence 𝒜 f n i) := by
  constructor
  intro y
  obtain ⟨z, rfl⟩ := (projectiveConfigurationMarkedToIncidence 𝒜 f n).surjective y
  obtain ⟨⟨j, x⟩, rfl⟩ :=
    (sigmaMk (fun _ : ULift.{u} (Fin n) => (orderedFamilyConfigurationOver f n).left)).surjective z
  refine ⟨configurationRightAction f n (Equiv.swap i j.down) x, ?_⟩
  rw [← Scheme.Hom.comp_apply, projectiveConfigurationSingleMarkToIncidence_action,
    Equiv.swap_apply_left, sigmaMk_mk]
  rfl

/-- Incidence over unordered configurations is irreducible whenever the
ordered configuration is irreducible and there is a label to mark. -/
theorem irreducibleSpace_projectiveConfigurationIncidence
    [IrreducibleSpace (orderedFamilyConfigurationOver f n).left] (i : Fin n) :
    IrreducibleSpace (projectiveConfigurationIncidence 𝒜 f n) :=
  (projectiveConfigurationSingleMarkToIncidence 𝒜 f n i).surjective.irreducibleSpace
    (projectiveConfigurationSingleMarkToIncidence 𝒜 f n i).continuous

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
theorem projectiveConfigurationSingleMarkToIncidence_toBase (i : Fin n) :
    projectiveConfigurationSingleMarkToIncidence 𝒜 f n i ≫
      projectiveConfigurationIncidenceToBase 𝒜 f n =
        projectiveConfigurationQuotientMap 𝒜 f n := by
  rw [projectiveConfigurationIncidenceToBase, ← Category.assoc,
    projectiveConfigurationSingleMarkToIncidence_ι, Category.assoc,
    projectiveConfigurationFamilyMap_toBase, ← Category.assoc,
    orderedConfigurationSection_snd, Category.id_comp]

/-- The incidence has a point above every nonempty configuration. -/
theorem surjective_projectiveConfigurationIncidenceToBase (i : Fin n) :
    Surjective (projectiveConfigurationIncidenceToBase 𝒜 f n) := by
  constructor
  intro y
  obtain ⟨x, rfl⟩ := (projectiveConfigurationQuotientMap 𝒜 f n).surjective y
  refine ⟨projectiveConfigurationSingleMarkToIncidence 𝒜 f n i x, ?_⟩
  rw [← Scheme.Hom.comp_apply, projectiveConfigurationSingleMarkToIncidence_toBase]

end Incidence

section GenericFiber

/-- A surjective morphism between irreducible schemes preserves their
generic points. -/
theorem genericPoint_map_of_surjective
    {X Y : Scheme.{u}} [IrreducibleSpace X] [IrreducibleSpace Y]
    (f : X ⟶ Y) [Surjective f] : f (genericPoint X) = genericPoint Y := by
  apply IsGenericPoint.eq _ (genericPoint_spec Y)
  simpa only [Set.image_univ, Set.range_eq_univ.mpr f.surjective, closure_univ]
    using (genericPoint_spec X).image f.continuous

/-- The generic fiber of a finite surjective morphism with irreducible
source has exactly one point. Specialization from the generic source point
and discreteness of finite fibers supply uniqueness. -/
theorem genericPullback_nonempty_subsingleton_of_irreducible
    {X Y : Scheme.{u}} [IrreducibleSpace X] [IsIntegral Y]
    (f : X ⟶ Y) [IsFinite f] [Surjective f] :
    Nonempty (pullback f (Y.fromSpecStalk (genericPoint Y)) : Scheme.{u}) ∧
      Subsingleton (pullback f (Y.fromSpecStalk (genericPoint Y)) : Scheme.{u}) := by
  let c := Y.fromSpecStalk (genericPoint Y)
  let T := pullback f c
  let i : T ⟶ X := pullback.fst f c
  let : IsArtinianScheme T := PfaffianDescent.finiteScheme_isArtinian (pullback.snd f c)
  have hrange : Set.range c = {genericPoint Y} := by
    rw [Scheme.range_fromSpecStalk]
    ext y
    change (y ⤳ genericPoint Y) ↔ y = genericPoint Y
    exact ⟨fun h => (h.antisymm ((genericPoint_spec Y).specializes (Set.mem_univ y))).eq,
      fun h => specializes_of_eq h⟩
  have hirange : Set.range i = f ⁻¹' {genericPoint Y} := by
    change Set.range (pullback.fst f c) = _
    rw [Scheme.Pullback.range_fst, hrange]
  obtain ⟨z, hz⟩ : genericPoint X ∈ Set.range i := by
    rw [hirange]
    exact genericPoint_map_of_surjective f
  have hzw (w : T) : z = w := by
    apply specializes_iff_eq.mp
    apply i.isEmbedding.isInducing.specializes_iff.mp
    rw [hz]
    exact (genericPoint_spec X).specializes (Set.mem_univ _)
  exact ⟨⟨z⟩, ⟨fun a b => (hzw a).symm.trans (hzw b)⟩⟩

/-- A nonempty finite étale scheme with one topological point has a field
as its coordinate algebra. This does not assume the field is perfect. -/
theorem finiteEtaleScheme_isField_of_subsingleton
    {K : Type u} [Field K] {X : Scheme.{u}} [Nonempty X] [Subsingleton X]
    (f : X ⟶ Spec (.of K)) [IsFinite f] [Etale f] : IsField Γ(X, ⊤) := by
  let : IsAffine X := isAffine_of_isAffineHom f
  let := PfaffianDescent.finiteSchemeCoefficientAlgebra f
  have hspec : Etale (Spec.map (CommRingCat.ofHom (algebraMap K Γ(X, ⊤)))) := by
    rw [PfaffianDescent.finiteSchemeCoefficient_spec f]
    infer_instance
  have hring : (algebraMap K Γ(X, ⊤)).Etale :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mp hspec
  have : Algebra.Etale K Γ(X, ⊤) := RingHom.etale_algebraMap.mp hring
  have : _root_.IsReduced Γ(X, ⊤) :=
    Algebra.FormallyUnramified.isReduced_of_field K Γ(X, ⊤)
  have : IsReduced X := isReduced_of_isAffine_isReduced X
  have : IrreducibleSpace X :=
    { toNonempty := inferInstance, toPreirreducibleSpace := inferInstance }
  have : IsIntegral X := isIntegral_of_irreducibleSpace_of_isReduced X
  have : Module.Finite K Γ(X, ⊤) := PfaffianDescent.finiteSchemeCoefficient_finite f
  have : IsArtinianRing Γ(X, ⊤) := IsArtinianRing.of_finite K _
  exact IsArtinianRing.isField_of_isDomain _

end GenericFiber

/-- A closed subscheme either misses a reduced one-point scheme or contains
it scheme-theoretically. The factorization is over the original field;
no choice of a geometric component or invariance premise is needed. -/
theorem isEmpty_pullback_or_factors_of_reduced_subsingleton
    {C D X : Scheme.{u}} [Subsingleton D] [IsReduced D]
    (i : C ⟶ X) [IsClosedImmersion i] (j : D ⟶ X) :
    IsEmpty (pullback i j : Scheme.{u}) ∨ ∃ h : D ⟶ C, h ≫ i = j := by
  classical
  by_cases h : Nonempty (pullback i j : Scheme.{u})
  · have : Surjective (pullback.snd i j) :=
      ⟨fun y => ⟨Classical.choice h, Subsingleton.elim _ y⟩⟩
    have : IsIso (pullback.snd i j) :=
      isIso_of_isClosedImmersion_of_surjective (pullback.snd i j)
    refine Or.inr ⟨inv (pullback.snd i j) ≫ pullback.fst i j, ?_⟩
    rw [Category.assoc, pullback.condition, ← Category.assoc,
      IsIso.inv_hom_id, Category.id_comp]
  · exact Or.inl (not_nonempty_iff.mp h)

section GenericConfiguration

variable {A : Type u} [CommRing A] {σ : Type v} [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable {K : Type u} [Field K] (f : Proj 𝒜 ⟶ Spec (.of K)) [IsSeparated f]
variable (n : ℕ) [IsIntegral (orderedFamilyConfigurationOver f n).left]

/-- The actual generic finite subscheme over unordered configurations is
nonempty and consists of one topological point. -/
theorem projectiveConfigurationGenericFiniteSubscheme_nonempty_subsingleton (i : Fin n) :
    Nonempty (projectiveConfigurationGenericFiniteSubscheme 𝒜 f n).val.subscheme ∧
      Subsingleton (projectiveConfigurationGenericFiniteSubscheme 𝒜 f n).val.subscheme := by
  let B := (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme
  let c := B.fromSpecStalk (genericPoint B)
  let p := pullback.snd f (projectiveConfigurationQuotientToBase 𝒜 f n)
  let D := projectiveConfigurationFiniteSubscheme 𝒜 f n
  have : IrreducibleSpace (projectiveConfigurationIncidence 𝒜 f n) :=
    irreducibleSpace_projectiveConfigurationIncidence 𝒜 f n i
  have : Surjective (projectiveConfigurationIncidenceToBase 𝒜 f n) :=
    surjective_projectiveConfigurationIncidenceToBase 𝒜 f n i
  have h := genericPullback_nonempty_subsingleton_of_irreducible
    (projectiveConfigurationIncidenceToBase 𝒜 f n)
  let e : (projectiveConfigurationGenericFiniteSubscheme 𝒜 f n).val.subscheme ≅
      pullback (projectiveConfigurationIncidenceToBase 𝒜 f n) c :=
    (isPullback_idealSubschemeFamily D.val (pullback.fst p c) (pullback.snd p c)
      p c (IsPullback.of_hasPullback p c)).isoPullback
  obtain ⟨z⟩ := h.1
  refine ⟨⟨e.inv z⟩, ⟨fun a b => ?_⟩⟩
  exact e.hom.homeomorph.injective (h.2.elim (e.hom a) (e.hom b))

/-- The generic rank-`n` finite étale configuration is the spectrum of a
field. This is the arithmetic form of transitivity on its geometric points. -/
theorem projectiveConfigurationGenericFiniteSubscheme_isField (i : Fin n) :
    IsField Γ((projectiveConfigurationGenericFiniteSubscheme 𝒜 f n).val.subscheme, ⊤) := by
  have h := projectiveConfigurationGenericFiniteSubscheme_nonempty_subsingleton 𝒜 f n i
  let D := projectiveConfigurationGenericFiniteSubscheme 𝒜 f n
  let B := (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme
  let p := pullback.snd (pullback.snd f (projectiveConfigurationQuotientToBase 𝒜 f n))
    (B.fromSpecStalk (genericPoint B))
  have : Nonempty D.val.subscheme := h.1
  have : Subsingleton D.val.subscheme := h.2
  have : IsFinite (D.val.subschemeι ≫ p) := D.property.1
  have : Etale (D.val.subschemeι ≫ p) :=
    etale_projectiveConfigurationGenericFiniteSubscheme_toBase 𝒜 f n
  exact finiteEtaleScheme_isField_of_subsingleton (D.val.subschemeι ≫ p)

/-- The one-point property survives the canonical generic-fiber
presentation of the projective family. -/
theorem projectiveConfigurationGenericFiberFiniteSubscheme_nonempty_subsingleton
    (i : Fin n) :
    Nonempty (projectiveConfigurationGenericFiberFiniteSubscheme 𝒜 f n).val.subscheme ∧
      Subsingleton (projectiveConfigurationGenericFiberFiniteSubscheme 𝒜 f n).val.subscheme := by
  exact nonempty_subsingleton_of_schemeIso
    (FiniteSubschemeDatum.baseChangeSubschemeIso
      (projectiveConfigurationGenericFiberAmbientIso 𝒜 f n).inv (𝟙 _)
      (projectiveConfigurationGenericFiberAmbientIsPullback 𝒜 f n)
      (projectiveConfigurationGenericFiniteSubscheme 𝒜 f n))
    (projectiveConfigurationGenericFiniteSubscheme_nonempty_subsingleton 𝒜 f n i)

/-- Choosing the coefficient homomorphism for the generic fiber preserves
the one-point property of the generic configuration. -/
theorem projectiveConfigurationGenericFiniteSubschemeAtBaseMap_nonempty_subsingleton
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.functionField)
    (ha : Spec.map a =
      (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.fromSpecStalk
          (genericPoint (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme) ≫
        projectiveConfigurationQuotientToBase 𝒜 f n) (i : Fin n) :
    Nonempty (projectiveConfigurationGenericFiniteSubschemeAtBaseMap 𝒜 f n a ha).val.subscheme ∧
      Subsingleton
        (projectiveConfigurationGenericFiniteSubschemeAtBaseMap 𝒜 f n a ha).val.subscheme := by
  unfold projectiveConfigurationGenericFiniteSubschemeAtBaseMap
  dsimp only
  apply nonempty_subsingleton_of_schemeIso
    (FiniteSubschemeDatum.transportAlongAmbientIsoSubschemeIso _ _ _ _ _)
  exact projectiveConfigurationGenericFiberFiniteSubscheme_nonempty_subsingleton 𝒜 f n i

end GenericConfiguration

end AllCharacteristics
