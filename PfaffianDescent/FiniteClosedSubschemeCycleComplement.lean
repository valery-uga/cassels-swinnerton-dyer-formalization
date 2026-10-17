import PfaffianDescent.IntrinsicFiniteCycle
import PfaffianDescent.ResidualCycles
import PfaffianDescent.FiniteSchemeFundamentalIso
import AllCharacteristics.ClosedImmersionCyclePushforward

/-!
# Cycle complements of finite closed subschemes

If a finite scheme `Z` is a closed subscheme of a finite scheme `W`, the
fundamental cycle of `Z`, pushed to `W`, is coefficientwise bounded by the
fundamental cycle of `W`.  Their difference is therefore an effective cycle.
Its degree is the difference of the two scheme lengths.  This gives the cycle
needed in the final Voisin construction without requiring the scheme-theoretic
residual to be Frobenius or reduced.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits AllCharacteristics

universe u

variable {K : Type u} [Field K] {Z W X : Scheme.{u}}

/-- The fundamental cycle of a finite closed subscheme is coefficientwise at
most the fundamental cycle of its ambient finite scheme. -/
theorem finiteSchemeFundamentalCycle_pushforward_le
    (i : Z ⟶ W) [IsClosedImmersion i]
    (f : W ⟶ Spec (.of K)) [IsFinite f] :
    pushforwardClosedCycle i (finiteSchemeFundamentalCycle (i ≫ f)) ≤
      finiteSchemeFundamentalCycle f := by
  classical
  letI : IsAffine W := isAffine_of_isAffineHom f
  letI := finiteSchemeCoefficientAlgebra f
  letI : Module.Finite K Γ(W, ⊤) := finiteSchemeCoefficient_finite f
  letI : IsArtinianRing Γ(W, ⊤) := isArtinian_of_tower K inferInstance
  letI : IsArtinianScheme W := finiteScheme_isArtinian f
  letI : IsArtinianScheme Z := finiteScheme_isArtinian (i ≫ f)
  rw [Finsupp.le_def]
  intro y
  by_cases hy : y ∈ Set.range (closedPointMap i)
  · obtain ⟨x, rfl⟩ := hy
    have hi : Function.Injective (closedPointMap i) := by
      intro x y hxy
      apply Subtype.ext
      exact i.isClosedEmbedding.isEmbedding.injective (congrArg Subtype.val hxy)
    unfold pushforwardClosedCycle
    rw [Finsupp.mapDomain_apply hi]
    rw [finiteSchemeFundamentalCycle_apply, finiteSchemeFundamentalCycle_apply]
    let S := W.presheaf.stalk (i x.val)
    let R := Z.presheaf.stalk x.val
    letI : Algebra S R := (i.stalkMap x.val).hom.toAlgebra
    have hsurj : Function.Surjective (algebraMap S R) := by
      exact i.stalkMap_surjective x.val
    have heq : Module.length S R = Module.length R R :=
      Module.length_eq_of_surjective hsurj
    have hle : Module.length S R ≤ Module.length S S :=
      Module.length_le_of_surjective (Algebra.linearMap S R) hsurj
    change (Module.length R R).toNat ≤ (Module.length S S).toNat
    rw [← heq]
    let q : PrimeSpectrum Γ(W, ⊤) := W.isoSpec.hom (i x.val)
    letI : IsArtinianRing (Localization.AtPrime q.asIdeal) :=
      IsArtinianRing.localization_artinian q.asIdeal.primeCompl _
    letI : IsArtinianRing ((Spec (.of Γ(W, ⊤))).presheaf.stalk q) :=
      (Spec.stalkIso (.of Γ(W, ⊤)) q).commRingCatIsoToRingEquiv.symm.isArtinianRing
    letI : IsArtinianRing S :=
      (asIso (W.isoSpec.hom.stalkMap (i x.val))).commRingCatIsoToRingEquiv.isArtinianRing
    exact ENat.toNat_le_toNat hle Module.length_ne_top
  · unfold pushforwardClosedCycle
    rw [Finsupp.mapDomain_of_notMem_range _ _ hy]
    exact Nat.zero_le _

/-- The effective cycle left after removing the fundamental cycle of a finite
closed subscheme from that of its ambient finite scheme. -/
noncomputable def finiteClosedSubschemeComplementCycle
    (i : Z ⟶ W) [IsClosedImmersion i]
    (f : W ⟶ Spec (.of K)) [IsFinite f] : EffectiveZeroCycle W :=
  finiteSchemeFundamentalCycle f -
    pushforwardClosedCycle i (finiteSchemeFundamentalCycle (i ≫ f))

/-- The complement depends only on the embedded finite subscheme, not on
its presentation.  In particular, relabeling a finite set of selected
points does not change the complementary cycle. -/
theorem finiteClosedSubschemeComplementCycle_eq_of_iso
    {Z' : Scheme.{u}}
    (i : Z ⟶ W) [IsClosedImmersion i]
    (i' : Z' ⟶ W) [IsClosedImmersion i']
    (f : W ⟶ Spec (.of K)) [IsFinite f]
    (e : Z ≅ Z') (he : e.hom ≫ i' = i) :
    finiteClosedSubschemeComplementCycle i f =
      finiteClosedSubschemeComplementCycle i' f := by
  have hfund : AllCharacteristics.pushforwardCycle e.hom
      (finiteSchemeFundamentalCycle (i ≫ f)) =
      finiteSchemeFundamentalCycle (i' ≫ f) :=
    finiteSchemeFundamentalCycle_iso e (i ≫ f) (i' ≫ f)
  have hmap (z : EffectiveZeroCycle Z) :
      pushforwardClosedCycle i z =
        pushforwardClosedCycle (e.hom ≫ i') z := by
    unfold pushforwardClosedCycle
    congr 1
    funext x
    apply Subtype.ext
    exact congrArg (fun g : Z ⟶ W => g x.val) he.symm
  have hpush : pushforwardClosedCycle i
      (finiteSchemeFundamentalCycle (i ≫ f)) =
      pushforwardClosedCycle i'
        (finiteSchemeFundamentalCycle (i' ≫ f)) := by
    rw [← AllCharacteristics.pushforwardCycle_eq_pushforwardClosedCycle i,
      ← AllCharacteristics.pushforwardCycle_eq_pushforwardClosedCycle i']
    calc
      AllCharacteristics.pushforwardCycle i
          (finiteSchemeFundamentalCycle (i ≫ f)) =
          AllCharacteristics.pushforwardCycle (e.hom ≫ i')
            (finiteSchemeFundamentalCycle (i ≫ f)) := by
              rw [AllCharacteristics.pushforwardCycle_eq_pushforwardClosedCycle i,
                AllCharacteristics.pushforwardCycle_eq_pushforwardClosedCycle (e.hom ≫ i')]
              exact hmap _
      _ = AllCharacteristics.pushforwardCycle i'
            (AllCharacteristics.pushforwardCycle e.hom
              (finiteSchemeFundamentalCycle (i ≫ f))) :=
            AllCharacteristics.pushforwardCycle_comp e.hom i' _
      _ = AllCharacteristics.pushforwardCycle i'
            (finiteSchemeFundamentalCycle (i' ≫ f)) := by rw [hfund]
  simp only [finiteClosedSubschemeComplementCycle, hpush]

/-- The ambient fundamental cycle decomposes as the complement cycle plus the
pushed-forward fundamental cycle of the closed subscheme. -/
theorem finiteClosedSubschemeComplementCycle_add
    (i : Z ⟶ W) [IsClosedImmersion i]
    (f : W ⟶ Spec (.of K)) [IsFinite f] :
    finiteSchemeFundamentalCycle f =
      finiteClosedSubschemeComplementCycle i f +
        pushforwardClosedCycle i (finiteSchemeFundamentalCycle (i ≫ f)) := by
  exact (tsub_add_cancel_of_le (finiteSchemeFundamentalCycle_pushforward_le i f)).symm

/-- The complement cycle has degree equal to the difference between the
ambient rank and the rank of the closed subscheme. -/
theorem finiteClosedSubschemeComplementCycle_degree
    (i : Z ⟶ W) [IsClosedImmersion i]
    (f : W ⟶ Spec (.of K)) [IsFinite f] :
    EffectiveZeroCycle.degree f (finiteClosedSubschemeComplementCycle i f) =
      finiteSchemeRank f - finiteSchemeRank (i ≫ f) := by
  have hdeg := congrArg (EffectiveZeroCycle.degree f)
    (finiteClosedSubschemeComplementCycle_add i f)
  rw [effectiveCycle_degree_add, degree_pushforwardClosedCycle,
    finiteSchemeFundamentalCycle_degree, finiteSchemeFundamentalCycle_degree] at hdeg
  omega

/-- Pushing a finite complement cycle through a closed immersion gives an
effective cycle of the same rank difference on the ambient scheme. -/
theorem exists_effectiveCycle_of_finite_closed_subscheme_rank_difference
    (i : Z ⟶ W) [IsClosedImmersion i]
    (c : W ⟶ X) [IsClosedImmersion c]
    (f : X ⟶ Spec (.of K)) [IsFinite (c ≫ f)]
    (m n : ℕ)
    (hW : finiteSchemeRank (c ≫ f) = m)
    (hZ : finiteSchemeRank (i ≫ c ≫ f) = n) :
    ∃ z : EffectiveZeroCycle X, EffectiveZeroCycle.degree f z = m - n := by
  let z := pushforwardClosedCycle c
    (finiteClosedSubschemeComplementCycle i (c ≫ f))
  refine ⟨z, ?_⟩
  rw [show EffectiveZeroCycle.degree f z =
      EffectiveZeroCycle.degree (c ≫ f)
        (finiteClosedSubschemeComplementCycle i (c ≫ f)) by
    exact degree_pushforwardClosedCycle c f _]
  rw [finiteClosedSubschemeComplementCycle_degree, hW]
  simpa only [Category.assoc] using congrArg (m - ·) hZ

end PfaffianDescent
