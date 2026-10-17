import PfaffianDescent.FiniteSchemeAlgebra
import PfaffianDescent.SignedCyclePushforward
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits AllCharacteristics
universe u
section
variable {X Y : Scheme.{u}} [IsArtinianScheme X] [IsArtinianScheme Y]

/-- Isomorphisms carry the intrinsic fundamental zero-cycle to the intrinsic fundamental zero-cycle. -/
theorem fundamentalZeroCycle_iso (e : X ≅ Y) :
    pushforwardClosedCycle e.hom (fundamentalZeroCycle X) = fundamentalZeroCycle Y := by
  classical
  have hi : Function.Injective (closedPointMap e.hom) := by
    intro x y h
    apply Subtype.ext
    exact (Scheme.homeoOfIso e).injective (congrArg Subtype.val h)
  apply Finsupp.ext
  intro y
  let x := closedPointMap e.inv y
  have hxy : closedPointMap e.hom x = y := by
    apply Subtype.ext
    exact congrArg (fun f : Y ⟶ Y => f y.val) e.inv_hom_id
  rw [← hxy]
  change (fundamentalZeroCycle X).mapDomain (closedPointMap e.hom) (closedPointMap e.hom x) = _
  rw [Finsupp.mapDomain_apply hi]
  exact congrArg ENat.toNat (ring_length_eq_of_ringEquiv
    (asIso (e.hom.stalkMap x.val)).commRingCatIsoToRingEquiv).symm

/- An isomorphism has residue degree one, so the residue-weighted proper
pushforward agrees with the closed-immersion-style map on effective cycles. -/
theorem pushforwardCycle_iso {X Y : Scheme.{u}} (e : X ≅ Y)
    (z : EffectiveZeroCycle X) :
    AllCharacteristics.pushforwardCycle e.hom z =
      pushforwardClosedCycle e.hom z := by
  have hdeg : ∀ x : closedPoints X, e.hom.residueDegree x.1 = 1 := by
    intro x
    have hc := AllCharacteristics.residueDegree_comp e.hom e.inv x.1
    rw [Iso.hom_inv_id, Scheme.Hom.residueDegree_id] at hc
    exact Nat.eq_one_of_mul_eq_one_left hc.symm
  classical
  induction z using Finsupp.induction with
  | zero => simp [AllCharacteristics.pushforwardCycle, pushforwardClosedCycle]
  | @single_add x n z hx hn hrec =>
      have hi : AllCharacteristics.pushforwardCycle e.hom (Finsupp.single x n + z) =
          AllCharacteristics.pushforwardCycle e.hom (Finsupp.single x n) +
            AllCharacteristics.pushforwardCycle e.hom z := by
        exact Finsupp.sum_add_index' (fun x => by simp)
          (fun x n m => by simp only [add_mul, Finsupp.single_add])
      rw [hi, hrec]
      have hc : pushforwardClosedCycle e.hom (Finsupp.single x n + z) =
          pushforwardClosedCycle e.hom (Finsupp.single x n) + pushforwardClosedCycle e.hom z := by
        unfold pushforwardClosedCycle
        rw [Finsupp.mapDomain_add]
      rw [hc]
      congr 1
      rw [show AllCharacteristics.pushforwardCycle e.hom (Finsupp.single x n) =
        Finsupp.single (AllCharacteristics.universallyClosedPointMap e.hom x)
          (n * e.hom.residueDegree x.val) by
          unfold AllCharacteristics.pushforwardCycle
          exact Finsupp.sum_single_index (by simp)]
      unfold pushforwardClosedCycle
      rw [Finsupp.mapDomain_single, hdeg]
      have hpoint : AllCharacteristics.universallyClosedPointMap e.hom x =
          closedPointMap e.hom x := by
        apply Subtype.ext
        rfl
      rw [hpoint]
      simp

end
section
variable {K : Type u} [Field K] {X : Scheme.{u}}

/-- An Artinian scheme which is locally of finite type over a field is finite over that field.
This is the scheme-theoretic conversion from a zero-dimensional, proper fibre to the
finite fibre needed for a pencil of zero-cycles. -/
lemma isFinite_of_isArtinianScheme_of_locallyOfFiniteType
    (g : X ⟶ Spec (.of K)) [IsArtinianScheme X] [LocallyOfFiniteType g] : IsFinite g := by
  letI : LocallyQuasiFinite g :=
    LocallyQuasiFinite.of_finite_preimage_singleton g (fun _ ↦ Set.toFinite _)
  exact IsFinite.of_locallyQuasiFinite g

/-- A quasi-compact finite-type scheme over a field is Artinian when its topological
Krull dimension is zero. -/
lemma isArtinianScheme_of_topologicalKrullDim_le_zero_of_locallyOfFiniteType
    (g : X ⟶ Spec (.of K)) [QuasiCompact g] [LocallyOfFiniteType g]
    (hzero : topologicalKrullDim X ≤ 0) : IsArtinianScheme X := by
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian g
  letI : IsLocallyArtinian X :=
    IsLocallyArtinian.of_topologicalKrullDim_le_zero hzero
  letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace g
  exact ⟨⟩

/-- A scheme finite over a field is Artinian. -/
lemma finiteScheme_isArtinian (f : X ⟶ Spec (.of K)) [IsFinite f] : IsArtinianScheme X := by
  have : IsAffine X := isAffine_of_isAffineHom f
  letI := finiteSchemeCoefficientAlgebra f
  haveI := finiteSchemeCoefficient_finite f
  have : IsArtinianRing Γ(X, ⊤) := isArtinian_of_tower K inferInstance
  have : IsLocallyArtinian X := IsLocallyArtinian.of_isImmersion X.isoSpec.hom
  exact ⟨⟩

/-- The intrinsic finite-scheme cycle, with the length of each actual stalk as multiplicity. -/
noncomputable def finiteSchemeFundamentalCycle (f : X ⟶ Spec (.of K)) [IsFinite f] : EffectiveZeroCycle X :=
  letI := finiteScheme_isArtinian f
  fundamentalZeroCycle X

lemma finiteSchemeFundamentalCycle_apply (f : X ⟶ Spec (.of K)) [IsFinite f] (x : closedPoints X) :
    finiteSchemeFundamentalCycle f x = (Module.length (X.presheaf.stalk x.val) (X.presheaf.stalk x.val)).toNat := rfl

/-- The degree of the intrinsic finite-scheme cycle is the actual coordinate-algebra rank. -/
theorem finiteSchemeFundamentalCycle_degree (f : X ⟶ Spec (.of K)) [IsFinite f] :
    EffectiveZeroCycle.degree f (finiteSchemeFundamentalCycle f) = finiteSchemeRank f := by
  have : IsAffine X := isAffine_of_isAffineHom f
  letI := finiteSchemeCoefficientAlgebra f
  haveI := finiteSchemeCoefficient_finite f
  have : IsArtinianRing Γ(X, ⊤) := isArtinian_of_tower K inferInstance
  haveI := finiteScheme_isArtinian f
  change EffectiveZeroCycle.degree f (fundamentalZeroCycle X) = _
  rw [← fundamentalZeroCycle_iso X.isoSpec.symm, degree_pushforwardClosedCycle]
  exact (congrArg (fun q => EffectiveZeroCycle.degree q
    (fundamentalZeroCycle (Spec (.of Γ(X, ⊤))))) (finiteSchemeCoefficient_spec f).symm).trans
      (fundamentalZeroCycle_degree_affine.trans (finiteSchemeCoefficient_finrank f))

/-- Intrinsic fundamental cycles in field-valued fibers of a finite flat morphism have its fiber rank. -/
theorem finiteFiberFundamentalCycle_degree {Z B : Scheme.{u}}
    (f : Z ⟶ B) [IsFinite f] [Flat f] (b : Spec (.of K) ⟶ B) :
    EffectiveZeroCycle.degree (pullback.snd f b) (finiteSchemeFundamentalCycle (pullback.snd f b)) =
      f.finrank (b (IsLocalRing.closedPoint K)) :=
  (finiteSchemeFundamentalCycle_degree (pullback.snd f b)).trans
    ((finiteSchemeRank_eq_finrank (pullback.snd f b)).trans (Scheme.Hom.finrank_pullback_snd f b _))

end
end PfaffianDescent
