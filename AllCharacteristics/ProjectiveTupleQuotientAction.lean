import AllCharacteristics.ProjectiveOrderedTupleQuotient
import AllCharacteristics.AffineSchemeActionOrbits

/-!
# Permutation invariance of the actual projective tuple quotient

The whole ordered power has an explicit cover by its original common-affine
charts. The original permutation maps restrict to the constructed chart
actions, and the full projective quotient morphism is invariant under them.
-/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
universe u v
variable {A : Type u} [CommRing A] {σ : Type v} [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable {S : Scheme.{u}} [IsAffine S] (f : Proj 𝒜 ⟶ S) (n : ℕ)

/-- An explicit cover of the entire original ordered relative power by
common-affine-open charts. -/
noncomputable def projectiveOrderedCommonAffineCover : (orderedFamilyPowerOver f n).left.OpenCover where
  I₀ := (Proj 𝒜).affineOpens
  X U := (orderedFamilyCommonOpen f U.val n).toScheme
  f U := (orderedFamilyCommonOpen f U.val n).ι
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_, fun U ↦ inferInstance⟩
    intro x
    obtain ⟨U, hU⟩ := exists_commonAffineOpen_orderedProjectivePoint 𝒜 f n x
    exact ⟨U, ⟨x, hU⟩, rfl⟩

omit [IsAffine S] in
/-- Chart permutations commute with their original embeddings in the ordered power. -/
theorem commonOpenRightAction_toPower (U : (Proj 𝒜).Opens) (e : Equiv.Perm (Fin n)) :
    commonOpenRightAction f U n e ≫ (orderedFamilyCommonOpen f U n).ι =
      (orderedFamilyCommonOpen f U n).ι ≫ orderedFamilyRightAction f n e :=
  schemeRestrictedRightAction_ι (Equiv.Perm (Fin n)) (orderedFamilyRightAction f n)
    (orderedFamilyCommonOpen f U n) (orderedFamilyCommonOpen_preimage f U n) e

/-- The actual full projective quotient morphism is invariant under every original tuple permutation. -/
theorem projectiveOrderedTupleQuotientMap_invariant (e : Equiv.Perm (Fin n)) :
    orderedFamilyRightAction f n e ≫ projectiveOrderedTupleQuotientMap 𝒜 f n =
      projectiveOrderedTupleQuotientMap 𝒜 f n := by
  apply (projectiveOrderedCommonAffineCover 𝒜 f n).hom_ext
  intro U
  change (Proj 𝒜).affineOpens at U
  change (orderedFamilyCommonOpen f U.val n).ι ≫
    (orderedFamilyRightAction f n e ≫ projectiveOrderedTupleQuotientMap 𝒜 f n) =
      (orderedFamilyCommonOpen f U.val n).ι ≫ projectiveOrderedTupleQuotientMap 𝒜 f n
  rw [← Category.assoc, ← commonOpenRightAction_toPower 𝒜 f n U.val e,
    Category.assoc, projectiveOrderedTupleQuotientMap_chart 𝒜 f n U]
  have hq := commonOpenTupleQuotientMap_invariant f U.val n U.property e
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun m ↦ m ≫ commonOpenTupleQuotientGluedChart f n U) hq)

end AllCharacteristics
