import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Limits

/-! # Finite disjoint unions of closed subschemes

The coproduct of finitely many closed immersions with disjoint images is an
actual closed immersion. This applies to the disjoint sections of an ordered
configuration after their base change to the universal family.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace AllCharacteristics
universe u v

/-- A finite disjoint family of closed immersions gives a closed immersion
from its actual coproduct. -/
lemma isClosedImmersion_sigmaDesc_of_disjoint_same_universe
    {ι : Type u} [Finite ι] {Y : ι → Scheme.{u}} {X : Scheme.{u}}
    (a : ∀ i, Y i ⟶ X) [∀ i, IsClosedImmersion (a i)]
    (ha : Pairwise fun i j => Disjoint (Set.range (a i)) (Set.range (a j))) :
    IsClosedImmersion (Sigma.desc a) := by
  have hs : SurjectiveOnStalks (Sigma.desc a) :=
    IsZariskiLocalAtSource.sigmaDesc (P := @SurjectiveOnStalks.{u}) (fun _ => inferInstance)
  have hc : Topology.IsClosedEmbedding (Sigma.desc a ∘ sigmaMk Y) := by
    apply Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
    · fun_prop
    · rintro ⟨i, x⟩ ⟨j, y⟩ h
      have he : a i x = a j y := by simpa [← Scheme.Hom.comp_apply] using h
      obtain rfl : i = j := by
        by_contra hij
        exact Set.disjoint_iff_forall_ne.mp (ha hij) ⟨x, rfl⟩ ⟨y, rfl⟩ he
      exact congrArg (Sigma.mk i) ((a i).isClosedEmbedding.injective he)
    · intro C hC
      have he : (Sigma.desc a ∘ sigmaMk Y) '' C =
          ⋃ i, (a i) '' ((fun y : Y i => (⟨i, y⟩ : Σ j, Y j)) ⁻¹' C) := by
        ext x
        constructor
        · rintro ⟨⟨i, y⟩, hy, rfl⟩
          apply Set.mem_iUnion.mpr
          exact ⟨i, y, hy, by simp [← Scheme.Hom.comp_apply]⟩
        · intro hx
          obtain ⟨i, y, hy, rfl⟩ := Set.mem_iUnion.mp hx
          exact ⟨⟨i, y⟩, hy, by simp [← Scheme.Hom.comp_apply]⟩
      rw [he]
      exact isClosed_iUnion_of_finite fun i =>
        (a i).isClosedEmbedding.isClosedMap _ (hC.preimage continuous_sigmaMk)
  have hc' : Topology.IsClosedEmbedding (Sigma.desc a) := by
    convert hc.comp (sigmaMk Y).symm.isClosedEmbedding using 1
    ext x
    simp
  exact { isClosedEmbedding := hc', stalkMap_surjective := fun x => (Sigma.desc a).stalkMap_surjective x }

/-- The finite disjoint-union closed immersion criterion also allows a small
indexing type in a different universe. -/
lemma isClosedImmersion_sigmaDesc_of_disjoint
    {ι : Type v} [Finite ι] [Small.{u} ι] {Y : ι → Scheme.{u}} {X : Scheme.{u}}
    (a : ∀ i, Y i ⟶ X) [∀ i, IsClosedImmersion (a i)]
    (ha : Pairwise fun i j => Disjoint (Set.range (a i)) (Set.range (a j))) :
    IsClosedImmersion (Sigma.desc a) := by
  obtain ⟨κ, ⟨e⟩⟩ := Small.equiv_small (α := ι)
  have : Finite κ := Finite.of_equiv ι e
  let a' : ∀ i : κ, Y (e.symm i) ⟶ X := fun i => a (e.symm i)
  have hclosed : IsClosedImmersion (Sigma.desc a') :=
    isClosedImmersion_sigmaDesc_of_disjoint_same_universe a'
      (fun i j hij => ha (fun he => hij (e.symm.injective he)))
  have he : (Sigma.reindex e.symm Y).inv ≫ Sigma.desc a' = Sigma.desc a := by
    apply Sigma.hom_ext
    intro i
    obtain ⟨j, rfl⟩ := e.symm.surjective i
    simp [a']
  rw [← he]
  exact @IsClosedImmersion.comp _ _ _ (Sigma.reindex e.symm Y).inv
    (Sigma.desc a') inferInstance hclosed

end AllCharacteristics
