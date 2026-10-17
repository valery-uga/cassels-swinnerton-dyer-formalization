import AllCharacteristics.ProjectiveConfigurationQuotient
import AllCharacteristics.RelativeAffineConfigurationQuotient

/-! # The original action and orbit fibers of the projective configuration quotient -/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
universe u v
variable {A : Type u} [CommRing A] {σ : Type v} [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable {S : Scheme.{u}} [IsAffine S] (f : Proj 𝒜 ⟶ S) (n : ℕ)

/-- The actual configuration quotient is invariant under the original
permutation action on ordered distinct configurations. -/
theorem projectiveConfigurationQuotientMap_invariant (g : Equiv.Perm (Fin n)) :
    configurationRightAction f n g ≫ projectiveConfigurationQuotientMap 𝒜 f n =
      projectiveConfigurationQuotientMap 𝒜 f n := by
  let C := (orderedFamilyConfigurationOver f n).left
  let q : C ⟶ (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme :=
    projectiveConfigurationQuotientMap 𝒜 f n
  let i : C ⟶ (orderedFamilyPowerOver f n).left := (orderedFamilyConfigurationOpen f n).ι
  let j := (projectiveConfigurationQuotientOpen 𝒜 f n).ι
  let qFull := projectiveOrderedTupleQuotientMap 𝒜 f n
  have hp : q ≫ j = i ≫ qFull := (isPullback_projectiveConfigurationQuotientMap 𝒜 f n).w.symm
  have hg : configurationRightAction f n g ≫ i = i ≫ orderedFamilyRightAction f n g :=
    configurationRightAction_ι f n g
  change configurationRightAction f n g ≫ q = q
  apply (cancel_mono j).mp
  rw [Category.assoc, hp, ← Category.assoc, hg, Category.assoc,
    projectiveOrderedTupleQuotientMap_invariant]

/-- The actual points of the unordered distinct-configuration quotient have
exactly the original permutation orbits as fibers. -/
theorem projectiveConfigurationQuotientMap_eq_iff_orbit
    (x y : (orderedFamilyConfigurationOver f n).left) :
    projectiveConfigurationQuotientMap 𝒜 f n x = projectiveConfigurationQuotientMap 𝒜 f n y ↔
      ∃ g : Equiv.Perm (Fin n), configurationRightAction f n g x = y := by
  let C := (orderedFamilyConfigurationOver f n).left
  let i : C ⟶ (orderedFamilyPowerOver f n).left := (orderedFamilyConfigurationOpen f n).ι
  let q : C ⟶ (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme :=
    projectiveConfigurationQuotientMap 𝒜 f n
  let j := (projectiveConfigurationQuotientOpen 𝒜 f n).ι
  let qFull := projectiveOrderedTupleQuotientMap 𝒜 f n
  have : IsOpenImmersion i := inferInstanceAs
    (IsOpenImmersion (orderedFamilyConfigurationOpen f n).ι)
  have hp (z : C) : j (q z) = qFull (i z) :=
    congrArg (fun m : C ⟶ projectiveOrderedTupleQuotient 𝒜 f n ↦ m z)
      (isPullback_projectiveConfigurationQuotientMap 𝒜 f n).w.symm
  constructor
  · intro he
    have he' : qFull (i x) = qFull (i y) :=
      (hp x).symm.trans ((congrArg j he).trans (hp y))
    obtain ⟨g, hg⟩ := (projectiveOrderedTupleQuotientMap_eq_iff_orbit 𝒜 f n (i x) (i y)).mp he'
    refine ⟨g, i.isOpenEmbedding.injective ?_⟩
    exact (congrArg (fun m : C ⟶ (orderedFamilyPowerOver f n).left ↦ m x)
      (configurationRightAction_ι f n g)).trans hg
  · rintro ⟨g, rfl⟩
    exact (congrArg (fun m : C ⟶ (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme ↦ m x)
      (projectiveConfigurationQuotientMap_invariant 𝒜 f n g)).symm

end AllCharacteristics
