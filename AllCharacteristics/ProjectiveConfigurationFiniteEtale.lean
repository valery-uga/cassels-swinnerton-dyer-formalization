import AllCharacteristics.ProjectiveConfigurationEtale
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!
# The finite étale configuration cover and its actual base morphism

The free quotient is finite even without a finite-type hypothesis on the
original family: it is integral and étale. It is therefore a faithfully flat
finite cover and an effective epimorphism in the category of schemes.
-/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
universe u v
variable {A : Type u} [CommRing A] {σ : Type v} [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable {S : Scheme.{u}} [IsAffine S] (f : Proj 𝒜 ⟶ S) (n : ℕ)

/-- The actual distinct-configuration quotient is finite without an extra
finite-type assumption on the original projective family. -/
instance isFinite_projectiveConfigurationQuotientMap_of_etale :
    IsFinite (projectiveConfigurationQuotientMap 𝒜 f n) :=
  (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType _).mpr ⟨inferInstance, inferInstance⟩

/-- The actual finite étale configuration quotient is proper. -/
instance isProper_projectiveConfigurationQuotientMap_of_etale :
    IsProper (projectiveConfigurationQuotientMap 𝒜 f n) := by infer_instance

/-- The actual configuration quotient is an effective epimorphism of schemes. -/
instance effectiveEpi_projectiveConfigurationQuotientMap :
    EffectiveEpi (projectiveConfigurationQuotientMap 𝒜 f n) := by infer_instance

/-- The unordered configuration scheme retains its actual original base morphism. -/
noncomputable def projectiveConfigurationQuotientToBase :
    (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme ⟶ S :=
  (projectiveConfigurationQuotientOpen 𝒜 f n).ι ≫ projectiveOrderedTupleQuotientToBase 𝒜 f n

/-- The finite étale configuration cover is a morphism over the original base. -/
theorem projectiveConfigurationQuotientMap_toBase :
    projectiveConfigurationQuotientMap 𝒜 f n ≫ projectiveConfigurationQuotientToBase 𝒜 f n =
      (orderedFamilyConfigurationOver f n).hom := by
  let C := (orderedFamilyConfigurationOver f n).left
  let q := projectiveConfigurationQuotientMap 𝒜 f n
  let j := (projectiveConfigurationQuotientOpen 𝒜 f n).ι
  let i : C ⟶ (orderedFamilyPowerOver f n).left := (orderedFamilyConfigurationOpen f n).ι
  let qFull := projectiveOrderedTupleQuotientMap 𝒜 f n
  let b := projectiveOrderedTupleQuotientToBase 𝒜 f n
  have hp : q ≫ j = i ≫ qFull := (isPullback_projectiveConfigurationQuotientMap 𝒜 f n).w.symm
  have hb : qFull ≫ b = (orderedFamilyPowerOver f n).hom :=
    projectiveOrderedTupleQuotientMap_toBase 𝒜 f n
  change q ≫ (j ≫ b) = i ≫ (orderedFamilyPowerOver f n).hom
  exact (Category.assoc q j b).symm.trans
    ((congrArg (fun m : C ⟶ projectiveOrderedTupleQuotient 𝒜 f n ↦ m ≫ b) hp).trans
      ((Category.assoc i qFull b).trans (congrArg (fun m ↦ i ≫ m) hb)))

end AllCharacteristics
