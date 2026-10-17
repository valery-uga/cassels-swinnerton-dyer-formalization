import AllCharacteristics.LocalizedInvariantMapComparison
import AllCharacteristics.AffineLocalizationEquivalence

/-!
# Actual local isomorphisms of invariant quotients on open overlaps

For an equivariant affine open immersion, every invariant principal open
contained in its image gives an isomorphism of the localized invariant
spectra. The localized actions, their coefficient compatibility, and the
original localized ring equivalence are all constructed internally.
-/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
universe u v
variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B]
variable (G : Type v) [Group G] [Finite G]
variable [MulSemiringAction G A] [MulSemiringAction G B]
variable [SMulCommClass G R A] [SMulCommClass G R B]
variable (φ : A →+* B) (hφ : ∀ (g : G) (a : A), φ (g • a) = g • φ a)
variable [IsOpenImmersion (Spec.map (CommRingCat.ofHom φ))]
variable (t : FixedPoints.subalgebra R A G)

/-- The actual localized invariant-quotient map is an isomorphism over an invariant open
contained in the original equivariant affine open image. -/
theorem isIso_Spec_localizedInvariantMap_of_basicOpen_subset
    (ht : (PrimeSpectrum.basicOpen t.val : Set (PrimeSpectrum A)) ⊆
      Set.range (Spec.map (CommRingCat.ofHom φ))) :
    IsIso (Spec.map (CommRingCat.ofHom
      (Localization.awayMap (equivariantInvariantMap R A B G φ hφ) t))) := by
  let L : Type u := Localization.Away t.val
  let M : Type u := Localization.Away (φ t.val)
  have : IsScalarTower R A L := inferInstance
  have : IsScalarTower R B M := inferInstance
  let htB : ∀ g : G, g • φ t.val = φ t.val := fun g ↦ by rw [← hφ, t.property g]
  let := localizedGroupAction A L G t.val t.property
  let := localizedGroupAction B M G (φ t.val) htB
  let : SMulDistribClass G A L := smulDistribClass_localizedGroupAction A L G t.val t.property
  let : SMulDistribClass G B M := smulDistribClass_localizedGroupAction B M G (φ t.val) htB
  let : SMulCommClass G R L := smulCommClass_of_equivariant_algebra_tower R A L G
  let : SMulCommClass G R M := smulCommClass_of_equivariant_algebra_tower R B M G
  have hbij : Function.Bijective (IsLocalization.Away.map L M φ t.val) :=
    (awayMapRingEquiv_of_basicOpen_subset φ t.val ht).bijective
  have hinv := localizedInvariantMap_bijective_of_bijective_localizedMap R A B L M G φ hφ t hbij
  have : IsIso (CommRingCat.ofHom
      (Localization.awayMap (equivariantInvariantMap R A B G φ hφ) t)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hinv
  infer_instance

end AllCharacteristics
