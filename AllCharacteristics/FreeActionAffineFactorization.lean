import AllCharacteristics.FreeActionAffineKernelPair
import Mathlib.AlgebraicGeometry.EffectiveEpi

/-!
# Descent of invariant morphisms from an actual free affine quotient

The quotient kernel pair is the union of the original action graphs. Thus an
invariant morphism to any scheme coequalizes that kernel pair. Faithfully flat
descent then gives its unique factorization through the actual invariant spectrum.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace AllCharacteristics
universe u
variable (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
variable (G : Type) [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G R B]
variable (hfree : ∀ g : G, g ≠ 1 → actionDifferenceIdeal B G g = ⊤)
include hfree

/-- The actual free affine quotient is a regular epimorphism of schemes. -/
theorem isRegularEpi_affineInvariantQuotientMap_of_free :
    IsRegularEpi (affineInvariantQuotientMap R B G) := by
  have : Etale (affineInvariantQuotientMap R B G) :=
    etale_affineInvariantQuotientMap_of_free_action R B G hfree
  have : IsAffine (affineInvariantQuotient R B G) := by
    change IsAffine (Spec (.of (FixedPoints.subalgebra R B G)))
    infer_instance
  exact isRegularEpi_of_flat_of_surjective_of_isAffine _

/-- Invariance under the original group action gives the actual kernel-pair
compatibility, including nilpotent structure and arbitrary scheme targets. -/
theorem affineInvariant_kernelPair_condition_of_invariant
    {T : Scheme.{u}} (a : Spec (.of B) ⟶ T)
    (ha : ∀ g : G, Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom G B g)) ≫ a = a) :
    pullback.fst (affineInvariantQuotientMap R B G) (affineInvariantQuotientMap R B G) ≫ a =
      pullback.snd (affineInvariantQuotientMap R B G) (affineInvariantQuotientMap R B G) ≫ a := by
  let : Fintype G := Fintype.ofFinite G
  have : IsIso (affineInvariantKernelPairMap R B G) :=
    isIso_affineInvariantKernelPairMap_of_free R B G hfree
  apply (cancel_epi (affineInvariantKernelPairMap R B G)).mp
  apply Sigma.hom_ext
  intro g
  rw [← Category.assoc, ← Category.assoc, affineInvariantKernelPairMap_component_fst,
    Category.id_comp, ← Category.assoc, ← Category.assoc,
    affineInvariantKernelPairMap_component_snd, ha]

/-- Every invariant morphism to an arbitrary scheme factors uniquely through
the actual invariant spectrum of a free finite-group action. -/
theorem existsUnique_affineInvariantSchemeFactor_of_free
    {T : Scheme.{u}} (a : Spec (.of B) ⟶ T)
    (ha : ∀ g : G, Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom G B g)) ≫ a = a) :
    ∃! b : affineInvariantQuotient R B G ⟶ T, affineInvariantQuotientMap R B G ≫ b = a := by
  have : IsRegularEpi (affineInvariantQuotientMap R B G) :=
    isRegularEpi_affineInvariantQuotientMap_of_free R B G hfree
  obtain ⟨b, hb⟩ := IsRegularEpi.exists_of_isKernelPair
    (affineInvariantQuotientMap R B G) (IsKernelPair.of_hasPullback _) a
    (affineInvariant_kernelPair_condition_of_invariant R B G hfree a ha)
  refine ⟨b, hb, ?_⟩
  intro c hc
  exact (cancel_epi (affineInvariantQuotientMap R B G)).mp (hc.trans hb.symm)

end AllCharacteristics
