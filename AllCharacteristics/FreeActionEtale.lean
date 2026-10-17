import AllCharacteristics.FreeActionTensorIsomorphism
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Etale.Descent
import Mathlib.RingTheory.Etale.Pi
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# Finite étale quotients of affine free finite-group actions

Finite projectivity supplies flatness. Integrality and injectivity of the
actual invariant inclusion supply faithful flatness. The proved tensor-square
isomorphism trivializes the quotient after that faithfully flat base change,
so étaleness descends. This imposes no characteristic restriction.
-/

open scoped TensorProduct
namespace AllCharacteristics
universe u v
variable (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
variable (G : Type v) [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G R B]

/-- An actual scheme-theoretically free finite-group invariant extension is faithfully flat. -/
theorem faithfullyFlat_fixedSubalgebra_of_free_action
    (hfree : ∀ g : G, g ≠ 1 → actionDifferenceIdeal B G g = ⊤) :
    Module.FaithfullyFlat (FixedPoints.subalgebra R B G) B := by
  have : Module.Projective (FixedPoints.subalgebra R B G) B :=
    (finite_projective_fixedSubalgebra_of_free_action R B G hfree).2
  exact Module.FaithfullyFlat.of_comap_surjective
    (Algebra.IsIntegral.comap_surjective (FixedPoints.subalgebra R B G) B)

/-- The actual invariant algebra of a free finite-group action has an étale quotient map. -/
theorem etale_fixedSubalgebra_of_free_action
    (hfree : ∀ g : G, g ≠ 1 → actionDifferenceIdeal B G g = ⊤) :
    Algebra.Etale (FixedPoints.subalgebra R B G) B := by
  let : Fintype G := Fintype.ofFinite G
  have : Module.FaithfullyFlat (FixedPoints.subalgebra R B G) B :=
    faithfullyFlat_fixedSubalgebra_of_free_action R B G hfree
  have : Algebra.Etale B (B ⊗[FixedPoints.subalgebra R B G] B) :=
    Algebra.Etale.of_equiv (freeActionTensorAlgEquiv R B G hfree).symm
  exact Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat B

/-- The original spectrum-to-invariant-spectrum morphism is étale under the
actual no-fixed-locus ideal condition. -/
theorem etale_affineInvariantQuotientMap_of_free_action
    (hfree : ∀ g : G, g ≠ 1 → actionDifferenceIdeal B G g = ⊤) :
    AlgebraicGeometry.Etale (affineInvariantQuotientMap R B G) := by
  have : Algebra.Etale (FixedPoints.subalgebra R B G) B :=
    etale_fixedSubalgebra_of_free_action R B G hfree
  change AlgebraicGeometry.Etale (AlgebraicGeometry.Spec.map
    (CommRingCat.ofHom (algebraMap (FixedPoints.subalgebra R B G) B)))
  exact AlgebraicGeometry.HasRingHomProperty.Spec_iff.mpr
    (RingHom.etale_algebraMap.mpr inferInstance)

end AllCharacteristics
