import AllCharacteristics.EtaleSourceHomology
import AllCharacteristics.FreeActionEtale
import AllCharacteristics.AffineInvariantFiniteType

/-! # Smoothness of the actual invariant algebra of a free finite action -/

namespace AllCharacteristics
universe u v
variable (R B : Type u) [CommRing R] [IsNoetherianRing R] [CommRing B] [Algebra R B]
variable (G : Type v) [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G R B]

/-- A smooth algebra with a free finite-group action has a smooth invariant
algebra over its original noetherian coefficient ring, in every characteristic. -/
theorem smooth_fixedSubalgebra_of_free_action [Algebra.Smooth R B]
    (hfree : ∀ g : G, g ≠ 1 → actionDifferenceIdeal B G g = ⊤) :
    Algebra.Smooth R (FixedPoints.subalgebra R B G) := by
  have : Module.FaithfullyFlat (FixedPoints.subalgebra R B G) B :=
    faithfullyFlat_fixedSubalgebra_of_free_action R B G hfree
  have : Algebra.Etale (FixedPoints.subalgebra R B G) B :=
    etale_fixedSubalgebra_of_free_action R B G hfree
  have : Algebra.FinitePresentation R (FixedPoints.subalgebra R B G) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  exact smooth_of_faithfullyFlat_etale R (FixedPoints.subalgebra R B G) B

end AllCharacteristics
