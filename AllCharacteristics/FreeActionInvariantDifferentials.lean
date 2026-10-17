import AllCharacteristics.EtaleSourceDifferentials
import AllCharacteristics.FreeActionEtale
import AllCharacteristics.AffineInvariantFiniteType

/-! # Projectivity of the differential module of an actual free invariant quotient -/

namespace AllCharacteristics
universe u v
variable (R B : Type u) [CommRing R] [IsNoetherianRing R] [CommRing B] [Algebra R B]
variable (G : Type v) [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G R B]

/-- The actual free finite-group quotient of a smooth algebra over a
noetherian ring has a projective module of relative differentials. -/
theorem projective_kaehler_fixedSubalgebra_of_free_action [Algebra.Smooth R B]
    (hfree : ∀ g : G, g ≠ 1 → actionDifferenceIdeal B G g = ⊤) :
    Module.Projective (FixedPoints.subalgebra R B G)
      (KaehlerDifferential R (FixedPoints.subalgebra R B G)) := by
  have : Module.FaithfullyFlat (FixedPoints.subalgebra R B G) B :=
    faithfullyFlat_fixedSubalgebra_of_free_action R B G hfree
  have : Algebra.Etale (FixedPoints.subalgebra R B G) B :=
    etale_fixedSubalgebra_of_free_action R B G hfree
  have : Algebra.FinitePresentation R (FixedPoints.subalgebra R B G) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  exact projective_kaehler_of_faithfullyFlat_formallyEtale R (FixedPoints.subalgebra R B G) B

end AllCharacteristics
