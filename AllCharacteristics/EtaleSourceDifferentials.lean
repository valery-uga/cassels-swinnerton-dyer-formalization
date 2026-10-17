import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Flat.EquationalCriterion

/-!
# Descent of the differential module along a faithfully flat étale source cover

For a finitely presented algebra with a smooth faithfully flat étale cover,
the module of differentials is projective. The remaining formal-smoothness
condition is precisely the vanishing of its first cotangent homology.
-/

open scoped TensorProduct
namespace AllCharacteristics
universe u v w
variable (R : Type u) (S : Type v) (T : Type w)
variable [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
variable [Module.FaithfullyFlat S T] [Algebra.FormallyEtale S T] [Algebra.FormallySmooth R T]
include T

/-- Flatness of the differential module descends from a smooth faithfully
flat formally étale cover of the original algebra. -/
theorem flat_kaehler_of_faithfullyFlat_formallyEtale :
    Module.Flat S (KaehlerDifferential R S) := by
  have : Module.Flat T (T ⊗[S] KaehlerDifferential R S) :=
    Module.Flat.of_linearEquiv (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R S T)
  exact Module.Flat.of_flat_tensorProduct S (KaehlerDifferential R S) T

/-- Finite presentation upgrades the descended flat differential module to
an actual projective module over the original algebra. -/
theorem projective_kaehler_of_faithfullyFlat_formallyEtale [Algebra.FinitePresentation R S] :
    Module.Projective S (KaehlerDifferential R S) := by
  have : Module.Flat S (KaehlerDifferential R S) :=
    flat_kaehler_of_faithfullyFlat_formallyEtale R S T
  exact Module.Flat.projective_of_finitePresentation

/-- With an actual smooth faithfully flat formally étale source cover, the
remaining formal-smoothness condition is exactly first cotangent homology. -/
theorem formallySmooth_iff_h1Cotangent_of_faithfullyFlat_formallyEtale
    [Algebra.FinitePresentation R S] :
    Algebra.FormallySmooth R S ↔ Subsingleton (Algebra.H1Cotangent R S) := by
  have : Module.Projective S (KaehlerDifferential R S) :=
    projective_kaehler_of_faithfullyFlat_formallyEtale R S T
  rw [Algebra.formallySmooth_iff]
  exact and_iff_right this

end AllCharacteristics
