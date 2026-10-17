import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.LinearAlgebra.Span.Basic

/- SOURCE ONLY / UNVERIFIED. The localization transition is determined by
its action on actual differentials from the original ring. -/
noncomputable section
namespace PfaffianDescent
open KaehlerDifferential
universe u
variable {k R T N : Type u} [CommRing k] [CommRing R] [CommRing T]
  [Algebra k R] [Algebra k T] [Algebra R T] [IsScalarTower k R T]
  [AddCommGroup N] [Module T N]

lemma localizedKaehler_linearMap_ext (M : Submonoid R) [IsLocalization M T]
    (f g : KaehlerDifferential k T →ₗ[T] N)
    (h : ∀ r : R, f (D k T (algebraMap R T r)) =
      g (D k T (algebraMap R T r))) : f = g := by
  apply LinearMap.ext_on_range
    (span_range_map_derivation_of_isLocalization k R T M)
  intro r
  simpa only [Function.comp_apply, map_D] using h r

end PfaffianDescent
