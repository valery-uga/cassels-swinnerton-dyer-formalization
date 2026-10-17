import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.RingTheory.Localization.Submodule

/-!
# Regularity under flat unramified algebra extensions

Faithful flatness lifts prime chains. For a flat unramified local map,
the maximal ideal is extended from the original ring, so its number of
generators is bounded by the original embedding dimension. These two
inequalities prove regularity ascent.
-/

open IsLocalRing
namespace AllCharacteristics
universe u v
variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]

/-- Prime-chain lifting bounds the original dimension by that of a faithfully flat algebra. -/
lemma ringKrullDim_le_of_faithfullyFlat [Module.FaithfullyFlat R S] :
    ringKrullDim R ≤ ringKrullDim S := by
  rw [ringKrullDim, Order.krullDim]
  apply iSup_le
  intro l
  obtain ⟨P, _, _⟩ := Ideal.exists_isPrime_liesOver_of_faithfullyFlat (B := S) l.last.asIdeal
  obtain ⟨L, hL, _, _⟩ := Ideal.exists_ltSeries_of_hasGoingDown l P
  rw [← hL]
  exact Order.LTSeries.length_le_krullDim L

/-- An essentially finite-type flat unramified local algebra over a regular local ring is regular. -/
theorem isRegularLocalRing_of_flat_formallyUnramified
    [IsRegularLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
    [Algebra.EssFiniteType R S] [Module.Flat R S] [Algebra.FormallyUnramified R S] :
    IsRegularLocalRing S := by
  have : IsNoetherianRing S := Algebra.EssFiniteType.isNoetherianRing R S
  have : Module.FaithfullyFlat R S := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have fg := (maximalIdeal R).fg_of_isNoetherianRing
  have hspan : Ideal.span (algebraMap R S '' (maximalIdeal R).generators) =
      maximalIdeal S := by
    rw [← Ideal.map_span, Ideal.span, Submodule.span_generators, Algebra.FormallyUnramified.map_maximalIdeal]
  have hcard : (maximalIdeal S).spanFinrank ≤ (maximalIdeal R).spanFinrank := by
    rw [← hspan, ← Submodule.FG.generators_ncard fg]
    exact (Submodule.spanFinrank_span_le_ncard_of_finite
      ((Submodule.FG.finite_generators fg).image (algebraMap R S))).trans
      (Set.ncard_image_le (Submodule.FG.finite_generators fg))
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  calc
    ((maximalIdeal S).spanFinrank : WithBot ℕ∞) ≤ (maximalIdeal R).spanFinrank := by
      exact_mod_cast hcard
    _ = ringKrullDim R := IsRegularLocalRing.spanFinrank_maximalIdeal
    _ ≤ ringKrullDim S := ringKrullDim_le_of_faithfullyFlat R S

/-- Regularity ascends along an essentially finite-type flat unramified algebra map. -/
theorem isRegularRing_of_flat_formallyUnramified
    [IsRegularRing R] [Algebra.EssFiniteType R S] [Module.Flat R S]
    [Algebra.FormallyUnramified R S] : IsRegularRing S := by
  have : IsNoetherianRing S := Algebra.EssFiniteType.isNoetherianRing R S
  apply isRegularRing_iff.mpr
  intro q hq
  let p : Ideal R := q.under R
  let := Localization.AtPrime.algebraOfLiesOver p q
  have : Algebra.EssFiniteType R (Localization.AtPrime q) := .comp R S _
  have : Algebra.EssFiniteType (Localization.AtPrime p) (Localization.AtPrime q) :=
    .of_comp R _ _
  have : Algebra.FormallyUnramified R (Localization.AtPrime q) := .comp R S _
  have : Algebra.FormallyUnramified (Localization.AtPrime p) (Localization.AtPrime q) :=
    .of_restrictScalars R _ _
  exact isRegularLocalRing_of_flat_formallyUnramified (Localization.AtPrime p)
    (Localization.AtPrime q)

end AllCharacteristics
