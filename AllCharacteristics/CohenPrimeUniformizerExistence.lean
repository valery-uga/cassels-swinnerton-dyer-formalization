import AllCharacteristics.PrimeUniformizerTransfiniteGlobal
import AllCharacteristics.FinitelyGeneratedDVRLifting

/-! SOURCE ONLY / UNVERIFIED. Arbitrary positive-characteristic residue field,
complete characteristic-zero DVR, and the actual prime p as uniformizer.
No weak Cohen-ring existence theorem is used in this construction. -/
noncomputable section
namespace AllCharacteristics
open IsLocalRing
universe u

namespace CompleteDVRPrimeLiftData

def ofPositiveCharacteristic (p : ℕ) [Fact p.Prime]
    (k : Type u) [Field k] [CharP k p] : CompleteDVRPrimeLiftData p k := by
  apply Classical.choice
  let F := (⊥ : Subfield k)
  letI : Finite F := primeSubfield_finite_positive p k
  let seed : CompleteDVRPrimeLiftData p F := ofPerfect p F
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis F k
  let E := IntermediateField.adjoin F (Set.range (Subtype.val : s → k))
  letI : Algebra.IsAlgebraic E k := hs.isAlgebraic_field
  let D : CompleteDVRPrimeLiftData p E :=
    (seed.rationalFunction s).ofEquiv hs.1.aevalEquivField.toRingEquiv
  exact ⟨D.algebraicExtension⟩

theorem maximalIdeal_eq_span_prime {p : ℕ} {k : Type u} [Field k]
    (D : CompleteDVRPrimeLiftData p k) :
    letI : CommRing D.lift.R := D.lift.commRing
    letI : IsDomain D.lift.R := D.lift.domain
    letI : IsDiscreteValuationRing D.lift.R := D.lift.dvr
    maximalIdeal D.lift.R = Ideal.span {(p : D.lift.R)} := by
  letI : CommRing D.lift.R := D.lift.commRing
  letI : IsDomain D.lift.R := D.lift.domain
  letI : IsDiscreteValuationRing D.lift.R := D.lift.dvr
  exact D.prime_irreducible.maximalIdeal_eq

theorem residue_kernel_eq_span_prime {p : ℕ} {k : Type u} [Field k]
    (D : CompleteDVRPrimeLiftData p k) :
    letI : CommRing D.lift.R := D.lift.commRing
    letI : IsDomain D.lift.R := D.lift.domain
    letI : IsDiscreteValuationRing D.lift.R := D.lift.dvr
    RingHom.ker D.lift.residue = Ideal.span {(p : D.lift.R)} := by
  letI : CommRing D.lift.R := D.lift.commRing
  letI : IsDomain D.lift.R := D.lift.domain
  letI : IsDiscreteValuationRing D.lift.R := D.lift.dvr
  exact (IsLocalRing.ker_eq_maximalIdeal D.lift.residue
    D.lift.residue_surjective).trans D.maximalIdeal_eq_span_prime

def residueFieldEquiv {p : ℕ} {k : Type u} [Field k]
    (D : CompleteDVRPrimeLiftData p k) :
    letI : CommRing D.lift.R := D.lift.commRing
    letI : IsDomain D.lift.R := D.lift.domain
    letI : IsDiscreteValuationRing D.lift.R := D.lift.dvr
    ResidueField D.lift.R ≃+* k := by
  letI : CommRing D.lift.R := D.lift.commRing
  letI : IsDomain D.lift.R := D.lift.domain
  letI : IsDiscreteValuationRing D.lift.R := D.lift.dvr
  exact residueEquivOfSurjective D.lift.residue D.lift.residue_surjective

theorem residueFieldEquiv_residue {p : ℕ} {k : Type u} [Field k]
    (D : CompleteDVRPrimeLiftData p k) :
    letI : CommRing D.lift.R := D.lift.commRing
    letI : IsDomain D.lift.R := D.lift.domain
    letI : IsDiscreteValuationRing D.lift.R := D.lift.dvr
    ∀ r, D.residueFieldEquiv (residue D.lift.R r) = D.lift.residue r := by
  letI : CommRing D.lift.R := D.lift.commRing
  letI : IsDomain D.lift.R := D.lift.domain
  letI : IsDiscreteValuationRing D.lift.R := D.lift.dvr
  exact residueEquivOfSurjective_residue D.lift.residue D.lift.residue_surjective

end CompleteDVRPrimeLiftData

/-- Literal prime-uniformizer Cohen-ring assertion, retaining residue exactly k.
Completeness is for the actual maximal ideal, which equals the principal p ideal. -/
theorem exists_completeDVR_prime_uniformizer (p : ℕ) [Fact p.Prime]
    (k : Type u) [Field k] [CharP k p] :
    ∃ (R : Type u) (_ : CommRing R) (_ : IsDomain R)
      (_ : IsDiscreteValuationRing R) (_ : IsAdicComplete (maximalIdeal R) R)
      (_ : CharZero R) (b : R →+* k),
      Function.Surjective b ∧ maximalIdeal R = Ideal.span {(p : R)} ∧
      RingHom.ker b = Ideal.span {(p : R)} ∧
      ∃ e : ResidueField R ≃+* k, ∀ r, e (residue R r) = b r := by
  let D := CompleteDVRPrimeLiftData.ofPositiveCharacteristic p k
  letI : CommRing D.lift.R := D.lift.commRing
  letI : IsDomain D.lift.R := D.lift.domain
  letI : IsDiscreteValuationRing D.lift.R := D.lift.dvr
  letI : IsAdicComplete (maximalIdeal D.lift.R) D.lift.R := D.lift.complete
  letI : CharZero D.lift.R := D.lift.charZero
  exact ⟨D.lift.R, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, D.lift.residue, D.lift.residue_surjective,
    D.maximalIdeal_eq_span_prime, D.residue_kernel_eq_span_prime,
    D.residueFieldEquiv, D.residueFieldEquiv_residue⟩

end AllCharacteristics
