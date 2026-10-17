import AllCharacteristics.DVRCompletion
import AllCharacteristics.PolynomialResidueLocalization
import AllCharacteristics.FiniteExtensionDVRLifting
import AllCharacteristics.WittLiftingBase

/-!
# Constructing complete characteristic-zero DVR lifting bases

This existence proposition records an actual complete DVR and a surjection
onto the specified field. It is proved for perfect positive-characteristic
fields, and is preserved by field isomorphisms, rational function extensions
in arbitrary variable sets, and arbitrary finite field extensions. The
construction of a rational function base does not require perfectness of
its coefficient field, only a previously constructed lifting base.
-/

open IsLocalRing
namespace AllCharacteristics
universe u

/-- Existence of an actual complete characteristic-zero DVR whose residue
field is the specified field. -/
def HasCompleteCharZeroDVRLift (k : Type u) [Field k] : Prop :=
  ∃ (R : Type u) (_ : CommRing R) (_ : IsDomain R) (_ : IsDiscreteValuationRing R)
    (_ : IsAdicComplete (maximalIdeal R) R) (_ : CharZero R) (b : R →+* k),
    Function.Surjective b

/-- Witt vectors construct a lifting base for each perfect field of positive
characteristic. -/
theorem hasCompleteCharZeroDVRLift_of_perfect_positive
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] [PerfectRing k p] :
    HasCompleteCharZeroDVRLift k := by
  obtain ⟨R, _, _, _, _, _, b, hb, _⟩ := exists_completeDVR_of_perfect_field p k
  exact ⟨R, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, b, hb⟩

/-- Transporting the prescribed residue field through an isomorphism keeps
the same complete characteristic-zero DVR. -/
theorem HasCompleteCharZeroDVRLift.of_equiv
    {k L : Type u} [Field k] [Field L] (h : HasCompleteCharZeroDVRLift k) (e : k ≃+* L) :
    HasCompleteCharZeroDVRLift L := by
  obtain ⟨R, _, _, _, _, _, b, hb⟩ := h
  exact ⟨R, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    e.toRingHom.comp b, e.surjective.comp hb⟩

/-- Polynomial localization followed by completion constructs a lifting base
for the rational function field in any set of variables. -/
theorem HasCompleteCharZeroDVRLift.rationalFunction
    {k : Type u} [Field k] (h : HasCompleteCharZeroDVRLift k) (σ : Type u) :
    HasCompleteCharZeroDVRLift (FractionRing (MvPolynomial σ k)) := by
  obtain ⟨R, _, _, _, _, _, b, hb⟩ := h
  let B := Localization.AtPrime (polynomialResiduePrime σ b)
  have : IsDiscreteValuationRing B := polynomialResidueLocalization_isDiscreteValuationRing σ b hb
  have : CharZero B := charZero_of_injective_algebraMap
    (FaithfulSMul.algebraMap_injective (MvPolynomial σ R) B)
  let c : B →+* FractionRing (MvPolynomial σ k) :=
    localizationResidueMap (MvPolynomial.map b) (polynomialResiduePrime σ b) rfl
  have hc : Function.Surjective c := polynomialResidueLocalization_surjective σ b hb
  obtain ⟨A, _, _, _, _, _, _, d, hd, _⟩ := exists_completeDVR_of_DVR_residue c hc
  exact ⟨A, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, d, hd⟩

/-- A complete characteristic-zero DVR lifting base extends through every
finite residue extension, including inseparable extensions. -/
theorem HasCompleteCharZeroDVRLift.finite_extension
    {k L : Type u} [Field k] [Field L] [Algebra k L] [Module.Finite k L]
    (h : HasCompleteCharZeroDVRLift k) : HasCompleteCharZeroDVRLift L := by
  obtain ⟨R, _, _, _, _, _, b, hb⟩ := h
  obtain ⟨A, _, _, _, _, _, _, _, _, c, hc, _⟩ :=
    exists_completeDVR_lift_of_finite_extension (L := L) b hb
  exact ⟨A, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, c, hc⟩

end AllCharacteristics
