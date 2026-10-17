import PfaffianDescent.CorayAffineCurveLocalCotangent
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# Dimension and a genuine normalization defect of the actual affine curve

The actual two-equation quotient has dimension at most one: each of its two
nonzero-divisor equations drops the actual Krull dimension by at least one.
The actual full jet supplies large cotangent rank at its actual point.
In the integral-curve branch this yields a nontrivial literal normalization
quotient. No dimension or cotangent-rank certificate is supplied.

The integral branch is expressed by the primitive prime-ideal predicate on
the actual two-equation ideal. Establishing/handling the geometric integral
versus reducible branches, finite defect lengths and genus are still required.

STATUS: UNVERIFIED source draft. Root owns all compiler checks.
-/

noncomputable section
namespace PfaffianDescent.Coray

open MvPolynomial TrivSqZeroExt IsLocalRing Module
open scoped nonZeroDivisors

universe u
variable {M : Type u} [Field M]

/-- The actual affine two-equation quotient has dimension at most one,
derived from actual regular equations in a three-variable polynomial ring. -/
theorem affineCurve_ringKrullDim_le_one
    (p q : MvPolynomial (Fin 3) M) (hp : Irreducible p)
    (hq : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 3) M))) :
    ringKrullDim (affineCurveRing p q) ≤ 1 := by
  let I : Ideal (MvPolynomial (Fin 3) M) := Ideal.span {p}
  let A := MvPolynomial (Fin 3) M ⧸ I
  letI : I.IsPrime := Ideal.isPrime_span_singleton_of_prime hp.prime
  have hpreg : p ∈ (MvPolynomial (Fin 3) M)⁰ :=
    mem_nonZeroDivisors_iff_ne_zero.mpr hp.ne_zero
  have hqzero : Ideal.Quotient.mk I q ≠ 0 := by
    intro hzero
    exact hq (Ideal.Quotient.eq_zero_iff_mem.mp hzero)
  have hqreg : Ideal.Quotient.mk I q ∈ A⁰ :=
    mem_nonZeroDivisors_iff_ne_zero.mpr hqzero
  have hle : I ≤ affineCurveIdeal p q := by
    change Ideal.span {p} ≤ Ideal.span ({p, q} : Set (MvPolynomial (Fin 3) M))
    apply Ideal.span_le.mpr
    rintro r rfl
    exact Ideal.subset_span (by simp)
  let ψ : A →+* affineCurveRing p q := Ideal.Quotient.factor hle
  have hψsurj : Function.Surjective ψ := Ideal.Quotient.factor_surjective hle
  have hψq : ψ (Ideal.Quotient.mk I q) = 0 := by
    change Ideal.Quotient.factor hle (Ideal.Quotient.mk I q) = 0
    rw [Ideal.Quotient.factor_mk]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    change q ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 3) M))
    exact Ideal.subset_span (by simp)
  have hfirst : ringKrullDim A + 1 ≤ 3 := by
    have h := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hpreg
    simpa [A, I, MvPolynomial.ringKrullDim_of_isNoetherianRing,
      ringKrullDim_eq_zero_of_field, Nat.card_eq_fintype_card, Fintype.card_fin,
      zero_add, WithBot.coe_ofNat] using h
  have hsecond : ringKrullDim (affineCurveRing p q) + 1 ≤ ringKrullDim A :=
    ringKrullDim_succ_le_of_surjective ψ hψsurj hqreg hψq
  have hsum : ringKrullDim (affineCurveRing p q) + 1 + 1 ≤
      (1 : WithBot ℕ∞) + 1 + 1 := by
    calc
      ringKrullDim (affineCurveRing p q) + 1 + 1 ≤ ringKrullDim A + 1 :=
        by simpa only [add_comm] using add_le_add_right hsecond 1
      _ ≤ 3 := hfirst
      _ = (1 : WithBot ℕ∞) + 1 + 1 := by norm_num
  exact ENat.WithBot.add_le_add_one_right_iff.mp
    (ENat.WithBot.add_le_add_one_right_iff.mp hsum)

/-- Every actual point localization of this affine curve has dimension at
most one, using the actual height/local-dimension comparison. -/
theorem affineCurve_local_ringKrullDim_le_one
    (p q : MvPolynomial (Fin 3) M) (hp : Irreducible p)
    (hq : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 3) M)))
    (P : Ideal (affineCurveRing p q)) [P.IsPrime] :
    ringKrullDim (Localization.AtPrime P) ≤ 1 := by
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height P (Localization.AtPrime P)]
  exact (Ideal.height_le_ringKrullDim_of_ne_top (Ideal.IsPrime.ne_top' (I := P))).trans
    (affineCurve_ringKrullDim_le_one p q hp hq)

/-- The primitive integral-curve branch turns the proved local dimension
bound into the exact DimensionLEOne class used by normalization defect. -/
theorem affineCurve_local_dimensionLEOne_of_prime
    (p q : MvPolynomial (Fin 3) M) (hp : Irreducible p)
    (hq : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 3) M)))
    [hcurve : (affineCurveIdeal p q).IsPrime]
    (P : Ideal (affineCurveRing p q)) [P.IsPrime] :
    Ring.DimensionLEOne (Localization.AtPrime P) := by
  letI : Ring.KrullDimLE 1 (Localization.AtPrime P) :=
    Ring.krullDimLE_iff.mpr (affineCurve_local_ringKrullDim_le_one p q hp hq P)
  exact ⟨fun {J} hJzero hJprime => hJprime.isMaximal_of_ne_bot hJzero⟩

/-- At the actual full-jet point of the actual integral affine curve, the
literal normalization quotient is nontrivial. Domain, noetherianity, local
dimension and cotangent rank are derived from the actual ring and equations. -/
theorem affineCurve_actualPoint_normalizationDefect_nontrivial
    (p q : MvPolynomial (Fin 3) M) (hirr : Irreducible p)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 3) M)))
    [hcurve : (affineCurveIdeal p q).IsPrime]
    (x : Fin 3 → M) (pivot : Fin 3)
    (hp : eval x p = 0) (hpivot : eval x (pderiv pivot p) ≠ 0)
    (hq : affineNormalizedSurfaceJetMap p x pivot q = 0) :
    let φ := (affineCurvePointJet p q x pivot hp hpivot hq).toRingHom
    let hφ : Function.Surjective φ :=
      affineCurvePointJet_surjective p q x pivot hp hpivot hq
    let P := RingHom.ker (fullJetResidueMap φ)
    letI : P.IsPrime := (fullJetResidueIdeal_isMaximal φ hφ).isPrime
    Nontrivial (localNormalizationDefect (Localization.AtPrime P)
      (FractionRing (Localization.AtPrime P))) := by
  let φ := (affineCurvePointJet p q x pivot hp hpivot hq).toRingHom
  let hφ : Function.Surjective φ :=
    affineCurvePointJet_surjective p q x pivot hp hpivot hq
  let P := RingHom.ker (fullJetResidueMap φ)
  letI : P.IsPrime := (fullJetResidueIdeal_isMaximal φ hφ).isPrime
  letI : Ring.DimensionLEOne (Localization.AtPrime P) :=
    affineCurve_local_dimensionLEOne_of_prime p q hirr hnot P
  exact localNormalizationDefect_nontrivial_of_surjective_fullJet
    (FractionRing (Localization.AtPrime P))
    (fullJetAtActualPoint φ hφ) (fullJetAtActualPoint_surjective φ hφ)

end PfaffianDescent.Coray
