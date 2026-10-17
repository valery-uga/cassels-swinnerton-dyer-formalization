import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Dimension of closed points on affine hypersurfaces

Maximal ideals of polynomial rings over a field have height equal to the
number of variables. Quotienting the ambient local ring at a closed point
by a nonzero equation lowers that dimension by one.
-/

open MvPolynomial
namespace AllCharacteristics
universe u v
variable {K : Type u} [Field K]
set_option linter.style.haveILetI false in
/-- Every maximal ideal of a polynomial ring over a field has full height. -/
theorem maximalIdeal_height_mvPolynomial {ι : Type v} [Finite ι]
    (m : Ideal (MvPolynomial ι K)) [m.IsMaximal] : m.height = Nat.card ι := by
  classical
  induction ι using Finite.induction_empty_option with
  | of_equiv e H =>
    let φ := (renameEquiv K e).toRingEquiv
    let n := m.comap φ
    haveI : n.IsMaximal := Ideal.comap_isMaximal_of_surjective φ φ.surjective
    have hn := H n
    rw [RingEquiv.height_comap] at hn
    simpa only [Nat.card_congr e] using hn
  | h_empty =>
    let φ := isEmptyRingEquiv K PEmpty.{v + 1}
    let n := m.comap φ.symm
    haveI : n.IsMaximal := Ideal.comap_isMaximal_of_surjective φ.symm φ.symm.surjective
    have hn : n = ⊥ := Ideal.eq_bot_of_prime n
    have hh : n.height = 0 := by rw [hn, Ideal.height_bot]
    rw [RingEquiv.height_comap] at hh
    simpa using hh
  | @h_option α instα IH =>
    let φ := (optionEquivLeft K α).toRingEquiv
    let n := m.comap φ.symm
    haveI : n.IsMaximal := Ideal.comap_isMaximal_of_surjective φ.symm φ.symm.surjective
    haveI : (n.under (MvPolynomial α K)).IsMaximal :=
      Polynomial.isMaximal_comap_C_of_isJacobsonRing n
    have hn := Polynomial.height_eq_height_add_one (n.under (MvPolynomial α K)) n
    rw [IH] at hn
    rw [RingEquiv.height_comap] at hn
    simpa only [Nat.card_eq_fintype_card, Fintype.card_option, Nat.cast_add,
      Nat.cast_one] using hn

/-- Closed points of affine space have the expected local dimension. -/
theorem ringKrullDim_localizationAtMaximal_mvPolynomial {ι : Type v} [Finite ι]
    (m : Ideal (MvPolynomial ι K)) [m.IsMaximal] :
    ringKrullDim (Localization.AtPrime m) = Nat.card ι := by
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height m]
  exact_mod_cast maximalIdeal_height_mvPolynomial m

open scoped nonZeroDivisors in
/-- A nonzero hypersurface in affine three-space has local dimension two
at a closed point, expressed in the ambient local ring. -/
theorem ringKrullDim_quotient_localized_polynomial_equation_eq_two
    (m : Ideal (MvPolynomial (Fin 3) K)) [m.IsMaximal]
    (f : MvPolynomial (Fin 3) K) (hf : f ≠ 0) (hfm : f ∈ m) :
    ringKrullDim (Localization.AtPrime m ⧸
      Ideal.span {algebraMap (MvPolynomial (Fin 3) K) (Localization.AtPrime m) f}) = 2 := by
  let R := Localization.AtPrime m
  let x : R := algebraMap (MvPolynomial (Fin 3) K) R f
  have hx : x ∈ R⁰ := by
    apply mem_nonZeroDivisors_iff_ne_zero.mpr
    simpa only [map_zero] using (IsLocalization.injective R m.primeCompl_le_nonZeroDivisors).ne hf
  have hxm : x ∈ IsLocalRing.maximalIdeal R := by
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff R m f).mpr hfm
  have hdim : ringKrullDim R = 3 := by
    simpa using ringKrullDim_localizationAtMaximal_mvPolynomial m
  have h := ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors
    hx hxm
  rw [hdim] at h
  apply (ENat.WithBot.add_natCast_cancel
    (a := ringKrullDim (R ⧸ Ideal.span {x})) (b := 2) (c := 1)).mp
  convert h using 1 <;> norm_num
end AllCharacteristics
