import AllCharacteristics.RegularPairDimension
import Mathlib.RingTheory.Regular.IsSMulRegular
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.LocalRing.Quotient

/-!
Construct a regular pair inside an arbitrary ideal with Artinian quotient
on a regular local surface, by taking suitable powers of parameters.
-/

open scoped nonZeroDivisors

namespace AllCharacteristics.HilbertSurfaceDraft

/-- A second regular element remains regular after replacing the first
element by any power.  The proof is elementary cancellation, not a
regular-sequence power theorem. -/
theorem isSMulRegular_quotient_first_power
    {R : Type*} [CommRing R] (a b : R)
    (ha : IsSMulRegular R a)
    (hb : IsSMulRegular (R ⧸ Ideal.span {a}) b) (n : ℕ) :
    IsSMulRegular (R ⧸ Ideal.span {a ^ n}) b := by
  induction n with
  | zero =>
    apply (isSMulRegular_quotient_iff_mem_of_smul_mem
      (Ideal.span ({a ^ 0} : Set R)) b).mpr
    intro z _
    simp
  | succ n ih =>
    apply (isSMulRegular_quotient_iff_mem_of_smul_mem
      (Ideal.span ({a ^ (n + 1)} : Set R)) b).mpr
    intro z hz
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.mp hz
    have hbase : b • z ∈ Ideal.span ({a} : Set R) := by
      apply Ideal.mem_span_singleton.mpr
      refine ⟨a ^ n * w, ?_⟩
      calc
        b • z = a ^ (n + 1) * w := hw
        _ = a * (a ^ n * w) := by rw [pow_succ']; ring
    have hzbase : z ∈ Ideal.span ({a} : Set R) :=
      mem_of_isSMulRegular_quotient_of_smul_mem hb hbase
    obtain ⟨v, hv⟩ := Ideal.mem_span_singleton.mp hzbase
    have hcancel : b * v = a ^ n * w := by
      apply ha
      change a * (b * v) = a * (a ^ n * w)
      calc
        a * (b * v) = b * (a * v) := by ring
        _ = b * z := by rw [← hv]
        _ = a ^ (n + 1) * w := hw
        _ = a * (a ^ n * w) := by rw [pow_succ']; ring
    have hvpow : v ∈ Ideal.span ({a ^ n} : Set R) := by
      apply mem_of_isSMulRegular_quotient_of_smul_mem ih
      exact Ideal.mem_span_singleton.mpr ⟨w, hcancel⟩
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton.mp hvpow
    apply Ideal.mem_span_singleton.mpr
    refine ⟨t, ?_⟩
    calc
      z = a * v := hv
      _ = a * (a ^ n * t) := by rw [ht]
      _ = a ^ (n + 1) * t := by rw [pow_succ']; ring

/-- Powers of any regular local parameter pair lie in every ideal whose
quotient is Artinian.  This applies to arbitrary non-lci finite subschemes. -/
theorem exists_regular_pair_in_ideal_of_artinian_quotient
    {R : Type*} [CommRing R] [IsRegularLocalRing R]
    (hdim : ringKrullDim R = 2) (I : Ideal R)
    [IsArtinianRing (R ⧸ I)] :
    ∃ a b : R, a ∈ I ∧ b ∈ I ∧ IsSMulRegular R a ∧
      IsSMulRegular (R ⧸ Ideal.span {a}) b := by
  obtain ⟨x, y, hx, hx2, hybar, hxreg, hyreg⟩ :=
    exists_local_nonZeroDivisor_pair_of_regularLocal_dim_two hdim
  let Q := R ⧸ Ideal.span {x}
  let π : R →+* Q := Ideal.Quotient.mk (Ideal.span {x})
  have hy : y ∈ IsLocalRing.maximalIdeal R := by
    have hy' : y ∈ ((IsLocalRing.maximalIdeal R).map π).comap π := hybar
    rw [Ideal.comap_map_of_surjective π Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker] at hy'
    have hspan : Ideal.span ({x} : Set R) ≤ IsLocalRing.maximalIdeal R :=
      Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hx)
    simpa only [sup_eq_left.mpr hspan] using hy'
  have hxR : IsSMulRegular R x :=
    Module.Flat.isSMulRegular_of_nonZeroDivisors hxreg
  have hyQ : IsSMulRegular Q y := by
    have h : IsSMulRegular Q (π y) :=
      Module.Flat.isSMulRegular_of_nonZeroDivisors hyreg
    simpa [IsSMulRegular, Algebra.smul_def, π, Q,
      Ideal.Quotient.algebraMap_eq] using h
  obtain ⟨n, hn⟩ :=
    IsLocalRing.exists_maximalIdeal_pow_le_of_isArtinianRing_quotient I
  refine ⟨x ^ n, y ^ n, hn (Ideal.pow_mem_pow hx n),
    hn (Ideal.pow_mem_pow hy n), IsSMulRegular.pow n hxR, ?_⟩
  exact IsSMulRegular.pow n (isSMulRegular_quotient_first_power x y hxR hyQ n)

end AllCharacteristics.HilbertSurfaceDraft
