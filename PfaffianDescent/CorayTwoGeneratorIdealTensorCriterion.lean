import Mathlib.RingTheory.LocalRing.Module
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
import Mathlib.LinearAlgebra.TensorProduct.Associator
import Mathlib.Tactic.Ring

/-!
# Literal two-generator ideal tensor map

The tensor-injectivity cut is proved by actual two-generator relations.
For a prime P and a parameter x outside P, a prime parameter quotient
constructs the required relation inside the SAME P. The local module
criterion then gives P free, hence principal by its actual inclusion in R.
No projective dimension, flatness, principal P, or numerical genus premise.
SOURCE ONLY / UNVERIFIED; root owns compiler/audit.
-/
noncomputable section
namespace PfaffianDescent.Coray
open scoped TensorProduct
open IsLocalRing
universe u
variable {R : Type u} [CommRing R]

/-- Every literal tensor has a two-generator expression; coefficients
remain in the OWN ideal P, not merely in its containing ring. -/
theorem pairGeneratedIdeal_tensor_decomposition
    (I P : Ideal R) (x y : R) (hx : x ∈ I) (hy : y ∈ I)
    (hI : I = Ideal.span ({x, y} : Set R)) (t : I ⊗[R] P) :
    ∃ a b : P, t = (⟨x, hx⟩ : I) ⊗ₜ[R] a + (⟨y, hy⟩ : I) ⊗ₜ[R] b := by
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul z a =>
    obtain ⟨c, d, hcd⟩ := Ideal.mem_span_pair.mp (hI.le z.property)
    have hz : z = c • (⟨x, hx⟩ : I) + d • (⟨y, hy⟩ : I) := by
      apply Subtype.ext
      exact hcd.symm
    exact ⟨c • a, d • a, by
      simp only [hz, TensorProduct.add_tmul, TensorProduct.smul_tmul,
        TensorProduct.tmul_smul]⟩
  | add t s ht hs =>
    obtain ⟨a, b, hab⟩ := ht
    obtain ⟨c, d, hcd⟩ := hs
    refine ⟨a + c, b + d, ?_⟩
    rw [hab, hcd, TensorProduct.tmul_add, TensorProduct.tmul_add]
    abel

/-- The actual map I⊗P→R⊗P is injective when the OWN two-generator
relations in P are the literal commutative relation (−y,x). -/
theorem pairGeneratedIdeal_rTensor_subtype_injective_of_syzygy
    (I P : Ideal R) (x y : R) (hx : x ∈ I) (hy : y ∈ I)
    (hI : I = Ideal.span ({x, y} : Set R))
    (hrelation : ∀ a b : P, x • a + y • b = 0 →
      ∃ r : P, a = (-y) • r ∧ b = x • r) :
    Function.Injective (I.subtype.rTensor P) := by
  rw [injective_iff_map_eq_zero]
  intro t ht
  obtain ⟨a, b, rfl⟩ := pairGeneratedIdeal_tensor_decomposition I P x y hx hy hI t
  have hrel : x • a + y • b = 0 := by
    have h := congrArg (TensorProduct.lid R P) ht
    simpa only [map_add, LinearMap.rTensor_tmul, TensorProduct.lid_tmul,
      Submodule.subtype_apply, map_zero] using h
  obtain ⟨r, ha, hb⟩ := hrelation a b hrel
  have hcoeff : (-y) • (⟨x, hx⟩ : I) + x • (⟨y, hy⟩ : I) = 0 := by
    apply Subtype.ext
    change (-y) * x + x * y = 0
    ring
  have hxmove : (⟨x, hx⟩ : I) ⊗ₜ[R] ((-y) • r) =
      ((-y) • (⟨x, hx⟩ : I)) ⊗ₜ[R] r :=
    (TensorProduct.smul_tmul (-y) (⟨x, hx⟩ : I) r).symm
  have hymove : (⟨y, hy⟩ : I) ⊗ₜ[R] (x • r) =
      (x • (⟨y, hy⟩ : I)) ⊗ₜ[R] r :=
    (TensorProduct.smul_tmul x (⟨y, hy⟩ : I) r).symm
  rw [ha, hb, hxmove, hymove, ← TensorProduct.add_tmul, hcoeff,
    TensorProduct.zero_tmul]

/-- Primeness of the actual parameter quotient and x outside P derive
EVERY pair relation with its coefficient in the SAME prime ideal P. -/
theorem primeIdeal_pair_syzygy_of_prime_parameter_quotient
    [IsDomain R] (P : Ideal R) [P.IsPrime]
    (x y : R) (hxP : x ∉ P)
    (hprime : (Ideal.span ({x} : Set R)).IsPrime)
    (hy : y ∉ Ideal.span ({x} : Set R))
    (a b : P) (hab : x • a + y • b = 0) :
    ∃ r : P, a = (-y) • r ∧ b = x • r := by
  let J : Ideal R := Ideal.span ({x} : Set R)
  letI : J.IsPrime := hprime
  let q := Ideal.Quotient.mk J
  have hx0 : x ≠ 0 := by
    intro hzero
    apply hxP
    rw [hzero]
    exact P.zero_mem
  have hrel : x * a.val + y * b.val = 0 := congrArg Subtype.val hab
  have hxbar : q x = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton x))
  have hybar : q y ≠ 0 := fun h => hy (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hprod : q y * q b.val = 0 := by
    simpa only [map_add, map_mul, hxbar, zero_mul, zero_add, map_zero] using
      congrArg q hrel
  have hbbar : q b.val = 0 := (mul_eq_zero.mp hprod).resolve_left hybar
  have hbmem : b.val ∈ Ideal.span ({x} : Set R) :=
    Ideal.Quotient.eq_zero_iff_mem.mp hbbar
  obtain ⟨r, hr⟩ : ∃ r : R, b.val = x * r := Ideal.mem_span_singleton.mp hbmem
  have hxr : x * r ∈ P := by rw [← hr]; exact b.property
  have hPrime : P.IsPrime := inferInstance
  have hrP : r ∈ P :=
    (hPrime.mem_or_mem hxr).resolve_left hxP
  have hcancel : x * (a.val + y * r) = 0 := by
    calc
      x * (a.val + y * r) = x * a.val + y * (x * r) := by ring
      _ = 0 := by rw [← hr]; exact hrel
  have ha0 : a.val + y * r = 0 := (mul_eq_zero.mp hcancel).resolve_left hx0
  have ha : a.val = (-y) * r :=
    (eq_neg_iff_add_eq_zero.mpr ha0).trans (neg_mul y r).symm
  refine ⟨⟨r, hrP⟩, ?_, ?_⟩
  · apply Subtype.ext
    exact ha
  · apply Subtype.ext
    exact hr

/-- Over the actual local ring, the literal prime parameter pair constructs
freeness of P and rank at most one, hence a principal generator for P. -/
theorem localPrimeIdeal_isPrincipal_of_pair_parameter_quotient
    [IsLocalRing R] [IsNoetherianRing R] [IsDomain R]
    (P : Ideal R) [P.IsPrime] (x y : R)
    (hx : x ∈ maximalIdeal R) (hy : y ∈ maximalIdeal R)
    (hspan : maximalIdeal R = Ideal.span ({x, y} : Set R))
    (hxP : x ∉ P) (hprime : (Ideal.span ({x} : Set R)).IsPrime)
    (hynot : y ∉ Ideal.span ({x} : Set R)) : P.IsPrincipal := by
  letI : Module.Finite R P := Module.Finite.of_fg (IsNoetherian.noetherian P)
  letI : Module.FinitePresentation R P := Module.finitePresentation_of_finite R P
  have hinj : Function.Injective ((maximalIdeal R).subtype.rTensor P) :=
    pairGeneratedIdeal_rTensor_subtype_injective_of_syzygy
      (maximalIdeal R) P x y hx hy hspan
      (primeIdeal_pair_syzygy_of_prime_parameter_quotient P x y hxP hprime hynot)
  letI : Module.Free R P := Module.free_of_maximalIdeal_rTensor_injective hinj
  apply P.rank_le_one_iff_isPrincipal.mp
  simpa only [Module.rank_self] using
    P.subtype.rank_le_of_injective (show Function.Injective P.subtype from Subtype.val_injective)

end PfaffianDescent.Coray
