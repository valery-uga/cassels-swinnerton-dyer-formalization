import AllCharacteristics.HomogeneousPrimeSeparation
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Homogeneous avoidance for finite antichains of relevant primes

Positive-degree separators are raised to powers of one common degree and
added. Each prime sees exactly one nonzero summand. The argument works over
arbitrary commutative rings, including finite residue fields.
-/

open AlgebraicGeometry
open scoped BigOperators
namespace AllCharacteristics
universe u v w
variable {A : Type u} [CommRing A] {σ : Type v} [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- A finite antichain of relevant homogeneous primes admits one positive-degree
homogeneous element outside every prime. -/
theorem exists_positive_homogeneous_avoiding_antichain {ι : Type w} [Fintype ι]
    (p : ι → ProjectiveSpectrum 𝒜)
    (hp : ∀ i j, i ≠ j → ¬ (p i).asHomogeneousIdeal ≤ (p j).asHomogeneousIdeal) :
    ∃ (D : ℕ), 0 < D ∧ ∃ a : A, a ∈ 𝒜 D ∧ ∀ i, a ∉ (p i).asHomogeneousIdeal := by
  classical
  have hsep (i : ι) := exists_positive_homogeneous_prime_separator 𝒜 (p i)
    (fun j ↦ (p j).asHomogeneousIdeal) (Finset.univ.erase i)
    (fun j hj ↦ hp j i (Finset.ne_of_mem_erase hj))
  choose d hd a ha hn hs using hsep
  let D := ∏ i, d i
  let e (i : ι) := ∏ j ∈ Finset.univ.erase i, d j
  let b (i : ι) := a i ^ e i
  have hD : 0 < D := Finset.prod_pos (fun i _ ↦ hd i)
  have he (i : ι) : 0 < e i := Finset.prod_pos (fun j _ ↦ hd j)
  have hdeg (i : ι) : b i ∈ 𝒜 D := by
    have heq : e i * d i = D := Finset.prod_erase_mul Finset.univ d (Finset.mem_univ i)
    have hb := SetLike.pow_mem_graded (e i) (ha i)
    have hb' : a i ^ e i ∈ 𝒜 (e i * d i) := by
      simpa only [nsmul_eq_mul, Nat.cast_id] using hb
    exact heq ▸ hb'
  have hnot (i : ι) : b i ∉ (p i).asHomogeneousIdeal :=
    fun hb ↦ hn i ((p i).isPrime.mem_of_pow_mem (e i) hb)
  have hmem (i j : ι) (hij : i ≠ j) : b i ∈ (p j).asHomogeneousIdeal :=
    (p j).asHomogeneousIdeal.toIdeal.pow_mem_of_mem
      (hs i j (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩)) (e i) (he i)
  refine ⟨D, hD, ∑ i, b i, sum_mem (fun i _ ↦ hdeg i), ?_⟩
  intro i hi
  have hrest : ∑ j ∈ Finset.univ.erase i, b j ∈ (p i).asHomogeneousIdeal :=
    (p i).asHomogeneousIdeal.toIdeal.sum_mem (fun j hj ↦ hmem j i (Finset.ne_of_mem_erase hj))
  have hsum : b i + ∑ j ∈ Finset.univ.erase i, b j ∈ (p i).asHomogeneousIdeal :=
    (Finset.add_sum_erase Finset.univ b (Finset.mem_univ i)).symm ▸ hi
  apply hnot i
  have hb := (p i).asHomogeneousIdeal.toIdeal.sub_mem hsum hrest
  have hb' : b i ∈ (p i).asHomogeneousIdeal.toIdeal := by
    simpa only [add_sub_cancel_right] using hb
  exact hb'

end AllCharacteristics
