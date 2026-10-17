import PfaffianDescent.VoisinCanonicalPencilCoefficients
import PfaffianDescent.VoisinQuadraticEvaluationMatrix
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Selecting a quadratic minor from split component spanning

If the component evaluations of a finite coordinate algebra span the split
eight-dimensional coordinate space and quadratic restriction is surjective,
the ordered eight-point evaluation matrix has full row rank.
-/

namespace PfaffianDescent

open MvPolynomial
open AllCharacteristics.UniversalHomogeneous
open AllCharacteristics.HomogeneousProjective

universe u

/-- Distinct geometric components span the whole split coordinate space.
Artin's linear independence of algebra homomorphisms rules out a nonzero
linear functional annihilating all component-value vectors. -/
theorem componentSpan_eq_top_of_injective
    {K A L : Type u} [Field K] [CommRing A] [Algebra K A]
    [Field L] [Algebra K L]
    (φ : Fin 8 → A →ₐ[K] L)
    (hφ : Function.Injective φ) :
    Submodule.span L (Set.range (fun t : A => fun i : Fin 8 => φ i t)) = ⊤ := by
  let W : Submodule L (Fin 8 → L) :=
    Submodule.span L (Set.range (fun t : A => fun i : Fin 8 => φ i t))
  by_contra hn
  have hlt : W < ⊤ := lt_top_iff_ne_top.mpr hn
  obtain ⟨ℓ, hℓ, hker⟩ := W.exists_le_ker_of_lt_top hlt
  let c : Fin 8 → L := fun i => ℓ (Pi.single i 1)
  have hsingle (i : Fin 8) (a : L) : ℓ (Pi.single i a) = a * c i := by
    have h := congrArg ℓ (Pi.single_smul i a (1 : L))
    simpa [c, smul_eq_mul] using h
  have hlin : LinearIndependent L
      (fun i : Fin 8 => (φ i).toLinearMap) :=
    (linearIndependent_algHom_toLinearMap K A L).comp φ hφ
  have hc : ∀ i, c i = 0 := by
    apply Fintype.linearIndependent_iff.mp hlin c
    apply LinearMap.ext
    intro t
    have ht : ℓ (fun i : Fin 8 => φ i t) = 0 :=
      hker (Submodule.subset_span ⟨t, rfl⟩)
    calc
      (∑ i, c i • (φ i).toLinearMap) t = ∑ i, c i * φ i t := by
        simp [Finset.sum_apply, smul_eq_mul]
      _ = ℓ (fun i : Fin 8 => φ i t) := by
        rw [← Finset.univ_sum_single (fun i : Fin 8 => φ i t), map_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [hsingle]
        ring
      _ = 0 := ht
  apply hℓ
  apply LinearMap.ext
  intro v
  rw [← Finset.univ_sum_single v, map_sum]
  simp [hsingle, hc]

theorem quadraticHomogeneousCoefficients_splitEvaluation
    {K A L : Type u} [Field K] [CommRing A] [Algebra K A]
    [Field L] [Algebra K L]
    (φ : Fin 8 → A →ₐ[K] L)
    (x : Fin 4 → A)
    (q : homogeneousSubmodule (Fin 4) K 2)
    (i : Fin 8) :
    (Matrix.toLin' (eightPointQuadraticEvaluationMatrix
      (fun k j => φ k (x j)))
      (fun m => algebraMap K L (quadraticHomogeneousCoefficients K q m))) i =
      φ i (q.1.eval₂ (algebraMap K A) x) := by
  have hnat : φ i (q.1.eval₂ (algebraMap K A) x) =
      q.1.eval₂ (algebraMap K L) (fun j => φ i (x j)) := by
    change (φ i).toRingHom (q.1.eval₂ (algebraMap K A) x) = _
    rw [MvPolynomial.eval₂_comp_left]
    congr 1
    · ext k
      exact (φ i).commutes k
  rw [hnat]
  rw [← quadraticPolynomialOfCoefficients_eval
    (fun m => algebraMap K L (quadraticHomogeneousCoefficients K q m))
    (fun k j => φ k (x j)) i]
  rw [← quadraticPolynomialOfCoefficients_map,
    quadraticPolynomialOfHomogeneousCoefficients]
  exact MvPolynomial.eval₂_eq_eval_map (algebraMap K L)
    (fun j => φ i (x j)) q.1 |>.symm

/-- Surjective quadratic restriction and spanning split components imply
surjectivity of the ordered eight-point quadratic evaluation matrix. -/
theorem eightPointQuadraticEvaluationMatrix_surjective_of_componentSpan
    {K A L : Type u} [Field K] [CommRing A] [Algebra K A]
    [Field L] [Algebra K L]
    (φ : Fin 8 → A →ₐ[K] L)
    (x : Fin 4 → A)
    (hquad : Function.Surjective
      (homogeneousSectionRestriction (K := K) x 2))
    (hcomponents : Submodule.span L
      (Set.range (fun t : A => fun i : Fin 8 => φ i t)) = ⊤) :
    Function.Surjective (Matrix.toLin'
      (eightPointQuadraticEvaluationMatrix
        (fun i j => φ i (x j)))) := by
  let M := Matrix.toLin'
    (eightPointQuadraticEvaluationMatrix (fun i j => φ i (x j)))
  have hle : Submodule.span L
      (Set.range (fun t : A => fun i : Fin 8 => φ i t)) ≤
      LinearMap.range M := by
    apply Submodule.span_le.mpr
    rintro w ⟨t, rfl⟩
    obtain ⟨q, hq⟩ := hquad t
    refine ⟨fun m => algebraMap K L
      (quadraticHomogeneousCoefficients K q m), ?_⟩
    funext i
    rw [quadraticHomogeneousCoefficients_splitEvaluation]
    exact congrArg (φ i) hq
  apply LinearMap.range_eq_top.mp
  apply top_unique
  rw [← hcomponents]
  exact hle

/-- A spanning split component tuple admits a unit eight-column quadratic
evaluation minor whenever ground-field quadratic restriction is surjective. -/
theorem exists_unit_eightPointQuadraticEvaluationMinor_of_componentSpan
    {K A L : Type u} [Field K] [CommRing A] [Algebra K A]
    [Field L] [Algebra K L]
    (φ : Fin 8 → A →ₐ[K] L)
    (x : Fin 4 → A)
    (hquad : Function.Surjective
      (homogeneousSectionRestriction (K := K) x 2))
    (hcomponents : Submodule.span L
      (Set.range (fun t : A => fun i : Fin 8 => φ i t)) = ⊤) :
    ∃ m : Fin 8 ↪ Monomials (Fin 4) 2,
      IsUnit (eightPointQuadraticEvaluationMinor m
        (fun i j => φ i (x j))).det :=
  exists_unit_eightPointQuadraticEvaluationMinor_of_surjective _
    (eightPointQuadraticEvaluationMatrix_surjective_of_componentSpan
      φ x hquad hcomponents)

/-- Distinct ordered components and surjective quadratic restriction select
a full-rank quadratic evaluation minor. -/
theorem exists_unit_eightPointQuadraticEvaluationMinor_of_injective
    {K A L : Type u} [Field K] [CommRing A] [Algebra K A]
    [Field L] [Algebra K L]
    (φ : Fin 8 → A →ₐ[K] L)
    (x : Fin 4 → A)
    (hquad : Function.Surjective
      (homogeneousSectionRestriction (K := K) x 2))
    (hφ : Function.Injective φ) :
    ∃ m : Fin 8 ↪ Monomials (Fin 4) 2,
      IsUnit (eightPointQuadraticEvaluationMinor m
        (fun i j => φ i (x j))).det :=
  exists_unit_eightPointQuadraticEvaluationMinor_of_componentSpan
    φ x hquad (componentSpan_eq_top_of_injective φ hφ)

end PfaffianDescent
