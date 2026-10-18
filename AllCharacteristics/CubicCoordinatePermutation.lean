import PfaffianDescent.CubicSecant
import Mathlib.Logic.Equiv.Fintype
import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-! Permuting the four ambient coordinates changes
neither cubic evaluation, its tangent pairing, nor geometric nonsingularity.
This permits use of any graph chart when excluding contained lines. -/

noncomputable section
namespace AllCharacteristics

open PfaffianDescent
open scoped BigOperators
universe u

def cubicCoordinatePermutation {R : Type*} [CommRing R] {n : ℕ}
    (c : Cubic R n) (π : Equiv.Perm (Fin n)) : Cubic R n :=
  fun i => c (π i.1, π i.2.1, π i.2.2)

theorem cubicCoordinatePermutation_eval
    {R : Type*} [CommRing R] {n : ℕ}
    (c : Cubic R n) (π : Equiv.Perm (Fin n)) (x : Fin n → R) :
    (cubicCoordinatePermutation c π).eval (fun i => x (π i)) = c.eval x := by
  exact Equiv.sum_comp (π.prodCongr (π.prodCongr π))
    (fun i : Fin n × Fin n × Fin n => c i * x i.1 * x i.2.1 * x i.2.2)

theorem cubicCoordinatePermutation_mixed
    {R : Type*} [CommRing R] {n : ℕ}
    (c : Cubic R n) (π : Equiv.Perm (Fin n)) (x d : Fin n → R) :
    (cubicCoordinatePermutation c π).mixed (fun i => x (π i)) (fun i => d (π i)) = c.mixed x d := by
  exact Equiv.sum_comp (π.prodCongr (π.prodCongr π))
    (fun i : Fin n × Fin n × Fin n => c i *
      (x i.1 * x i.2.1 * d i.2.2 + x i.1 * d i.2.1 * x i.2.2 +
        d i.1 * x i.2.1 * x i.2.2))

theorem cubicCoordinatePermutation_map
    {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}
    (f : R →+* S) (c : Cubic R n) (π : Equiv.Perm (Fin n)) :
    (cubicCoordinatePermutation c π).map f = cubicCoordinatePermutation (c.map f) π := rfl

/-- Geometric nonsingularity of the original cubic is preserved by a ground
coordinate permutation, over every coefficient homomorphism. -/
theorem cubicCoordinatePermutation_geometrically_nonsingular
    {K : Type u} [Field K] (c : Cubic K 4) (π : Equiv.Perm (Fin 4))
    (hsmooth : ∀ (M : Type u) [Field M] (f : K →+* M) (x : Fin 4 → M),
      x ≠ 0 → (c.map f).eval x = 0 → ∃ d, (c.map f).mixed x d ≠ 0) :
    ∀ (M : Type u) [Field M] (f : K →+* M) (x : Fin 4 → M),
      x ≠ 0 → ((cubicCoordinatePermutation c π).map f).eval x = 0 →
      ∃ d, ((cubicCoordinatePermutation c π).map f).mixed x d ≠ 0 := by
  intro M _ f x hx hcx
  let y : Fin 4 → M := fun i => x (π.symm i)
  have hy : y ≠ 0 := by
    intro hy0
    apply hx
    funext i
    have hi := congrFun hy0 (π i)
    simpa only [y, π.symm_apply_apply, Pi.zero_apply] using hi
  have hcy : (c.map f).eval y = 0 := by
    rw [← cubicCoordinatePermutation_eval (c.map f) π y]
    simpa only [y, π.symm_apply_apply, cubicCoordinatePermutation_map] using hcx
  obtain ⟨d, hd⟩ := hsmooth M f y hy hcy
  refine ⟨fun i => d (π i), ?_⟩
  have h := cubicCoordinatePermutation_mixed (c.map f) π y d
  have hmix : ((cubicCoordinatePermutation c π).map f).mixed x (fun i => d (π i)) =
      (c.map f).mixed y d := by
    simpa only [y, π.symm_apply_apply, cubicCoordinatePermutation_map] using h
  rw [hmix]
  exact hd

end AllCharacteristics
