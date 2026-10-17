import AllCharacteristics.HomogeneousProjectiveAmbient
import Mathlib.RingTheory.Ideal.Colon
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Data.Finset.Lattice.Fold

/-! Uniform coordinate torsion bounds derived from actual Noetherian colon
chains. No saturation, section surjectivity or cohomology certificate is an
input. SOURCE ONLY UNVERIFIED; root owns compilation and acceptance. -/
noncomputable section
namespace PfaffianDescent.Coray
open MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u v
attribute [local instance] MvPolynomial.gradedAlgebra

/-- A single actual Noetherian ideal has one power bound for every element
which is killed modulo that ideal by some power of the actual element z. -/
theorem noetherianIdeal_coordinatePowerTorsion_uniformBound
    {R : Type u} [CommRing R] [IsNoetherianRing R] (J : Ideal R) (z : R) :
    ∃ N : ℕ, ∀ a : R, (∃ n : ℕ, z ^ n * a ∈ J) → z ^ N * a ∈ J := by
  let c : ℕ →o Ideal R :=
    { toFun := fun n => J.colon ({z ^ n} : Set R)
      monotone' := monotone_nat_of_le_succ (fun n a ha => by
        apply Submodule.mem_colon_singleton.mpr
        have h := Submodule.mem_colon_singleton.mp ha
        simpa only [smul_eq_mul, pow_succ, mul_assoc, mul_comm, mul_left_comm]
          using J.mul_mem_left z h) }
  obtain ⟨N, hN⟩ :=
    monotone_stabilizes_iff_noetherian.mpr (inferInstance : IsNoetherian R R) c
  refine ⟨N, ?_⟩
  intro a ha
  obtain ⟨n, hn⟩ := ha
  have hcn : a ∈ c n := by
    apply Submodule.mem_colon_singleton.mpr
    simpa only [smul_eq_mul, mul_comm] using hn
  have hcN : a ∈ c N := by
    rw [hN (max N n) (le_max_left N n)]
    exact c.monotone (le_max_right N n) hcn
  simpa only [smul_eq_mul, mul_comm] using
    (Submodule.mem_colon_singleton.mp hcN)

/-- For the actual homogeneous polynomial ideal, one exponent simultaneously
bounds all four coordinate saturations. The bound is uniform in the polynomial
and preserves the whole original ideal, including its nilpotent structure. -/
theorem homogeneousIdeal_fourCoordinatePowerTorsion_uniformBound
    {K : Type v} [Field K]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) :
    ∃ N : ℕ, ∀ j : Fin 4, ∀ a : MvPolynomial (Fin 4) K,
      (∃ n : ℕ, (MvPolynomial.X j) ^ n * a ∈ I.toIdeal) →
      (MvPolynomial.X j) ^ N * a ∈ I.toIdeal := by
  classical
  choose b hb using fun j : Fin 4 =>
    noetherianIdeal_coordinatePowerTorsion_uniformBound I.toIdeal (MvPolynomial.X j)
  refine ⟨Finset.univ.sup b, ?_⟩
  intro j a ha
  have hj : b j ≤ Finset.univ.sup b := Finset.le_sup (Finset.mem_univ j)
  have h := I.toIdeal.mul_mem_left
    ((MvPolynomial.X j) ^ (Finset.univ.sup b - b j)) (hb j a ha)
  rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hj] at h
  exact h

/-- The actual homogeneous polynomial ideal admits actual finite homogeneous
ideal generators with one derived degree bound. No generator/presentation
certificate is supplied; Noetherianity and homogeneity construct them. -/
theorem homogeneousIdeal_exists_finite_homogeneousGenerators_with_degreeBound
    {K : Type v} [Field K]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) :
    ∃ (T : Finset (MvPolynomial (Fin 4) K)) (N : ℕ),
      Ideal.span (T : Set (MvPolynomial (Fin 4) K)) = I.toIdeal ∧
      ∀ a ∈ T, ∃ d : ℕ, d ≤ N ∧ a.IsHomogeneous d := by
  classical
  obtain ⟨S, hS⟩ :=
    (Ideal.IsHomogeneous.iff_exists (homogeneousSubmodule (Fin 4) K) I.toIdeal).mp
      I.isHomogeneous
  let H : Set (MvPolynomial (Fin 4) K) := Subtype.val '' S
  have hfg : (Ideal.span H : Ideal (MvPolynomial (Fin 4) K)).FG := by
    rw [← hS]
    exact Ideal.fg_of_isNoetherianRing I.toIdeal
  obtain ⟨T, hT, hspan⟩ :=
    (Submodule.fg_span_iff_fg_span_finset_subset H).mp hfg
  have hhom : ∀ a : T, ∃ d : ℕ, (a : MvPolynomial (Fin 4) K).IsHomogeneous d := by
    intro a
    obtain ⟨b, _hb, heq⟩ := hT a.property
    exact heq ▸ b.property
  choose d hd using hhom
  refine ⟨T, Finset.univ.sup d, hspan.symm.trans hS.symm, ?_⟩
  intro a ha
  exact ⟨d ⟨a, ha⟩, Finset.le_sup (f := d) (Finset.mem_univ (⟨a, ha⟩ : T)), hd ⟨a, ha⟩⟩

end PfaffianDescent.Coray
