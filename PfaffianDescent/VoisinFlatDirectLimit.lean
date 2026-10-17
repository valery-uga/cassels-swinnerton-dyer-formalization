import Mathlib.Algebra.Colimit.Module
import Mathlib.RingTheory.Flat.EquationalCriterion

/-!
# Flatness of sequential direct limits

The degree-zero ring of a projective coordinate chart is a sequential
direct limit of homogeneous pieces. This file proves the flatness step for
that route using the equational criterion.
-/

namespace PfaffianDescent

universe u v

/-- A sequential direct limit of flat modules is flat. -/
theorem flat_nat_directLimit
    {R : Type u} [CommRing R]
    {G : ℕ → Type v} [∀ n, AddCommGroup (G n)] [∀ n, Module R (G n)]
    [∀ n, Module.Flat R (G n)]
    (f : ∀ i j, i ≤ j → G i →ₗ[R] G j)
    [DirectedSystem G (f · · ·)] :
    Module.Flat R (Module.DirectLimit G f) := by
  classical
  apply Module.Flat.of_forall_isTrivialRelation
  intro l a x hrel
  have hex (i : Fin l) : ∃ n : ℕ, ∃ y : G n,
      Module.DirectLimit.of R ℕ G f n y = x i :=
    Module.DirectLimit.exists_of (x i)
  choose n y hy using hex
  let N : ℕ := Finset.univ.sup n
  have hle (i : Fin l) : n i ≤ N := Finset.le_sup (Finset.mem_univ i)
  let z (i : Fin l) : G N := f (n i) N (hle i) (y i)
  have hz (i : Fin l) : Module.DirectLimit.of R ℕ G f N (z i) = x i := by
    rw [← hy i]
    exact Module.DirectLimit.of_f
  have hzero : Module.DirectLimit.of R ℕ G f N (∑ i, a i • z i) = 0 := by
    rw [map_sum]
    simp_rw [map_smul, hz]
    exact hrel
  obtain ⟨M, hNM, hMzero⟩ := Module.DirectLimit.of.zero_exact hzero
  let w (i : Fin l) : G M := f N M hNM (z i)
  have hwzero : ∑ i, a i • w i = 0 := by
    change ∑ i, a i • f N M hNM (z i) = 0
    simp_rw [← map_smul]
    rw [← map_sum]
    exact hMzero
  obtain ⟨k, b, t, hbt, hbtzero⟩ :=
    Module.Flat.isTrivialRelation_of_sum_smul_eq_zero hwzero
  refine ⟨k, b, (fun j => Module.DirectLimit.of R ℕ G f M (t j)), ?_, hbtzero⟩
  intro i
  rw [← hz i, ← Module.DirectLimit.of_f (hij := hNM)]
  change Module.DirectLimit.of R ℕ G f M (w i) = _
  rw [hbt i, map_sum]
  simp only [map_smul]

end PfaffianDescent
