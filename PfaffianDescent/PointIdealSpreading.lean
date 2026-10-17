import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Isolating a closed point from its local ideal

A finitely generated ideal contained in another after localization has one
common denominator clearing all its generators. Applied to a maximal point
ideal, this isolates the common-zero locus on a principal neighborhood.
-/

namespace PfaffianDescent

variable {R S : Type*} [CommRing R] [CommRing S]
variable (M : Submonoid R) [Algebra R S] [IsLocalization M S]

/-- One localization denominator suffices for containment of a finitely
generated ideal. -/
theorem exists_denominator_mul_mem_of_fg
    (I J : Ideal R) (hJ : J.FG)
    (hle : J.map (algebraMap R S) ≤ I.map (algebraMap R S)) :
    ∃ t ∈ M, ∀ x ∈ J, t * x ∈ I := by
  classical
  obtain ⟨s, hs⟩ := hJ
  have hgens : ∀ x ∈ s, ∃ t ∈ M, t * x ∈ I := by
    intro x hx
    apply (IsLocalization.algebraMap_mem_map_algebraMap_iff M S I x).mp
    apply hle
    apply Ideal.mem_map_of_mem
    rw [← hs]
    exact Ideal.subset_span hx
  have hfinite : ∃ t ∈ M, ∀ x ∈ s, t * x ∈ I := by
    clear hs
    induction s using Finset.induction_on with
    | empty => exact ⟨1, M.one_mem, by simp⟩
    | @insert a s ha ih =>
      obtain ⟨u, hu, hua⟩ := hgens a (by simp)
      obtain ⟨t, ht, hts⟩ := ih (fun x hx ↦ hgens x (Finset.mem_insert_of_mem hx))
      refine ⟨u * t, M.mul_mem hu ht, ?_⟩
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · simpa only [mul_assoc, mul_comm u t] using I.mul_mem_left t hua
      · simpa only [mul_assoc] using I.mul_mem_left u (hts x hx)
  obtain ⟨t, ht, hts⟩ := hfinite
  refine ⟨t, ht, ?_⟩
  intro x hx
  rw [← hs] at hx
  induction hx using Submodule.span_induction with
  | mem y hy => exact hts y hy
  | zero => simpa using I.zero_mem
  | add y z hy hz ihy ihz => simpa only [mul_add] using I.add_mem ihy ihz
  | smul a y hy ih =>
    simpa only [smul_eq_mul, mul_left_comm t a] using I.mul_mem_left a ih

/-- If an ideal agrees locally with a finitely generated maximal ideal,
its common-zero locus contains only that point on a principal neighborhood. -/
theorem exists_principal_neighborhood_isolating_maximal_ideal
    (I m : Ideal R) [m.IsMaximal] (hm : m.FG)
    [IsLocalization m.primeCompl S]
    (hle : m.map (algebraMap R S) ≤ I.map (algebraMap R S)) :
    ∃ t ∉ m, ∀ (p : Ideal R) [p.IsPrime], I ≤ p → t ∉ p → p = m := by
  obtain ⟨t, ht, hmul⟩ := exists_denominator_mul_mem_of_fg m.primeCompl I m hm hle
  refine ⟨t, ht, ?_⟩
  intro p hp hIp htp
  have hmp : m ≤ p := by
    intro x hx
    exact (hp.mem_or_mem (hIp (hmul x hx))).resolve_left htp
  exact (Ideal.IsMaximal.eq_of_le (inferInstance : m.IsMaximal) hp.ne_top hmp).symm

end PfaffianDescent
