import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! Source-only, unverified. The linear tangent-incidence criterion used
before Coray's joint line/section selector. No geometric good-position,
regularity, or transversality hypothesis is supplied. -/
namespace PfaffianDescent.Coray
open Module Submodule LinearMap
universe u v w x

section
variable {K : Type u} [Field K]
variable {V : Type v} [AddCommGroup V] [Module K V]
variable {A : Type w} [AddCommGroup A] [Module K A]
variable {T : Type x} [AddCommGroup T] [Module K T]

/-- All tangent conditions are in the span of ordinary evaluation
conditions precisely when every ordinarily vanishing section has zero
first-order value. The duals and both maps retain the ORIGINAL field K. -/
theorem tangent_conditions_le_evaluation_span_iff
    (E : V →ₗ[K] A) (D : V →ₗ[K] T) :
    LinearMap.range D.dualMap ≤ LinearMap.range E.dualMap ↔
      LinearMap.ker E ≤ LinearMap.ker D := by
  rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker,
    LinearMap.range_dualMap_eq_dualAnnihilator_ker]
  constructor
  · intro h
    have hc := Submodule.dualCoannihilator_anti h
    simpa only [Subspace.dualAnnihilator_dualCoannihilator_eq] using hc
  · exact Submodule.dualAnnihilator_anti

/-- This is an equivalence, not an assumed nonzero tangent certificate.
It identifies the exact bad incidence that the subsequent line geometry
must avoid. It is valid without replacing K by a constants field. -/
theorem exists_vanishing_section_with_tangent_ne_zero_iff
    (E : V →ₗ[K] A) (D : V →ₗ[K] T) :
    (∃ s : V, E s = 0 ∧ D s ≠ 0) ↔
      ¬ LinearMap.range D.dualMap ≤ LinearMap.range E.dualMap := by
  rw [tangent_conditions_le_evaluation_span_iff]
  constructor
  · rintro ⟨s, hs, hD⟩ hle
    exact hD (hle (LinearMap.mem_ker.mpr hs))
  · intro hnot
    by_contra hnone
    apply hnot
    intro s hs
    apply LinearMap.mem_ker.mpr
    by_contra hD
    exact hnone ⟨s, LinearMap.mem_ker.mp hs, hD⟩

/-- A hyperplane can contain U without containing the whole tangent
space T exactly when T is not contained in U. This universal separation
law is the linear step after the bad-line incidence estimate. -/
theorem exists_hyperplane_through_span_not_tangent_iff
    (U T : Submodule K V) :
    (∃ phi : Module.Dual K V,
      U ≤ LinearMap.ker phi ∧ ¬ T ≤ LinearMap.ker phi) ↔ ¬ T ≤ U := by
  constructor
  · rintro ⟨phi, hU, hT⟩ hTU
    exact hT (hTU.trans hU)
  · intro hnot
    have hex : ∃ t : V, t ∈ T ∧ t ∉ U := by
      by_contra hnone
      apply hnot
      intro t ht
      by_contra hU
      exact hnone ⟨t, ht, hU⟩
    obtain ⟨t, ht, hU⟩ := hex
    obtain ⟨phi, hphi, hker⟩ := Submodule.exists_le_ker_of_notMem hU
    refine ⟨phi, hker, ?_⟩
    intro hT
    exact hphi (hT ht)

end
end PfaffianDescent.Coray
