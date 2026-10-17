import PfaffianDescent.ProjectiveFrame
import Mathlib.LinearAlgebra.Dimension.RankNullity

namespace PfaffianDescent
open Module
open scoped BigOperators

section
variable {K : Type*} [Field K]

/-- The linear map whose kernel is the space of relations among five vectors. -/
noncomputable def frameRelationMap (p : Fin 5 → Vec K 4) : (Fin 5 → K) →ₗ[K] Vec K 4 where
  toFun c := ∑ i, c i • p i
  map_add' c d := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a c := by simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply]

lemma frameRelationMap_surjective (p : Fin 5 → Vec K 4)
    (hp : Submodule.span K (Set.range p) = ⊤) : Function.Surjective (frameRelationMap p) := by
  classical
  apply LinearMap.range_eq_top.mp
  apply top_unique
  rw [← hp]
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  refine ⟨Pi.single i 1, ?_⟩
  simp [frameRelationMap, Pi.single_apply]

lemma frameRelationSpace_finrank (p : Fin 5 → Vec K 4)
    (hp : Submodule.span K (Set.range p) = ⊤) :
    finrank K (LinearMap.ker (frameRelationMap p)) = 1 := by
  have h := (frameRelationMap p).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (frameRelationMap_surjective p hp)] at h
  simp only [finrank_top] at h
  simp only [Vec, Module.finrank_pi, Module.finrank_self, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at h
  omega

/-- Spanning five vectors in four-space have a one-dimensional relation space. -/
lemma frame_relations_proportional (p : Fin 5 → Vec K 4)
    (hp : Submodule.span K (Set.range p) = ⊤)
    (c : Fin 5 → K) (hc : c ≠ 0) (hcr : ∑ i, c i • p i = 0)
    (d : Fin 5 → K) (hdr : ∑ i, d i • p i = 0) :
    ∃ a : K, a • c = d := by
  let c' : LinearMap.ker (frameRelationMap p) := ⟨c, hcr⟩
  let d' : LinearMap.ker (frameRelationMap p) := ⟨d, hdr⟩
  have hc' : c' ≠ 0 := by intro h; exact hc (congrArg Subtype.val h)
  obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' c' hc').mp
    (frameRelationSpace_finrank p hp) d'
  exact ⟨a, congrArg Subtype.val ha⟩

/-- The semilinear permutation of a relation induced by a field automorphism
is again a relation. -/
lemma frame_relation_transport (p : Fin 5 → Vec K 4)
    (σ : K ≃+* K) (e : Equiv.Perm (Fin 5))
    (he : ∀ i j, p (e i) j = σ (p i j))
    (c : Fin 5 → K) (hc : ∑ i, c i • p i = 0) :
    ∑ i, σ (c (e.symm i)) • p i = 0 := by
  funext j
  have h := congrFun hc j
  change (∑ i, c i * p i j) = 0 at h
  change (∑ i, σ (c (e.symm i)) * p i j) = 0
  calc
    _ = ∑ i, σ (c i) * p (e i) j := by
      simpa only [e.symm_apply_apply] using
        (Equiv.sum_comp e (fun i => σ (c (e.symm i)) * p i j)).symm
    _ = σ (∑ i, c i * p i j) := by simp only [he, map_sum, map_mul]
    _ = 0 := by rw [h, map_zero]

/-- Transitivity preserves the support of the one-dimensional relation space,
so no coefficient of a nonzero relation can vanish. -/
theorem transitive_frame_relation_coeff_ne_zero (p : Fin 5 → Vec K 4)
    (hp : Submodule.span K (Set.range p) = ⊤)
    (htrans : ∀ i j : Fin 5, ∃ (σ : K ≃+* K) (e : Equiv.Perm (Fin 5)),
      e i = j ∧ ∀ a b, p (e a) b = σ (p a b))
    (c : Fin 5 → K) (hc : c ≠ 0) (hcr : ∑ i, c i • p i = 0) :
    ∀ i, c i ≠ 0 := by
  classical
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hc
  intro i hi
  obtain ⟨σ, e, he, hep⟩ := htrans j i
  let d : Fin 5 → K := fun a => σ (c (e.symm a))
  have hdr : ∑ a, d a • p a = 0 := frame_relation_transport p σ e hep c hcr
  obtain ⟨a, ha⟩ := frame_relations_proportional p hp c hc hcr d hdr
  have hdi : d i = 0 := by
    have hh := congrFun ha i
    simpa only [Pi.smul_apply, hi, smul_zero] using hh.symm
  have hdj : d i = σ (c j) := by simp only [d, ← he, e.symm_apply_apply]
  apply hj
  exact σ.injective (hdj.symm.trans hdi |>.trans (map_zero σ).symm)

end
end PfaffianDescent
