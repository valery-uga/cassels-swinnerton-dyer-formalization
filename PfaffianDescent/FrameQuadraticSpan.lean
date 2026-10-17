import PfaffianDescent.FivePointResolution
import PfaffianDescent.HomogeneousCoordinateEquiv

namespace PfaffianDescent
open MvPolynomial
open scoped BigOperators
section
variable {K : Type*} [Field K]

/-- Every quadratic in the frame ideal is a ground-field linear combination of
its five displayed quadrics. -/
theorem frame_quadratic_mem_span (p : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 2) (hI : p ∈ frameIdeal) :
    p ∈ Submodule.span K (Set.range (frameRelations (K := K))) := by
  obtain ⟨v, hv⟩ := (frameGradedLast_range_iff 0 ⟨p, hp⟩).mpr hI
  have hc (i : Fin 5) : (v i).val = C (coeff 0 (v i).val) :=
    totalDegree_eq_zero_iff_eq_C.mp ((totalDegree_zero_iff_isHomogeneous (Fin 4)).mpr (v i).property)
  have he : p = ∑ i, coeff 0 (v i).val • frameRelations i := by
    have h := congrArg Subtype.val hv
    change (∑ i, (v i).val * frameRelations i) = p at h
    rw [← h]
    apply Finset.sum_congr rfl
    intro i _
    rw [MvPolynomial.smul_eq_C_mul]
    exact congrArg (fun r => r * frameRelations i) (hc i)
  rw [he]
  exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _
    (Submodule.subset_span (Set.mem_range_self i)))

/-- The quadratic generators after a graded coordinate change span every
quadratic in the transported ideal. -/
theorem changed_frame_quadratic_mem_span
    (E : MvPolynomial (Fin 4) K ≃ₐ[K] MvPolynomial (Fin 4) K)
    (hE : ∀ d (q : MvPolynomial (Fin 4) K), q.IsHomogeneous d → (E q).IsHomogeneous d)
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 2)
    (hI : p ∈ (frameIdeal (K := K)).map E.toRingHom) :
    p ∈ Submodule.span K (Set.range (fun i => E (frameRelations i))) := by
  obtain ⟨q, hq, he⟩ := (Ideal.mem_map_iff_of_surjective E.toRingHom E.surjective).mp hI
  change E q = p at he
  have hqh : q.IsHomogeneous 2 := by
    have h := homogeneous_equiv_symm E hE 2 hp
    rw [← he, AlgEquiv.symm_apply_apply] at h
    exact h
  have hs := frame_quadratic_mem_span q hqh hq
  have hm : E q ∈ (Submodule.span K (Set.range (frameRelations (K := K)))).map E.toLinearMap :=
    Submodule.mem_map.mpr ⟨q, hs, rfl⟩
  rw [Submodule.map_span, ← Set.range_comp] at hm
  exact he ▸ hm

end
end PfaffianDescent
