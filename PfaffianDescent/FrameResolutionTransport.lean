import PfaffianDescent.FrameResolution
import PfaffianDescent.PolynomialLinearChange

namespace PfaffianDescent
open MvPolynomial
open scoped BigOperators
section
variable {K : Type*} [Field K]

noncomputable def changedFrameFirst (E : MvPolynomial (Fin 4) K ≃ₐ[K] MvPolynomial (Fin 4) K) :
    MvPolynomial (Fin 4) K →ₗ[MvPolynomial (Fin 4) K] (Fin 5 → MvPolynomial (Fin 4) K) :=
  LinearMap.toSpanSingleton _ _ (fun i => E (frameRelations i))

noncomputable def changedFrameMiddle (E : MvPolynomial (Fin 4) K ≃ₐ[K] MvPolynomial (Fin 4) K) :
    (Fin 5 → MvPolynomial (Fin 4) K) →ₗ[MvPolynomial (Fin 4) K]
      (Fin 5 → MvPolynomial (Fin 4) K) := ((frameMatrix X).map E).mulVecLin

noncomputable def changedFrameLast (E : MvPolynomial (Fin 4) K ≃ₐ[K] MvPolynomial (Fin 4) K) :
    (Fin 5 → MvPolynomial (Fin 4) K) →ₗ[MvPolynomial (Fin 4) K] MvPolynomial (Fin 4) K :=
  Fintype.linearCombination _ (fun i => E (frameRelations i))

variable (E : MvPolynomial (Fin 4) K ≃ₐ[K] MvPolynomial (Fin 4) K)

lemma changedFrameFirst_map (r : MvPolynomial (Fin 4) K) :
    changedFrameFirst E (E r) = fun i => E (frameFirstMap r i) := by
  funext i
  exact (map_mul E r (frameRelations i)).symm

lemma changedFrameMiddle_map (v : Fin 5 → MvPolynomial (Fin 4) K) :
    changedFrameMiddle E (fun i => E (v i)) = fun i => E (frameMiddleMap v i) := by
  funext i
  exact (RingHom.map_mulVec E.toRingHom (frameMatrix X) v i).symm

lemma changedFrameLast_map (v : Fin 5 → MvPolynomial (Fin 4) K) :
    changedFrameLast E (fun i => E (v i)) = E (frameLastMap v) := by
  change (∑ i, E (v i) * E (frameRelations i)) = E (∑ i, v i * frameRelations i)
  simp only [map_sum, map_mul]

lemma changedFrameFirst_injective : Function.Injective (changedFrameFirst E) := by
  intro r s h
  have he : frameFirstMap (E.symm r) = frameFirstMap (E.symm s) := by
    funext i
    apply E.injective
    have hr := congrFun (changedFrameFirst_map E (E.symm r)) i
    have hs := congrFun (changedFrameFirst_map E (E.symm s)) i
    rw [AlgEquiv.apply_symm_apply] at hr hs
    exact hr.symm.trans ((congrFun h i).trans hs)
  exact E.symm.injective (frameFirstMap_injective he)

lemma changedFrameMiddle_kernel (v : Fin 5 → MvPolynomial (Fin 4) K)
    (hv : changedFrameMiddle E v = 0) :
    ∃ r : MvPolynomial (Fin 4) K, changedFrameFirst E r = v := by
  let u := fun i => E.symm (v i)
  have hu : frameMiddleMap u = 0 := by
    funext i
    apply E.injective
    have he := congrFun (changedFrameMiddle_map E u) i
    simp only [u, AlgEquiv.apply_symm_apply, hv, Pi.zero_apply, map_zero] at he ⊢
    exact he.symm
  have hm : u ∈ LinearMap.range (frameFirstMap (K := K)) :=
    (frameFirstMap_range_eq_middle_ker (K := K)) ▸ hu
  obtain ⟨r, hr⟩ := hm
  refine ⟨E r, ?_⟩
  rw [changedFrameFirst_map, hr]
  funext i
  exact E.apply_symm_apply (v i)

lemma changedFrameLast_kernel (v : Fin 5 → MvPolynomial (Fin 4) K)
    (hv : changedFrameLast E v = 0) :
    ∃ w : Fin 5 → MvPolynomial (Fin 4) K, changedFrameMiddle E w = v := by
  let u := fun i => E.symm (v i)
  have hu : frameLastMap u = 0 := by
    apply E.injective
    have he := changedFrameLast_map E u
    simp only [u, AlgEquiv.apply_symm_apply, hv, map_zero] at he ⊢
    exact he.symm
  have hm : u ∈ LinearMap.range (frameMiddleMap (K := K)) :=
    (frameMiddleMap_range_eq_last_ker (K := K)) ▸ hu
  obtain ⟨w, hw⟩ := hm
  refine ⟨fun i => E (w i), ?_⟩
  rw [changedFrameMiddle_map, hw]
  funext i
  exact E.apply_symm_apply (v i)

lemma changedFrameMiddle_first (r : MvPolynomial (Fin 4) K) :
    changedFrameMiddle E (changedFrameFirst E r) = 0 := by
  obtain ⟨s, rfl⟩ := E.surjective r
  rw [changedFrameFirst_map, changedFrameMiddle_map]
  have hz : frameMiddleMap (frameFirstMap s) = 0 :=
    LinearMap.mem_ker.mp ((frameFirstMap_range_eq_middle_ker (K := K)) ▸
      (show frameFirstMap s ∈ LinearMap.range frameFirstMap from ⟨s, rfl⟩))
  simp only [hz, Pi.zero_apply, map_zero]
  rfl

lemma changedFrameLast_middle (v : Fin 5 → MvPolynomial (Fin 4) K) :
    changedFrameLast E (changedFrameMiddle E v) = 0 := by
  have hv : v = fun i => E (E.symm (v i)) := by
    funext i; exact (E.apply_symm_apply (v i)).symm
  conv_lhs => rw [hv]
  rw [changedFrameMiddle_map, changedFrameLast_map]
  have h := LinearMap.congr_fun (frameLastMap_comp_middle (K := K)) (fun i => E.symm (v i))
  simp only [LinearMap.comp_apply, LinearMap.zero_apply] at h
  rw [h, map_zero]

/-- Exactness of the frame free complex survives every polynomial coordinate isomorphism. -/
theorem changed_frame_resolution :
    Function.Injective (changedFrameFirst E) ∧
    LinearMap.range (changedFrameFirst E) = LinearMap.ker (changedFrameMiddle E) ∧
    LinearMap.range (changedFrameMiddle E) = LinearMap.ker (changedFrameLast E) := by
  refine ⟨changedFrameFirst_injective E, ?_, ?_⟩
  · ext v
    constructor
    · rintro ⟨r, rfl⟩
      exact changedFrameMiddle_first E r
    · exact changedFrameMiddle_kernel E v
  · ext v
    constructor
    · rintro ⟨w, rfl⟩
      exact changedFrameLast_middle E w
    · exact changedFrameLast_kernel E v

end
end PfaffianDescent
