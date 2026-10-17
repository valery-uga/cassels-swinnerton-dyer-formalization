import PfaffianDescent.GeometricEvaluation

namespace PfaffianDescent
open Module
open scoped BigOperators

section
variable {K A L : Type*} [Field K] [CommRing A] [Algebra K A]
    [Field L] [Algebra K L] [FiniteDimensional K A] {n m : ℕ}

/-- Independent coordinate functions remain spanning after all geometric
evaluations. This proves the needed descent of the geometric linear span. -/
theorem geometric_span_eq_top_of_coordinates_independent
    (hdim : finrank K A = n) (ev : Fin n → A →ₐ[K] L) (hev : Function.Injective ev)
    (p : Vec A m) (hp : LinearIndependent K p) :
    Submodule.span L (Set.range (fun i j => ev i (p j))) = ⊤ := by
  classical
  let F := Fintype.linearCombination K p
  have hF : LinearMap.ker F = ⊥ := LinearMap.ker_eq_bot.mpr hp.fintypeLinearCombination_injective
  obtain ⟨g, hg⟩ := F.exists_leftInverse_of_injective hF
  have hgp (j : Fin m) : g (p j) = Pi.single j 1 := by
    have h := LinearMap.congr_fun hg (Pi.single j 1)
    simpa only [LinearMap.comp_apply, F, Fintype.linearCombination_apply_single,
      one_smul, LinearMap.id_apply] using h
  let W := Submodule.span L (Set.range (fun i j => ev i (p j)))
  let B := algebraHomsBasis hdim ev hev
  have hsingle (j : Fin m) : Pi.single j (1 : L) ∈ W := by
    let ell : A →ₗ[K] L := (Algebra.linearMap K L).comp ((LinearMap.proj j).comp g)
    have heq : (∑ i : Fin n, B.repr ell i • (fun k : Fin m => ev i (p k))) =
        Pi.single j (1 : L) := by
      funext k
      have h := congrArg (fun t : A →ₗ[K] L => t (p k)) (B.sum_repr ell)
      simp only [B, algebraHomsBasis_apply, LinearMap.sum_apply, LinearMap.smul_apply,
        AlgHom.toLinearMap_apply, ell, LinearMap.comp_apply, Algebra.linearMap_apply,
        LinearMap.proj_apply, hgp, Pi.single_apply, smul_eq_mul] at h
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
      by_cases hjk : j = k
      · subst k
        simpa only [↓reduceIte, map_one] using h
      · simpa only [hjk, Ne.symm hjk, ↓reduceIte, map_zero] using h
    rw [← heq]
    apply Submodule.sum_mem
    intro i _
    exact W.smul_mem _ (Submodule.subset_span (Set.mem_range_self i))
  apply top_unique
  intro v _
  have hv : v = ∑ j : Fin m, v j • Pi.single j (1 : L) := by
    funext j
    simp [Pi.single_apply]
  rw [hv]
  exact Submodule.sum_mem W (fun j _ => W.smul_mem _ (hsingle j))

/-- If the geometric span is proper, a nonzero ground-field linear equation
vanishes on all coordinates. Thus the point lies in a plane defined over the
ground field when there are four coordinates. -/
theorem ground_linear_relation_of_proper_geometric_span
    (hdim : finrank K A = n) (ev : Fin n → A →ₐ[K] L) (hev : Function.Injective ev)
    (p : Vec A m) (hspan : Submodule.span L (Set.range (fun i j => ev i (p j))) ≠ ⊤) :
    ∃ c : Fin m → K, c ≠ 0 ∧ ∑ j, c j • p j = 0 := by
  have hp : ¬ LinearIndependent K p := fun hp =>
    hspan (geometric_span_eq_top_of_coordinates_independent hdim ev hev p hp)
  obtain ⟨c, hc, j, hj⟩ := Fintype.not_linearIndependent_iff.mp hp
  refine ⟨c, ?_, hc⟩
  intro h
  exact hj (congrFun h j)

end
end PfaffianDescent
