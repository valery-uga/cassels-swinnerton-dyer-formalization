import PfaffianDescent.CubicFullJetMinorInterpolation
import PfaffianDescent.CubicClosedPointSerreSurfaceJetsDirections

/-!
Full cubic interpolation is preserved when arbitrary normalized surface
tangent frames are replaced by the actual Jacobian-pivot frames.
-/

noncomputable section
namespace PfaffianDescent

open MvPolynomial TrivSqZeroExt Module

variable {K : Type*} [Field K]

set_option backward.isDefEq.respectTransparency false

theorem cubicSurfaceFirstJet_map_injective
    (T : (Fin 2 → K) →ₗ[K] (Fin 2 → K)) (hT : Function.Injective T) :
    Function.Injective (TrivSqZeroExt.map T :
      CubicSurfaceFirstJet K →ₐ[K] CubicSurfaceFirstJet K) := by
  intro a b h
  apply TrivSqZeroExt.ext
  · simpa only [TrivSqZeroExt.fst_map] using congrArg TrivSqZeroExt.fst h
  · apply hT
    simpa only [TrivSqZeroExt.snd_map] using congrArg TrivSqZeroExt.snd h

theorem cubicSurfaceFirstJet_map_aeval
    (T : (Fin 2 → K) →ₗ[K] (Fin 2 → K))
    (J : Fin 4 → CubicSurfaceFirstJet K) (q : MvPolynomial (Fin 4) K) :
    (TrivSqZeroExt.map T) (aeval J q) =
      aeval (fun j => TrivSqZeroExt.map T (J j)) q := by
  have h : (TrivSqZeroExt.map T).comp (aeval J) =
      aeval (fun j => TrivSqZeroExt.map T (J j)) := by
    apply MvPolynomial.algHom_ext
    intro j
    simp
  exact AlgHom.congr_fun h q

/-- The value and derivative are transported together by the actual
square-zero algebra map. -/
theorem cubicElevenPointFullJetRestriction_surjective_of_frameMap
    (x : Fin 11 → Fin 4 → K)
    (J J' : Fin 3 → Fin 4 → CubicSurfaceFirstJet K)
    (T : Fin 3 → (Fin 2 → K) →ₗ[K] (Fin 2 → K))
    (hT : ∀ i, Function.Injective (T i))
    (hJ : ∀ i j, J i j = TrivSqZeroExt.map (T i) (J' i j))
    (hfull : Function.Surjective (cubicElevenPointFullJetRestriction x J)) :
    Function.Surjective (cubicElevenPointFullJetRestriction x J') := by
  intro z
  obtain ⟨q, hq⟩ := hfull ((fun i => TrivSqZeroExt.map (T i) (z.1 i)), z.2)
  refine ⟨q, ?_⟩
  apply Prod.ext
  · funext i
    apply cubicSurfaceFirstJet_map_injective (T i) (hT i)
    have hi := congrFun (congrArg Prod.fst hq) i
    change aeval (J i) q.1 = TrivSqZeroExt.map (T i) (z.1 i) at hi
    change TrivSqZeroExt.map (T i) (aeval (J' i) q.1) =
      TrivSqZeroExt.map (T i) (z.1 i)
    rw [cubicSurfaceFirstJet_map_aeval]
    simpa only [← hJ] using hi
  · have hlast := congrArg Prod.snd hq
    change (fun i => aeval (x (i.natAdd 3)) q.1) = z.2 at hlast ⊢
    exact hlast

/-- A normalized vector in the tangent hyperplane is determined by its
two free coordinates, since the actual gradient pivot is nonzero. -/
theorem cubicNormalizedTangentRow_eq_of_free
    (anchor : Fin 4) (g : Fin 4 → K) (pivot : Fin 3)
    (hpivot : g (anchor.succAbove pivot) ≠ 0)
    (v w : Fin 4 → Fin 2 → K)
    (hv0 : v anchor = 0) (hw0 : w anchor = 0)
    (hvg : ∑ j, g j • v j = 0) (hwg : ∑ j, g j • w j = 0)
    (hfree : ∀ t, v (anchor.succAbove (pivot.succAbove t)) =
      w (anchor.succAbove (pivot.succAbove t))) : v = w := by
  have heqpivot : v (anchor.succAbove pivot) = w (anchor.succAbove pivot) := by
    rw [Fin.sum_univ_succAbove _ anchor, hv0, smul_zero, zero_add,
      Fin.sum_univ_succAbove _ pivot] at hvg
    rw [Fin.sum_univ_succAbove _ anchor, hw0, smul_zero, zero_add,
      Fin.sum_univ_succAbove _ pivot] at hwg
    simp_rw [hfree] at hvg
    have hsmul : g (anchor.succAbove pivot) • v (anchor.succAbove pivot) =
        g (anchor.succAbove pivot) • w (anchor.succAbove pivot) := by
      exact add_right_cancel (hvg.trans hwg.symm)
    exact (smul_right_injective _ hpivot) hsmul
  funext j
  by_cases hj : j = anchor
  · subst j
    exact hv0.trans hw0.symm
  obtain ⟨r, rfl⟩ := Fin.exists_succAbove_eq hj
  by_cases hr : r = pivot
  · subst r
    exact heqpivot
  obtain ⟨t, rfl⟩ := Fin.exists_succAbove_eq hr
  exact hfree t

/-- The free-coordinate matrix of a normalized spanning tangent frame
is an invertible linear map from the canonical Jacobian-pivot frame. -/
theorem cubicNormalizedTangentRow_exists_frameMap
    (anchor : Fin 4) (g : Fin 4 → K) (pivot : Fin 3)
    (hpivot : g (anchor.succAbove pivot) ≠ 0)
    (v : Fin 4 → Fin 2 → K)
    (hv0 : v anchor = 0) (hvg : ∑ j, g j • v j = 0)
    (hspan : Function.Surjective (Fintype.linearCombination K v)) :
    ∃ T : (Fin 2 → K) →ₗ[K] (Fin 2 → K), Function.Bijective T ∧
      ∀ j, v j = T (cubicClosedPointSerreSurfaceJets_row anchor
        (fun r => g (anchor.succAbove r)) pivot j) := by
  classical
  let u := cubicClosedPointSerreSurfaceJets_row anchor
    (fun r => g (anchor.succAbove r)) pivot
  let T : (Fin 2 → K) →ₗ[K] (Fin 2 → K) := Fintype.linearCombination K
    (fun t => v (anchor.succAbove (pivot.succAbove t)))
  have hTrow : v = fun j => T (u j) := by
    apply cubicNormalizedTangentRow_eq_of_free anchor g pivot hpivot v (fun j => T (u j))
    · exact hv0
    · simp [u]
    · exact hvg
    · simp_rw [← map_smul]
      rw [← map_sum]
      rw [cubicClosedPointSerreSurfaceJets_row_gradient_zero anchor g pivot hpivot]
      exact map_zero T
    · intro t
      simp [T, u, Fintype.linearCombination_apply]
  have hTsurj : Function.Surjective T := by
    intro z
    obtain ⟨a, ha⟩ := hspan z
    refine ⟨∑ j, a j • u j, ?_⟩
    rw [map_sum]
    simp_rw [map_smul, ← congrFun hTrow]
    exact ha
  refine ⟨T, ⟨LinearMap.injective_iff_surjective.mpr hTsurj, hTsurj⟩, ?_⟩
  intro j
  exact congrFun hTrow j

end PfaffianDescent
