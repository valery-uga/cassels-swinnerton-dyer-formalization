import PfaffianDescent.AmbientPointKoszulBasisChartUniqueness
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Determinant

/-! # An actual homogeneous coordinate basis centered at any nonzero vector -/

noncomputable section
open MvPolynomial

namespace PfaffianDescent
universe u

/-- Any nonzero rational vector admits an invertible homogeneous coordinate
basis whose values at that vector are exactly `[1,0,0,0]`. -/
theorem ambientPointKoszul_exists_basis_for_vector
    {K : Type u} [Field K] (v : Fin 4 → K) (hv : v ≠ 0) :
    ∃ M : Matrix (Fin 4) (Fin 4) K,
      IsUnit M.det ∧ M.mulVec v = ambientPointKoszul_vector K := by
  classical
  let source : Fin 1 → (Fin 4 → K) := fun _ => v
  let target : Fin 1 → (Fin 4 → K) := fun _ => ambientPointKoszul_vector K
  have hs : LinearIndependent K source := by
    rw [linearIndependent_unique_iff]
    exact hv
  have ht : LinearIndependent K target := by
    rw [linearIndependent_unique_iff]
    intro h
    have h0 := congrFun h (0 : Fin 4)
    exact one_ne_zero h0
  let W := Submodule.span K (Set.range source)
  let W' := Submodule.span K (Set.range target)
  let f := hs.linearCombinationEquiv.symm ≪≫ₗ ht.linearCombinationEquiv
  letI : FiniteDimensional K W :=
    FiniteDimensional.of_injective W.subtype Subtype.val_injective
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq f
  have hsource : source 0 ∈ W := Submodule.subset_span (Set.mem_range_self 0)
  have htarget : target 0 ∈ W' := Submodule.subset_span (Set.mem_range_self 0)
  have hcombSource : hs.linearCombinationEquiv (Finsupp.single (0 : Fin 1) 1) =
      ⟨source 0, hsource⟩ := by
    apply Subtype.ext
    simp
  have hcombTarget : ht.linearCombinationEquiv (Finsupp.single (0 : Fin 1) 1) =
      ⟨target 0, htarget⟩ := by
    apply Subtype.ext
    simp
  have hf : f ⟨source 0, hsource⟩ = ⟨target 0, htarget⟩ := by
    rw [← hcombSource, ← hcombTarget]
    simp [f]
  have hgv : g v = ambientPointKoszul_vector K := by
    have h := hg ⟨source 0, hsource⟩
    rw [hf] at h
    simpa only [source, target] using h.symm
  let M := LinearMap.toMatrix' g.toLinearMap
  refine ⟨M, ?_, ?_⟩
  · simpa [M] using LinearEquiv.isUnit_det g (Pi.basisFun K (Fin 4))
      (Pi.basisFun K (Fin 4))
  · change (LinearMap.toMatrix' g.toLinearMap).mulVec v = _
    rw [LinearMap.toMatrix'_mulVec]
    exact hgv

end PfaffianDescent
