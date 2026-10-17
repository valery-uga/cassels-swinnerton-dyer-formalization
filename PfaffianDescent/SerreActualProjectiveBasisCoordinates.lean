import PfaffianDescent.SerreActualProjectiveBasisParameter

/-! Actual basis-change matrices preserve the coordinates of the same
section after coefficient extension and after normalization. -/
noncomputable section
open Module
open scoped Matrix
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem projectiveBasisCoordinates_coefficient_section
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {V : Type*} [AddCommGroup V] [Module K V]
    {n : ℕ} (b c : Basis (Fin n) K V) (s : V) :
    (c.toMatrix b).map (algebraMap K L) *ᵥ
        (fun i => algebraMap K L (b.repr s i)) =
      fun i => algebraMap K L (c.repr s i) := by
  funext i
  have h := (algebraMap K L).map_mulVec (c.toMatrix b) (b.repr s) i
  rw [Basis.toMatrix_mulVec_repr] at h
  exact h.symm

theorem projectiveBasisCoordinates_normalized_section
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {V : Type*} [AddCommGroup V] [Module K V]
    {n : ℕ} (b c : Basis (Fin n) K V) (s : V) (a : L) :
    (c.toMatrix b).map (algebraMap K L) *ᵥ
        (fun i => a * algebraMap K L (b.repr s i)) =
      fun i => a * algebraMap K L (c.repr s i) := by
  change (c.toMatrix b).map (algebraMap K L) *ᵥ
    (a • (fun i => algebraMap K L (b.repr s i))) =
      a • (fun i => algebraMap K L (c.repr s i))
  rw [Matrix.mulVec_smul, projectiveBasisCoordinates_coefficient_section]

end PfaffianDescent
