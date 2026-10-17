import PfaffianDescent.SerreActualProjectiveBasisParameter

/-! Entries of the actual canonical basis-change matrix under its actual
rank-index transport. -/
noncomputable section
open Module
namespace PfaffianDescent
universe u v

theorem serreActualCanonicalBasisMatrix_reindex
    {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {n : ℕ} (h : finrank K V = n)
    {ι : Type*} (b : Basis ι K V) (i : Fin n) (j : ι) :
    (finBasisOfFinrankEq K V h).toMatrix b i j =
      (Module.finBasis K V).toMatrix b ((finCongr h).symm i) j := by
  simp only [finBasisOfFinrankEq, Basis.toMatrix_apply, Basis.repr_reindex_apply]

end PfaffianDescent
