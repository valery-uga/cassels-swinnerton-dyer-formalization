import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Fin

/-! SOURCE ONLY, UNVERIFIED. The labeling permutation is derived from the
actual four support points, with no Galois-action certificate. -/
noncomputable section
namespace PfaffianDescent

theorem finiteFour_actual_support_relabeling {X : Type*}
    (canonical supplied : Fin 4 → X)
    (hCanonical : Function.Injective canonical) (hSupplied : Function.Injective supplied)
    (hRange : Set.range supplied = Set.range canonical) :
    ∃ rho : Equiv.Perm (Fin 4), ∀ i, supplied i = canonical (rho i) := by
  classical
  have h (i : Fin 4) : ∃ j, canonical j = supplied i := by
    have hi : supplied i ∈ Set.range canonical := by
      rw [← hRange]
      exact Set.mem_range_self i
    exact hi
  choose f hf using h
  have hInjective : Function.Injective f := by
    intro i j hij
    apply hSupplied
    rw [← hf i, ← hf j, hij]
  let rho := Equiv.ofBijective f ⟨hInjective, Finite.surjective_of_injective hInjective⟩
  exact ⟨rho, fun i => (hf i).symm⟩

end PfaffianDescent
