import Mathlib.RingTheory.Flat.LocallyFree
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.Flat.Stability

noncomputable section
namespace PfaffianDescent
open Module
open scoped TensorProduct
universe u v

/-- Genuine finite-flat constant rank constructs an actual local rank-n basis.
No local freeness, presentation, basis or covering conclusion is assumed. -/
lemma finiteFlatConstantRank_localTensorBasis301
    {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M] [Module A M]
    [Module.Finite A M] [Module.Flat A M] {n : ℕ}
    (hr : ∀ p : PrimeSpectrum A, Module.rankAtStalk (R := A) M p = n)
    (p : PrimeSpectrum A) :
    ∃ s ∉ p.asIdeal, Nonempty
      (Basis (Fin n) (Localization.Away s) (Localization.Away s ⊗[A] M)) := by
  obtain ⟨s, hs, hfree⟩ := Module.Free.away_of_finite_of_flat_of_rankAtStalk_constant M p.asIdeal
    (fun q _ => (hr ⟨q, inferInstance⟩).trans (hr p).symm)
  letI := hfree
  letI : Module.Free (Localization.Away s) (Localization.Away s ⊗[A] M) :=
    Module.Free.of_equiv (LocalizedModule.equivTensorProduct (Submonoid.powers s) M)
  have hp : p ∈ Set.range (PrimeSpectrum.comap (algebraMap A (Localization.Away s))) := by
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away s) s]
    exact (PrimeSpectrum.mem_basicOpen s p).mpr hs
  obtain ⟨q, _⟩ := hp
  letI : Nontrivial (Localization.Away s) := q.nontrivial
  have hd : Module.finrank (Localization.Away s) (Localization.Away s ⊗[A] M) = n := by
    exact (congrFun (Module.rankAtStalk_eq_finrank_of_free
        (R := Localization.Away s) (M := Localization.Away s ⊗[A] M)) q).symm.trans
      ((Module.rankAtStalk_baseChange (R := A) (M := M) q).trans
        (hr (q.comap (algebraMap A (Localization.Away s)))))
  exact ⟨s, hs, ⟨Module.finBasisOfFinrankEq (Localization.Away s)
    (Localization.Away s ⊗[A] M) hd⟩⟩

end PfaffianDescent
