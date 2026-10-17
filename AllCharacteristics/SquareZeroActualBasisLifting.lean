import AllCharacteristics.SquareZeroLinearMapLifting
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.Tactic.Choose

/-! Lift the given basis over the actual downstairs algebra, preserving its
individual basis vectors under the whole canonical base-change map. -/

open Module LinearMap TensorProduct
namespace AllCharacteristics
universe u v w t

/-- Every prescribed family lifting a downstairs basis is itself a basis
when the square-zero tensor obstruction has been proved to vanish. -/
theorem exists_basis_of_prescribed_square_zero_lifts166
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (hRS : Function.Surjective (algebraMap R S))
    (hI : (RingHom.ker (algebraMap R S)) ^ 2 = ⊥)
    {M : Type w} [AddCommGroup M] [Module R M] {ι : Type t}
    (b : Basis ι S (S ⊗[R] M)) (v : ι → M)
    (hv : ∀ i, (1 : S) ⊗ₜ[R] v i = b i)
    (hmu : Function.Injective
      (idealTensorMultiplication166 (RingHom.ker (algebraMap R S)) M)) :
    ∃ b' : Basis ι R M, ∀ i, b' i = v i := by
  classical
  let f := Finsupp.linearCombination R v
  let c : Basis ι S (S ⊗[R] (ι →₀ R)) :=
    (Finsupp.basisSingleOne : Basis ι R (ι →₀ R)).baseChange S
  let e := c.equiv b (Equiv.refl ι)
  have he : f.baseChange S = e.toLinearMap := by
    apply c.ext
    intro i
    have hec : e (c i) = b i := by simp [e]
    change f.baseChange S (c i) = e (c i)
    rw [hec]
    have hc : c i = (1 : S) ⊗ₜ[R] (Finsupp.single i (1 : R)) := by simp [c]
    rw [hc, LinearMap.baseChange_tmul]
    simpa [f] using hv i
  have hred : Function.Bijective (f.lTensor S) := by
    change Function.Bijective (f.baseChange S)
    rw [he]
    exact e.bijective
  have hf := bijective_of_square_zero_actualBaseChange_bijective166 hRS hI f hred hmu
  let e' := LinearEquiv.ofBijective f hf
  refine ⟨Basis.ofRepr e'.symm, ?_⟩
  intro i
  change e' (Finsupp.single i 1) = v i
  simp [e', f]

/-- The basis lifts are constructed from the actual surjective coefficient
reduction.  No basis, freeness, or flatness upstairs is supplied. -/
theorem exists_basis_of_square_zero_actualReduction166
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (hRS : Function.Surjective (algebraMap R S))
    (hI : (RingHom.ker (algebraMap R S)) ^ 2 = ⊥)
    {M : Type w} [AddCommGroup M] [Module R M] {ι : Type t}
    (b : Basis ι S (S ⊗[R] M))
    (hmu : Function.Injective
      (idealTensorMultiplication166 (RingHom.ker (algebraMap R S)) M)) :
    ∃ b' : Basis ι R M, ∀ i, (1 : S) ⊗ₜ[R] b' i = b i := by
  classical
  have hlift : ∀ i, ∃ m : M, (1 : S) ⊗ₜ[R] m = b i := by
    intro i
    exact TensorProduct.mk_surjective (R := R) (M := M) (S := S) hRS (b i)
  choose v hv using hlift
  obtain ⟨b', hb'⟩ := exists_basis_of_prescribed_square_zero_lifts166 hRS hI b v hv hmu
  exact ⟨b', fun i => by rw [hb' i]; exact hv i⟩

/-- A finite downstairs basis gives an actual finite free flat module of
the same rank upstairs, with every original basis vector retained. -/
theorem finite_free_flat_sameRank_of_square_zero_actualReduction166
    {R : Type u} {S : Type v} [CommRing R] [Nontrivial R]
    [CommRing S] [Algebra R S]
    (hRS : Function.Surjective (algebraMap R S))
    (hI : (RingHom.ker (algebraMap R S)) ^ 2 = ⊥)
    {M : Type w} [AddCommGroup M] [Module R M] (d : ℕ)
    (b : Basis (Fin d) S (S ⊗[R] M))
    (hmu : Function.Injective
      (idealTensorMultiplication166 (RingHom.ker (algebraMap R S)) M)) :
    ∃ b' : Basis (Fin d) R M,
      Module.Finite R M ∧ Module.Free R M ∧ Module.Flat R M ∧
      Module.finrank R M = d ∧ ∀ i, (1 : S) ⊗ₜ[R] b' i = b i := by
  obtain ⟨b', hb'⟩ := exists_basis_of_square_zero_actualReduction166 hRS hI b hmu
  letI : Module.Free R M := Module.Free.of_basis b'
  letI : Module.Finite R M := Module.Finite.of_basis b'
  refine ⟨b', inferInstance, inferInstance, inferInstance, ?_, hb'⟩
  simpa using Module.finrank_eq_card_basis b'

end AllCharacteristics
