import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Localization.Free
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Ideal.Operations

/-!
Construct the finite-support semilocal ring and spread a simultaneous basis
to one principal open containing every support point. Finite flatness and
constant rank of the module are explicit inputs to the basis theorem.
The surface syzygy modules used in the Hilbert--Burch application satisfy
these hypotheses by the subsequent local surface arguments.
-/
noncomputable section
namespace PfaffianDescent
open Module
open scoped TensorProduct
universe u v
set_option autoImplicit false

/-- Denominators avoiding every point of the specified finite support. -/
def finiteSupportDenominators001
    {R : Type u} [CommRing R] (t : Finset (MaximalSpectrum R)) : Submonoid R where
  carrier := {r | ∀ m ∈ t, r ∉ m.asIdeal}
  one_mem' := by
    intro m _
    exact m.isMaximal.isPrime.one_notMem
  mul_mem' := by
    intro a b ha hb m hm hab
    rcases m.isMaximal.isPrime.mem_or_mem hab with h | h
    · exact ha m hm h
    · exact hb m hm h

/-- Every maximal ideal in the constructed localization contracts to one
of the ORIGINAL specified maximal ideals.  This is finite prime avoidance,
not a semilocality premise. -/
theorem finiteSupportLocalization_maximal_under001
    {R : Type u} [CommRing R] (t : Finset (MaximalSpectrum R)) (ht : t.Nonempty)
    (Q : MaximalSpectrum (Localization (finiteSupportDenominators001 t))) :
    ∃ m ∈ t, Q.asIdeal.under R = m.asIdeal := by
  classical
  let S := finiteSupportDenominators001 t
  let L := Localization S
  have hQ := (IsLocalization.isPrime_iff_isPrime_disjoint S L Q.asIdeal).mp
    Q.isMaximal.isPrime
  have hsub : (Q.asIdeal.under R : Set R) ⊆
      ⋃ m ∈ (t : Set (MaximalSpectrum R)), (m.asIdeal : Set R) := by
    intro x hx
    by_contra hnot
    have hxS : x ∈ S := by
      intro m hm hxm
      apply hnot
      exact Set.mem_iUnion.mpr ⟨m, Set.mem_iUnion.mpr ⟨hm, hxm⟩⟩
    exact Set.disjoint_left.mp hQ.2 hxS hx
  obtain ⟨m0, _⟩ := ht
  obtain ⟨m, hm, hle⟩ :=
    (Ideal.subset_union_prime (f := MaximalSpectrum.asIdeal) m0 m0
      (fun m _ _ _ => m.isMaximal.isPrime)).mp hsub
  have hdis : Disjoint (S : Set R) (m.asIdeal : Set R) :=
    Set.disjoint_left.mpr (fun x hxS hxm => hxS m hm hxm)
  have hproper : m.asIdeal.map (algebraMap R L) ≠ ⊤ :=
    (IsLocalization.map_algebraMap_ne_top_iff_disjoint S L m.asIdeal).mpr hdis
  have hQle : Q.asIdeal ≤ m.asIdeal.map (algebraMap R L) := by
    rw [← IsLocalization.map_under S L Q.asIdeal]
    exact Ideal.map_mono hle
  have heq : Q.asIdeal = m.asIdeal.map (algebraMap R L) :=
    Q.isMaximal.eq_of_le hproper hQle
  refine ⟨m, hm, ?_⟩
  rw [heq]
  exact IsLocalization.under_map_of_isPrime_disjoint S L m.isMaximal.isPrime hdis

/-- The actual finite-support localization is semilocal. -/
theorem finiteSupportLocalization_finite_maximalSpectrum001
    {R : Type u} [CommRing R] (t : Finset (MaximalSpectrum R)) (ht : t.Nonempty) :
    Finite (MaximalSpectrum (Localization (finiteSupportDenominators001 t))) := by
  classical
  let S := finiteSupportDenominators001 t
  let L := Localization S
  have hmem (Q : MaximalSpectrum L) : Q.asIdeal.under R ∈ t.image MaximalSpectrum.asIdeal := by
    obtain ⟨m, hm, heq⟩ := finiteSupportLocalization_maximal_under001 t ht Q
    exact Finset.mem_image.mpr ⟨m, hm, heq.symm⟩
  let g : MaximalSpectrum L → (t.image MaximalSpectrum.asIdeal) :=
    fun Q => ⟨Q.asIdeal.under R, hmem Q⟩
  apply Finite.of_injective g
  intro Q Q' heq
  apply MaximalSpectrum.ext
  apply (IsLocalization.orderEmbedding S L).injective
  exact congrArg Subtype.val heq

/-- A finite flat module with constant rank on the constructed semilocal
ring has a basis on ONE original principal open avoiding the entire finite
support.  Applied to a syzygy module, this yields one simultaneous matrix
domain without splitting the ambient ring into quotient components. -/
theorem finiteSupportLocalization_exists_principal_basis001
    {R : Type u} [CommRing R]
    (t : Finset (MaximalSpectrum R)) (ht : t.Nonempty)
    (M : Type v) [AddCommGroup M] [Module R M] [Module.FinitePresentation R M]
    [Module.Flat (Localization (finiteSupportDenominators001 t))
      (LocalizedModule (finiteSupportDenominators001 t) M)]
    (n : ℕ)
    (rk : ∀ P : MaximalSpectrum (Localization (finiteSupportDenominators001 t)),
      Module.finrank (Localization (finiteSupportDenominators001 t) ⧸ P.asIdeal)
        ((Localization (finiteSupportDenominators001 t) ⧸ P.asIdeal) ⊗[
          Localization (finiteSupportDenominators001 t)]
          LocalizedModule (finiteSupportDenominators001 t) M) = n) :
    ∃ r : R, (∀ m ∈ t, r ∉ m.asIdeal) ∧
      Nonempty (Basis (Fin n) (Localization (.powers r)) (LocalizedModule.Away r M)) := by
  let S := finiteSupportDenominators001 t
  let L := Localization S
  letI : Finite (MaximalSpectrum L) :=
    finiteSupportLocalization_finite_maximalSpectrum001 t ht
  letI : Module.Finite L (LocalizedModule S M) :=
    Module.Finite.of_isLocalizedModule S (Rₚ := L) (LocalizedModule.mkLinearMap S M)
  obtain ⟨b⟩ := Module.nonempty_basis_of_flat_of_finrank_eq L (LocalizedModule S M) n rk
  obtain ⟨r, hr, b', _⟩ :=
    Module.FinitePresentation.exists_basis_localizedModule_powers S
      (LocalizedModule.mkLinearMap S M) L b
  exact ⟨r, hr, ⟨b'⟩⟩

end PfaffianDescent
end
