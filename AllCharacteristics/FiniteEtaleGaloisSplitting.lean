import Mathlib.RingTheory.TotallySplit
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-!
# Finite Galois splitting fields for finite étale algebras

A finite étale algebra of rank `n` over a characteristic-zero field becomes
the product of exactly `n` copies of a finite Galois extension.  This is the
algebraic input needed to turn an arbitrary finite étale subscheme, including
a disconnected one, into one Galois-stable ordered configuration.
-/

open scoped TensorProduct

namespace AllCharacteristics

universe u

/-- A finite split algebra whose original rank is `n` is split into exactly
`n` factors. -/
theorem nonempty_finiteSplitAlgEquivFin
    (K A L : Type u) [Field K] [CommRing A] [Algebra K A]
    [Field L] [Algebra K L] [Module.Finite K A]
    [Algebra.IsFiniteSplit L (L ⊗[K] A)]
    (n : ℕ) (hn : Module.finrank K A = n) :
    Nonempty ((L ⊗[K] A) ≃ₐ[L] (Fin n → L)) := by
  obtain ⟨m, ⟨e⟩⟩ :=
    Algebra.IsFiniteSplit.nonempty_algEquiv_fun L (L ⊗[K] A)
  have hm : n = m := by
    have h := e.toLinearEquiv.finrank_eq
    simpa [Module.finrank_baseChange, hn] using h
  subst m
  exact ⟨e⟩

/-- Every finite étale rank-`n` algebra over a characteristic-zero field has
a finite Galois splitting field over which it is the product of `n` copies of
that field. -/
theorem exists_finiteGalois_splitAlgEquivFin
    (K A : Type u) [Field K] [CharZero K] [CommRing A] [Algebra K A]
    [Algebra.Etale K A] [Module.Finite K A]
    (n : ℕ) (hn : Module.finrank K A = n) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L)
      (_ : FiniteDimensional K L) (_ : IsGalois K L),
      Nonempty ((L ⊗[K] A) ≃ₐ[L] (Fin n → L)) := by
  have hrank : Module.rankAtStalk (R := K) A = n := by
    simpa [Module.rankAtStalk_eq_finrank_of_free, hn]
  obtain ⟨T, hTcomm, hTalg, hTff, hTfin, hTetale, hsplitT⟩ :=
    Algebra.IsFiniteSplit.exists_tensorProduct_of_etale hrank
  letI : CommRing T := hTcomm
  letI : Algebra K T := hTalg
  letI : Module.FaithfullyFlat K T := hTff
  letI : Module.Finite K T := hTfin
  letI : Algebra.Etale K T := hTetale
  letI : Algebra.IsFiniteSplit T (T ⊗[K] A) := hsplitT
  letI : Nontrivial T := (FaithfulSMul.algebraMap_injective K T).nontrivial
  obtain ⟨M, hM⟩ := Ideal.exists_maximal T
  let E : Type u := T ⧸ M
  letI : Field E := @Ideal.Quotient.field T _ M hM
  letI : Algebra T E := inferInstance
  letI : Algebra K E := inferInstance
  letI : IsScalarTower K T E := inferInstance
  letI : Module.Finite T E := Module.Finite.quotient T M
  letI : Module.Finite K E := Module.Finite.trans T E
  have hsplitE : Algebra.IsFiniteSplit E (E ⊗[K] A) := by
    letI : Algebra.IsFiniteSplit E (E ⊗[T] (T ⊗[K] A)) := inferInstance
    exact Algebra.IsFiniteSplit.of_algEquiv
      (Algebra.TensorProduct.cancelBaseChange K T E E A)
  let Omega : Type u := AlgebraicClosure K
  letI : Field Omega := inferInstanceAs (Field (AlgebraicClosure K))
  letI : Algebra K Omega := inferInstanceAs (Algebra K (AlgebraicClosure K))
  let emb : E →ₐ[K] Omega := IsAlgClosed.lift
  letI : Algebra E Omega := emb.toRingHom.toAlgebra
  letI : IsScalarTower K E Omega := by
    apply IsScalarTower.of_algebraMap_eq
    intro r
    exact (emb.commutes r).symm
  let L : Type u := IntermediateField.normalClosure K E Omega
  letI : Field L := inferInstanceAs
    (Field (IntermediateField.normalClosure K E Omega))
  letI : Algebra K L := inferInstanceAs
    (Algebra K (IntermediateField.normalClosure K E Omega))
  letI : Algebra E L := inferInstanceAs
    (Algebra E (IntermediateField.normalClosure K E Omega))
  letI : IsScalarTower K E L := inferInstanceAs
    (IsScalarTower K E (IntermediateField.normalClosure K E Omega))
  letI : FiniteDimensional K L := inferInstanceAs
    (FiniteDimensional K (IntermediateField.normalClosure K E Omega))
  letI : IsGalois K L := inferInstanceAs
    (IsGalois K (IntermediateField.normalClosure K E Omega))
  letI : Algebra.IsFiniteSplit E (E ⊗[K] A) := hsplitE
  letI : Algebra.IsFiniteSplit L (L ⊗[E] (E ⊗[K] A)) := inferInstance
  have hsplitL : Algebra.IsFiniteSplit L (L ⊗[K] A) :=
    Algebra.IsFiniteSplit.of_algEquiv
      (Algebra.TensorProduct.cancelBaseChange K E L L A)
  letI : Algebra.IsFiniteSplit L (L ⊗[K] A) := hsplitL
  exact ⟨L, inferInstance, inferInstance, inferInstance, inferInstance,
    nonempty_finiteSplitAlgEquivFin K A L n hn⟩

end AllCharacteristics
