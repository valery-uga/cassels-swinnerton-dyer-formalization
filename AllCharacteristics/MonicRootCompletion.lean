import AllCharacteristics.FiniteFreeCompletion
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.Algebra.Field.Equiv

/-!
# Complete local root algebras lifting irreducible residue equations

A monic polynomial lifts through a surjective coefficient map without changing
its degree. Its root algebra has a finite power basis and is adically complete
when the base is complete. If the residue equation is irreducible, the lifted
root algebra is local and its maximal ideal is exactly the extended base ideal.
No separability or perfectness hypothesis is used.
-/

open Polynomial IsLocalRing
namespace AllCharacteristics
universe u v

/-- A monic polynomial lifts through a surjective coefficient map with its
degree and monicity preserved. -/
theorem exists_monic_polynomial_lift
    {R : Type u} {k : Type v} [CommRing R] [CommRing k]
    (b : R →+* k) (hb : Function.Surjective b) (p : k[X]) (hp : p.Monic) :
    ∃ q : R[X], q.map b = p ∧ q.natDegree = p.natDegree ∧ q.Monic := by
  apply Polynomial.lifts_and_natDegree_eq_and_monic _ hp
  exact Polynomial.map_surjective b hb p

/-- The root algebra of a monic polynomial is complete for the extended ideal
whenever the coefficient ring is complete. -/
theorem monic_adjoinRoot_isAdicComplete
    {R : Type u} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    (q : R[X]) (hq : q.Monic) :
    IsAdicComplete (I.map (algebraMap R (AdjoinRoot q))) (AdjoinRoot q) := by
  have := isAdicComplete_of_finite_basis I (AdjoinRoot.powerBasis' hq).basis
  exact (IsAdicComplete.map_algebraMap_iff I (AdjoinRoot q)).mpr inferInstance

/-- An irreducible residue equation makes the extended maximal ideal maximal
in the lifted root algebra. The residue polynomial may be inseparable. -/
theorem adjoinRoot_extended_maximalIdeal_isMaximal
    {R : Type u} [CommRing R] [IsLocalRing R]
    (q : R[X]) (hi : Irreducible (q.map (residue R))) :
    (Ideal.map (algebraMap R (AdjoinRoot q)) (maximalIdeal R)).IsMaximal := by
  let : Fact (Irreducible (q.map (residue R))) := ⟨hi⟩
  let e := AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot (maximalIdeal R) q
  apply Ideal.Quotient.maximal_of_isField
  exact e.toMulEquiv.isField (Field.toIsField (AdjoinRoot (q.map (residue R))))

/-- A monic polynomial with irreducible reduction over a complete local ring
defines a local root algebra. -/
theorem adjoinRoot_isLocalRing_of_irreducible_reduction
    {R : Type u} [CommRing R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R]
    (q : R[X]) (hq : q.Monic) (hi : Irreducible (q.map (residue R))) :
    IsLocalRing (AdjoinRoot q) := by
  let I := Ideal.map (algebraMap R (AdjoinRoot q)) (maximalIdeal R)
  have : I.IsMaximal := adjoinRoot_extended_maximalIdeal_isMaximal q hi
  have : IsAdicComplete I (AdjoinRoot q) := monic_adjoinRoot_isAdicComplete (maximalIdeal R) q hq
  exact isLocalRing_of_isAdicComplete_maximal I

/-- The maximal ideal of the lifted local root algebra is exactly the
extension of the coefficient ring's maximal ideal. -/
theorem adjoinRoot_maximalIdeal_eq_extended
    {R : Type u} [CommRing R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R]
    (q : R[X]) (hq : q.Monic) (hi : Irreducible (q.map (residue R))) :
    letI := adjoinRoot_isLocalRing_of_irreducible_reduction q hq hi
    maximalIdeal (AdjoinRoot q) = Ideal.map (algebraMap R (AdjoinRoot q)) (maximalIdeal R) := by
  let := adjoinRoot_isLocalRing_of_irreducible_reduction q hq hi
  exact (IsLocalRing.eq_maximalIdeal (adjoinRoot_extended_maximalIdeal_isMaximal q hi)).symm

/-- The lifted root algebra is complete with respect to its own maximal ideal. -/
theorem adjoinRoot_isAdicComplete_maximalIdeal
    {R : Type u} [CommRing R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R]
    (q : R[X]) (hq : q.Monic) (hi : Irreducible (q.map (residue R))) :
    letI := adjoinRoot_isLocalRing_of_irreducible_reduction q hq hi
    IsAdicComplete (maximalIdeal (AdjoinRoot q)) (AdjoinRoot q) := by
  let := adjoinRoot_isLocalRing_of_irreducible_reduction q hq hi
  rw [adjoinRoot_maximalIdeal_eq_extended q hq hi]
  exact monic_adjoinRoot_isAdicComplete (maximalIdeal R) q hq

end AllCharacteristics
