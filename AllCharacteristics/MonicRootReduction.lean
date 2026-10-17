import AllCharacteristics.MonicRootCompletion

/-!
# The reduction map of a lifted monic root algebra

The quotient comparison supplies a surjective reduction homomorphism. When the
residue polynomial is irreducible over a complete local base, its kernel is the
actual maximal ideal. The resulting residue-field equivalence retains the
coefficient map and the entire polynomial degree, including inseparable degree.
-/

open Polynomial IsLocalRing
namespace AllCharacteristics
universe u

/-- Reduction of a root algebra modulo the coefficient ring's maximal ideal. -/
noncomputable def adjoinRootReduction
    {R : Type u} [CommRing R] [IsLocalRing R] (q : R[X]) :
    AdjoinRoot q →+* AdjoinRoot (q.map (residue R)) :=
  (AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot (maximalIdeal R) q).toRingHom.comp
    (Ideal.Quotient.mk ((maximalIdeal R).map (algebraMap R (AdjoinRoot q))))

/-- Every residue-root-algebra element has a lift. -/
theorem adjoinRootReduction_surjective
    {R : Type u} [CommRing R] [IsLocalRing R] (q : R[X]) :
    Function.Surjective (adjoinRootReduction q) :=
  (AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot (maximalIdeal R) q).surjective.comp
    Ideal.Quotient.mk_surjective

/-- The reduction kernel is exactly the extended coefficient ideal. -/
theorem adjoinRootReduction_ker
    {R : Type u} [CommRing R] [IsLocalRing R] (q : R[X]) :
    RingHom.ker (adjoinRootReduction q) =
      (maximalIdeal R).map (algebraMap R (AdjoinRoot q)) := by
  ext a
  change (AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot (maximalIdeal R) q)
    (Ideal.Quotient.mk _ a) = 0 ↔ _
  rw [map_eq_zero_iff _
    (AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot (maximalIdeal R) q).injective,
    Ideal.Quotient.eq_zero_iff_mem]
  rfl

/-- Reduction commutes with the coefficient homomorphism. -/
theorem adjoinRootReduction_algebraMap
    {R : Type u} [CommRing R] [IsLocalRing R] (q : R[X]) (r : R) :
    adjoinRootReduction q (algebraMap R (AdjoinRoot q) r) =
      algebraMap (ResidueField R) (AdjoinRoot (q.map (residue R))) (residue R r) := by
  change (AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot (maximalIdeal R) q)
    (Ideal.Quotient.mk _ (AdjoinRoot.mk q (C r))) = _
  rw [AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot_mk_of, Polynomial.map_C]
  rfl

/-- The distinguished lifted root reduces to the distinguished residue root. -/
theorem adjoinRootReduction_root
    {R : Type u} [CommRing R] [IsLocalRing R] (q : R[X]) :
    adjoinRootReduction q (AdjoinRoot.root q) =
      AdjoinRoot.root (q.map (residue R)) := by
  change (AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot (maximalIdeal R) q)
    (Ideal.Quotient.mk _ (AdjoinRoot.mk q X)) = _
  rw [AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot_mk_of, Polynomial.map_X]
  rfl

/-- For an irreducible reduction, the reduction kernel is the local algebra's
actual maximal ideal. -/
theorem adjoinRootReduction_ker_eq_maximalIdeal
    {R : Type u} [CommRing R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R]
    (q : R[X]) (hq : q.Monic) (hi : Irreducible (q.map (residue R))) :
    letI := adjoinRoot_isLocalRing_of_irreducible_reduction q hq hi
    RingHom.ker (adjoinRootReduction q) = maximalIdeal (AdjoinRoot q) := by
  let := adjoinRoot_isLocalRing_of_irreducible_reduction q hq hi
  rw [adjoinRoot_maximalIdeal_eq_extended q hq hi, adjoinRootReduction_ker]

/-- The actual residue field of the lifted root algebra is the root algebra
of the residue polynomial. -/
noncomputable def adjoinRootResidueEquiv
    {R : Type u} [CommRing R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R]
    (q : R[X]) (hq : q.Monic) (hi : Irreducible (q.map (residue R))) :
    letI := adjoinRoot_isLocalRing_of_irreducible_reduction q hq hi
    ResidueField (AdjoinRoot q) ≃+* AdjoinRoot (q.map (residue R)) := by
  let := adjoinRoot_isLocalRing_of_irreducible_reduction q hq hi
  exact (Ideal.quotEquivOfEq (adjoinRoot_maximalIdeal_eq_extended q hq hi)).trans
    (AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot (maximalIdeal R) q)

/-- The residue-field equivalence identifies the intrinsic residue map with
the constructed reduction map. -/
theorem adjoinRootResidueEquiv_residue
    {R : Type u} [CommRing R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R]
    (q : R[X]) (hq : q.Monic) (hi : Irreducible (q.map (residue R))) (a : AdjoinRoot q) :
    letI := adjoinRoot_isLocalRing_of_irreducible_reduction q hq hi
    adjoinRootResidueEquiv q hq hi (residue (AdjoinRoot q) a) = adjoinRootReduction q a := by
  let := adjoinRoot_isLocalRing_of_irreducible_reduction q hq hi
  exact congrArg (AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot (maximalIdeal R) q)
    (Ideal.quotEquivOfEq_mk (adjoinRoot_maximalIdeal_eq_extended q hq hi) a)

/-- The lifted free rank equals the residue equation's full degree. -/
theorem monic_adjoinRoot_finrank_eq_residue_degree
    {R : Type u} [CommRing R] [IsLocalRing R] (q : R[X]) (hq : q.Monic) :
    Module.finrank R (AdjoinRoot q) = (q.map (residue R)).natDegree := by
  rw [hq.natDegree_map]
  exact (AdjoinRoot.powerBasis' hq).finrank

end AllCharacteristics
