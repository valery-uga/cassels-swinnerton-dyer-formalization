import AllCharacteristics.PresentedRootReduction

/-!
# Lifting a simple finite residue-field extension

A field extension with a power basis lifts to a finite free complete local
algebra over the given complete local coefficient ring. The reduction map is
surjective and respects the original coefficient map. Its rank is the full
field-extension degree, without any separability hypothesis.
-/

open IsLocalRing Polynomial
namespace AllCharacteristics
universe u v w

/-- A power basis identifies its field with the root algebra of its minimal
polynomial. This also applies to inseparable minimal polynomials. -/
noncomputable def powerBasisMinpolyEquiv
    {k : Type v} {L : Type w} [Field k] [Field L] [Algebra k L]
    (pb : PowerBasis k L) : AdjoinRoot (minpoly k pb.gen) ≃ₐ[k] L :=
  AdjoinRoot.equiv' (minpoly k pb.gen) pb
    (by rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]) (minpoly.aeval k pb.gen)

/-- A simple finite extension of a presented residue field has a complete
local finite free lift with the exact extension degree and coefficient map. -/
theorem exists_complete_local_lift_of_powerBasis
    {R : Type u} {k : Type v} {L : Type w}
    [CommRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R]
    [Field k] [Field L] [Algebra k L]
    (b : R →+* k) (hb : Function.Surjective b) (pb : PowerBasis k L) :
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra R A) (_ : IsLocalRing A)
      (_ : Module.Free R A) (_ : Module.Finite R A)
      (_ : IsAdicComplete (maximalIdeal A) A) (c : A →+* L),
      Function.Surjective c ∧
      (∀ r : R, c (algebraMap R A r) = algebraMap k L (b r)) ∧
      Module.finrank R A = Module.finrank k L ∧
      maximalIdeal A = (maximalIdeal R).map (algebraMap R A) := by
  obtain ⟨q, hqp, hd, hq⟩ := exists_monic_polynomial_lift b hb
    (minpoly k pb.gen) (minpoly.monic pb.isIntegral_gen)
  have hir : Irreducible (q.map (residue R)) :=
    irreducible_residue_of_surjective_reduction b hb q
      (hqp.symm ▸ minpoly.irreducible pb.isIntegral_gen)
  let A := AdjoinRoot q
  let : IsLocalRing A := adjoinRoot_isLocalRing_of_irreducible_reduction q hq hir
  let : Module.Free R A := hq.free_adjoinRoot
  let : Module.Finite R A := hq.finite_adjoinRoot
  let : IsAdicComplete (maximalIdeal A) A :=
    adjoinRoot_isAdicComplete_maximalIdeal q hq hir
  let e : AdjoinRoot (q.map b) ≃ₐ[k] L :=
    (AdjoinRoot.algEquivOfEq k _ _ hqp).trans (powerBasisMinpolyEquiv pb)
  let c : A →+* L := e.toRingEquiv.toRingHom.comp (adjoinRootReductionTo b hb q)
  refine ⟨A, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, c, e.surjective.comp (adjoinRootReductionTo_surjective b hb q), ?_, ?_,
    adjoinRoot_maximalIdeal_eq_extended q hq hir⟩
  · intro r
    change e (adjoinRootReductionTo b hb q (algebraMap R (AdjoinRoot q) r)) = _
    rw [adjoinRootReductionTo_algebraMap]
    exact e.commutes (b r)
  · exact (AdjoinRoot.powerBasis' hq).finrank.trans
      (hd.trans (pb.natDegree_minpoly.trans pb.finrank.symm))

end AllCharacteristics
