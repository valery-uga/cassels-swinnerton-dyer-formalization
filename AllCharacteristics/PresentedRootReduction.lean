import AllCharacteristics.MonicRootReduction
import AllCharacteristics.SurjectiveResiduePresentation

/-!
# Reduction into a prescribed residue root algebra

The coefficient field is allowed to be an arbitrary presentation of the
residue field. This permits iteration through a tower of simple extensions.
-/

open IsLocalRing Polynomial
namespace AllCharacteristics
universe u v

/-- Reduction of a root algebra through a chosen surjective field-valued map. -/
noncomputable def adjoinRootReductionTo
    {R : Type u} {k : Type v} [CommRing R] [IsLocalRing R] [Field k]
    (b : R →+* k) (hb : Function.Surjective b) (q : R[X]) :
    AdjoinRoot q →+* AdjoinRoot (q.map b) :=
  (AdjoinRoot.mapRingEquiv (residueEquivOfSurjective b hb)
    (q.map (residue R)) (q.map b)
    (Associated.of_eq (polynomial_map_residueEquivOfSurjective b hb q))).toRingHom.comp
      (adjoinRootReduction q)

/-- The prescribed reduction is surjective. -/
theorem adjoinRootReductionTo_surjective
    {R : Type u} {k : Type v} [CommRing R] [IsLocalRing R] [Field k]
    (b : R →+* k) (hb : Function.Surjective b) (q : R[X]) :
    Function.Surjective (adjoinRootReductionTo b hb q) :=
  (AdjoinRoot.mapRingEquiv (residueEquivOfSurjective b hb)
    (q.map (residue R)) (q.map b)
      (Associated.of_eq (polynomial_map_residueEquivOfSurjective b hb q))).surjective.comp
      (adjoinRootReduction_surjective q)

/-- The prescribed reduction has the same extended-ideal kernel. -/
theorem adjoinRootReductionTo_ker
    {R : Type u} {k : Type v} [CommRing R] [IsLocalRing R] [Field k]
    (b : R →+* k) (hb : Function.Surjective b) (q : R[X]) :
    RingHom.ker (adjoinRootReductionTo b hb q) =
      (maximalIdeal R).map (algebraMap R (AdjoinRoot q)) := by
  exact (RingHom.ker_comp_of_injective (adjoinRootReduction q)
    (AdjoinRoot.mapRingEquiv (residueEquivOfSurjective b hb)
      (q.map (residue R)) (q.map b)
      (Associated.of_eq (polynomial_map_residueEquivOfSurjective b hb q))).injective).trans
      (adjoinRootReduction_ker q)

/-- Coefficients reduce by the original chosen map. -/
theorem adjoinRootReductionTo_algebraMap
    {R : Type u} {k : Type v} [CommRing R] [IsLocalRing R] [Field k]
    (b : R →+* k) (hb : Function.Surjective b) (q : R[X]) (r : R) :
    adjoinRootReductionTo b hb q (algebraMap R (AdjoinRoot q) r) =
      algebraMap k (AdjoinRoot (q.map b)) (b r) := by
  change (AdjoinRoot.mapRingEquiv (residueEquivOfSurjective b hb)
    (q.map (residue R)) (q.map b)
      (Associated.of_eq (polynomial_map_residueEquivOfSurjective b hb q)))
    (adjoinRootReduction q (algebraMap R (AdjoinRoot q) r)) = _
  rw [adjoinRootReduction_algebraMap]
  change AdjoinRoot.map (residueEquivOfSurjective b hb).toRingHom
    (q.map (residue R)) (q.map b)
    (Associated.of_eq (polynomial_map_residueEquivOfSurjective b hb q)).symm.dvd
    (AdjoinRoot.of _ (residue R r)) = _
  rw [AdjoinRoot.map_of]
  exact congrArg (algebraMap k (AdjoinRoot (q.map b)))
    (residueEquivOfSurjective_residue b hb r)

end AllCharacteristics
