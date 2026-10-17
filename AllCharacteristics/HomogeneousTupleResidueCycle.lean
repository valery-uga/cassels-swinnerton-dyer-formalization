import AllCharacteristics.FiniteGaloisTupleCycle
import AllCharacteristics.HomogeneousTupleResidueGaloisOrbit

/-!
# Effective cycles from rational unordered projective tuples

The canonical residue point above a rational full-tuple quotient point has a
finite Galois residue field, and its ordered coordinates are permuted by every
Galois automorphism.  Grouping these coordinates by closed support gives an
effective zero-cycle over the original field whose degree is the tuple
length.  Coordinate collisions contribute multiplicity rather than being
discarded.
-/

open AlgebraicGeometry CategoryTheory

namespace AllCharacteristics
namespace HomogeneousProjective

universe u

variable {K : Type u} [Field K] [CharZero K]
variable {sigma : Type} [Finite sigma]
attribute [local instance] MvPolynomial.gradedAlgebra
variable (I : HomogeneousIdeal
  (MvPolynomial.homogeneousSubmodule sigma K)) (n : ℕ)

/-- The `i`-th projective coordinate of the canonical affine-chart residue
point. -/
noncomputable def affineTupleResidueCoordinatePoint
    (U : (scheme I).affineOpens)
    (q : PrimeSpectrum
      Γ((orderedFamilyCommonOpen (toBase I) U.val n).toScheme, ⊤))
    (i : Fin n) :
    Spec (.of q.asIdeal.ResidueField) ⟶ scheme I :=
  affineTuplePrimeResiduePoint I n U q ≫
    (orderedFamilyCommonOpen (toBase I) U.val n).ι ≫
    (orderedFamilyCoordinate (toBase I) n i).left

/-- The effective zero-cycle carried by the coordinates of the canonical
finite-Galois residue point in a common affine tuple chart. -/
noncomputable def affineTupleResidueCycle
    (U : (scheme I).affineOpens)
    (cU : Spec (.of K) ⟶ commonOpenTupleQuotient (toBase I) U.val n)
    (hcU : cU ≫ commonOpenTupleQuotientToBase (toBase I) U.val n = 𝟙 _)
    (q : PrimeSpectrum
      Γ((orderedFamilyCommonOpen (toBase I) U.val n).toScheme, ⊤))
    (hq : IsAffineTupleQuotientPrime I n U cU q)
    (horbit : IsAffineTupleResidueGaloisOrbit I n U cU hcU q hq) :
    EffectiveZeroCycle (scheme I) := by
  letI : Algebra K q.asIdeal.ResidueField :=
    affineTupleSectionPointResidueAlgebra I n U cU hcU q hq
  letI : Module.Finite K q.asIdeal.ResidueField := horbit.1
  letI : IsGalois K q.asIdeal.ResidueField := horbit.2.1
  let a : Fin n → (Spec (.of q.asIdeal.ResidueField) ⟶ scheme I) :=
    affineTupleResidueCoordinatePoint I n U q
  have ha : ∀ i, a i ≫ toBase I =
      Spec.map (CommRingCat.ofHom
        (algebraMap K q.asIdeal.ResidueField)) := by
    intro i
    exact affineTupleResidueCoordinate_toBase I n U cU hcU q hq i
  exact finiteGaloisTupleCycle (toBase I) a ha

/-- The coordinate cycle of the canonical residue point has degree exactly
the tuple length. -/
theorem affineTupleResidueCycle_degree
    (U : (scheme I).affineOpens)
    (cU : Spec (.of K) ⟶ commonOpenTupleQuotient (toBase I) U.val n)
    (hcU : cU ≫ commonOpenTupleQuotientToBase (toBase I) U.val n = 𝟙 _)
    (q : PrimeSpectrum
      Γ((orderedFamilyCommonOpen (toBase I) U.val n).toScheme, ⊤))
    (hq : IsAffineTupleQuotientPrime I n U cU q)
    (horbit : IsAffineTupleResidueGaloisOrbit I n U cU hcU q hq) :
    EffectiveZeroCycle.degree (toBase I)
      (affineTupleResidueCycle I n U cU hcU q hq horbit) = n := by
  letI : Algebra K q.asIdeal.ResidueField :=
    affineTupleSectionPointResidueAlgebra I n U cU hcU q hq
  letI : Module.Finite K q.asIdeal.ResidueField := horbit.1
  letI : IsGalois K q.asIdeal.ResidueField := horbit.2.1
  let a : Fin n → (Spec (.of q.asIdeal.ResidueField) ⟶ scheme I) :=
    affineTupleResidueCoordinatePoint I n U q
  have ha : ∀ i, a i ≫ toBase I =
      Spec.map (CommRingCat.ofHom
        (algebraMap K q.asIdeal.ResidueField)) := by
    intro i
    exact affineTupleResidueCoordinate_toBase I n U cU hcU q hq i
  have hstable : ∀ g : q.asIdeal.ResidueField ≃ₐ[K]
      q.asIdeal.ResidueField, ∃ e : Equiv.Perm (Fin n),
      ∀ i, Spec.map (CommRingCat.ofHom g.toRingHom) ≫ a i = a (e i) := by
    intro g
    exact horbit.2.2 g
  exact finiteGaloisTupleCycle_degree (toBase I) a ha hstable

/-- Every rational point of the full unordered projective tuple quotient
represents an effective zero-cycle of the same degree on the original
projective scheme. -/
theorem tupleQuotient_exists_effectiveZeroCycle
    (c : Spec (.of K) ⟶ tupleQuotient I n)
    (hc : c ≫ tupleQuotientToBase I n = 𝟙 _) :
    ∃ z : EffectiveZeroCycle (scheme I),
      EffectiveZeroCycle.degree (toBase I) z = n := by
  obtain ⟨U, cU, q, hcU, hq, -, horbit⟩ :=
    tupleQuotient_exists_residueGaloisCoordinateOrbit I n c hc
  exact ⟨affineTupleResidueCycle I n U cU hcU q hq horbit,
    affineTupleResidueCycle_degree I n U cU hcU q hq horbit⟩

end HomogeneousProjective
end AllCharacteristics
