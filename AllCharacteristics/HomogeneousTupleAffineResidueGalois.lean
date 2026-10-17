import AllCharacteristics.AffineSchemeActionSectionResidue
import AllCharacteristics.HomogeneousTupleAffineGaloisLift

/-!
# Galois residue lifts of rational unordered homogeneous tuples

Inside the common affine quotient chart supplied by the ordered lift, take
the prime determined by the ordered field-valued point.  Its residue field
is a finite Galois extension of the original ground field.  This is the
minimal splitting field attached to the chosen ordered tuple point and is
the field used for the coordinate-orbit multiplicity calculation.
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

/-- The local ordered lift has a prime whose residue field is finite Galois
over the original ground field. -/
def IsAffineTupleResidueGaloisLift
    {L : Type u} [Field L] [Algebra K L]
    (U : (scheme I).affineOpens)
    (aU : Spec (.of L) ⟶
      (orderedFamilyCommonOpen (toBase I) U.val n).toScheme)
    (cU : Spec (.of K) ⟶ commonOpenTupleQuotient (toBase I) U.val n) : Prop :=
  let X := (orderedFamilyCommonOpen (toBase I) U.val n).toScheme
  letI : IsAffine X :=
    isAffineOpen_orderedFamilyCommonOpen (toBase I) U.val n U.property
  let G := Equiv.Perm (Fin n)
  let rho := commonOpenRightAction (toBase I) U.val n
  let hOne := commonOpenRightAction_one (toBase I) U.val n
  let hMul := commonOpenRightAction_mul (toBase I) U.val n
  let fU := (orderedFamilyCommonOpen (toBase I) U.val n).ι ≫
    (orderedFamilyPowerOver (toBase I) n).hom
  let hf := commonOpenRightAction_toBase (toBase I) U.val n
  let q : PrimeSpectrum Γ(X, ⊤) :=
    X.isoSpec.hom (aU (IsLocalRing.closedPoint L))
  Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ cU =
      aU ≫ commonOpenTupleQuotientMap (toBase I) U.val n U.property ∧
    cU ≫ commonOpenTupleQuotientToBase (toBase I) U.val n = 𝟙 _ ∧
    ∃ hq : affineSchemeSectionQuotientPrime
        G rho hOne hMul fU hf q = cU (IsLocalRing.closedPoint K),
      ∃ alg : Algebra K q.asIdeal.ResidueField,
        @Module.Finite K q.asIdeal.ResidueField _ _ alg.toModule ∧
        @IsGalois K _ q.asIdeal.ResidueField _ alg

/-- Every rational point of the full unordered tuple quotient admits a local
ordered lift whose canonical prime residue field is finite Galois over the
ground field. -/
theorem tupleQuotient_exists_affineResidueGaloisLift
    (c : Spec (.of K) ⟶ tupleQuotient I n)
    (hc : c ≫ tupleQuotientToBase I n = 𝟙 _) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L)
      (_ : FiniteDimensional K L) (_ : IsGalois K L)
      (U : (scheme I).affineOpens)
      (aU : Spec (.of L) ⟶
        (orderedFamilyCommonOpen (toBase I) U.val n).toScheme)
      (cU : Spec (.of K) ⟶ commonOpenTupleQuotient (toBase I) U.val n),
      IsAffineTupleResidueGaloisLift I n U aU cU := by
  obtain ⟨L, _, _, _, _, U, aU, cU, -, hlocal, hcUbase⟩ :=
    tupleQuotient_exists_finiteGalois_affineChartLift I n c hc
  refine ⟨L, inferInstance, inferInstance, inferInstance, inferInstance,
    U, aU, cU, ?_⟩
  let X := (orderedFamilyCommonOpen (toBase I) U.val n).toScheme
  letI : IsAffine X :=
    isAffineOpen_orderedFamilyCommonOpen (toBase I) U.val n U.property
  let G := Equiv.Perm (Fin n)
  let rho := commonOpenRightAction (toBase I) U.val n
  let hOne := commonOpenRightAction_one (toBase I) U.val n
  let hMul := commonOpenRightAction_mul (toBase I) U.val n
  let fU := (orderedFamilyCommonOpen (toBase I) U.val n).ι ≫
    (orderedFamilyPowerOver (toBase I) n).hom
  let hf := commonOpenRightAction_toBase (toBase I) U.val n
  let q : PrimeSpectrum Γ(X, ⊤) :=
    X.isoSpec.hom (aU (IsLocalRing.closedPoint L))
  change
    (Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ cU =
      aU ≫ commonOpenTupleQuotientMap (toBase I) U.val n U.property) ∧
    (cU ≫ commonOpenTupleQuotientToBase (toBase I) U.val n = 𝟙 _) ∧
    ∃ hq : affineSchemeSectionQuotientPrime
        G rho hOne hMul fU hf q = cU (IsLocalRing.closedPoint K),
      ∃ alg : Algebra K q.asIdeal.ResidueField,
        @Module.Finite K q.asIdeal.ResidueField _ _ alg.toModule ∧
        @IsGalois K _ q.asIdeal.ResidueField _ alg
  refine ⟨hlocal, hcUbase, ?_⟩
  have hp := congrArg
    (fun m : Spec (.of L) ⟶ commonOpenTupleQuotient (toBase I) U.val n ↦
      m (IsLocalRing.closedPoint L)) hlocal
  have hpi : Spec.map (CommRingCat.ofHom (algebraMap K L))
      (IsLocalRing.closedPoint L) = IsLocalRing.closedPoint K :=
    Subsingleton.elim _ _
  change cU (Spec.map (CommRingCat.ofHom (algebraMap K L))
      (IsLocalRing.closedPoint L)) =
    commonOpenTupleQuotientMap (toBase I) U.val n U.property
      (aU (IsLocalRing.closedPoint L)) at hp
  rw [hpi] at hp
  have hq : affineSchemeSectionQuotientPrime
      G rho hOne hMul fU hf q = cU (IsLocalRing.closedPoint K) := by
    change commonOpenTupleQuotientMap (toBase I) U.val n U.property
      (aU (IsLocalRing.closedPoint L)) = cU (IsLocalRing.closedPoint K)
    exact hp.symm
  refine ⟨hq, ?_⟩
  let alg : Algebra K q.asIdeal.ResidueField :=
    affineSchemeSectionPointResidueAlgebra
      G rho hOne hMul fU hf cU hcUbase q hq
  refine ⟨alg, ?_, ?_⟩
  · exact affineSchemeSectionPointResidue_moduleFinite
      G rho hOne hMul fU hf cU hcUbase q hq
  · exact affineSchemeSectionPointResidue_isGalois
      G rho hOne hMul fU hf cU hcUbase q hq

end HomogeneousProjective
end AllCharacteristics
