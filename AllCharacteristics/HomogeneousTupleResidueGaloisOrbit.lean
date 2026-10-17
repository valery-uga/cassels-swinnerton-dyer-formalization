import AllCharacteristics.AffineSchemeActionSectionResidueOrbit
import AllCharacteristics.HomogeneousTupleAffineResidueGalois

/-!
# Galois permutation of a homogeneous tuple residue point

The canonical residue point above a rational local unordered-tuple point is
finite Galois over the ground field.  Every automorphism of that extension
permutes its ordered projective coordinates.  Repetitions are allowed, so
this applies to the full tuple quotient rather than only the configuration
open.
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

/-- The canonical residue-field point of a prime in a common affine tuple
chart.  The chart's affineness proof is installed internally so this point
can be used in theorem statements. -/
noncomputable def affineTuplePrimeResiduePoint
    (U : (scheme I).affineOpens)
    (q : PrimeSpectrum
      Γ((orderedFamilyCommonOpen (toBase I) U.val n).toScheme, ⊤)) :
    Spec (.of q.asIdeal.ResidueField) ⟶
      (orderedFamilyCommonOpen (toBase I) U.val n).toScheme := by
  letI : IsAffine
      (orderedFamilyCommonOpen (toBase I) U.val n).toScheme :=
    isAffineOpen_orderedFamilyCommonOpen (toBase I) U.val n U.property
  exact affinePrimeResiduePoint q

/-- A prime in the ordered affine chart lies above the closed point selected
by a rational point of the local unordered quotient. -/
def IsAffineTupleQuotientPrime
    (U : (scheme I).affineOpens)
    (cU : Spec (.of K) ⟶ commonOpenTupleQuotient (toBase I) U.val n)
    (q : PrimeSpectrum
      Γ((orderedFamilyCommonOpen (toBase I) U.val n).toScheme, ⊤)) : Prop :=
  affineSchemeSectionQuotientPrime
      (Equiv.Perm (Fin n))
      (commonOpenRightAction (toBase I) U.val n)
      (commonOpenRightAction_one (toBase I) U.val n)
      (commonOpenRightAction_mul (toBase I) U.val n)
      ((orderedFamilyCommonOpen (toBase I) U.val n).ι ≫
        (orderedFamilyPowerOver (toBase I) n).hom)
      (commonOpenRightAction_toBase (toBase I) U.val n) q =
    cU (IsLocalRing.closedPoint K)

/-- The canonical ground-field algebra on the residue field of a tuple-chart
prime above a rational quotient point. -/
@[instance_reducible]
noncomputable def affineTupleSectionPointResidueAlgebra
    (U : (scheme I).affineOpens)
    (cU : Spec (.of K) ⟶ commonOpenTupleQuotient (toBase I) U.val n)
    (hcU : cU ≫ commonOpenTupleQuotientToBase (toBase I) U.val n = 𝟙 _)
    (q : PrimeSpectrum
      Γ((orderedFamilyCommonOpen (toBase I) U.val n).toScheme, ⊤))
    (hq : IsAffineTupleQuotientPrime I n U cU q) :
    Algebra K q.asIdeal.ResidueField := by
  letI : IsAffine
      (orderedFamilyCommonOpen (toBase I) U.val n).toScheme :=
    isAffineOpen_orderedFamilyCommonOpen (toBase I) U.val n U.property
  exact affineSchemeSectionPointResidueAlgebra
    (Equiv.Perm (Fin n))
    (commonOpenRightAction (toBase I) U.val n)
    (commonOpenRightAction_one (toBase I) U.val n)
    (commonOpenRightAction_mul (toBase I) U.val n)
    ((orderedFamilyCommonOpen (toBase I) U.val n).ι ≫
      (orderedFamilyPowerOver (toBase I) n).hom)
    (commonOpenRightAction_toBase (toBase I) U.val n)
    cU hcU q hq

/-- The canonical residue point in a common affine tuple chart is a point
over the original ground field. -/
theorem affineTupleResiduePoint_toBase
    (U : (scheme I).affineOpens)
    (cU : Spec (.of K) ⟶ commonOpenTupleQuotient (toBase I) U.val n)
    (hcU : cU ≫ commonOpenTupleQuotientToBase (toBase I) U.val n = 𝟙 _)
    (q : PrimeSpectrum
      Γ((orderedFamilyCommonOpen (toBase I) U.val n).toScheme, ⊤))
    (hq : IsAffineTupleQuotientPrime I n U cU q) :
    letI := affineTupleSectionPointResidueAlgebra I n U cU hcU q hq
    Spec.map (CommRingCat.ofHom
        (algebraMap K q.asIdeal.ResidueField)) =
      affineTuplePrimeResiduePoint I n U q ≫
        (orderedFamilyCommonOpen (toBase I) U.val n).ι ≫
        (orderedFamilyPowerOver (toBase I) n).hom := by
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
  letI : Algebra K q.asIdeal.ResidueField :=
    affineTupleSectionPointResidueAlgebra I n U cU hcU q hq
  change affineSchemeSectionQuotientPrime
      G rho hOne hMul fU hf q = cU (IsLocalRing.closedPoint K) at hq
  have hbase := affineSchemeSectionPointResidue_toBase
    G rho hOne hMul fU hf cU hcU q hq
  change Spec.map (CommRingCat.ofHom
      (algebraMap K q.asIdeal.ResidueField)) =
    affineTuplePrimeResiduePoint I n U q ≫
      (orderedFamilyCommonOpen (toBase I) U.val n).ι ≫
      (orderedFamilyPowerOver (toBase I) n).hom at hbase
  exact hbase

/-- Every coordinate of the canonical ordered residue point lies in the
original projective fiber over its finite residue extension. -/
theorem affineTupleResidueCoordinate_toBase
    (U : (scheme I).affineOpens)
    (cU : Spec (.of K) ⟶ commonOpenTupleQuotient (toBase I) U.val n)
    (hcU : cU ≫ commonOpenTupleQuotientToBase (toBase I) U.val n = 𝟙 _)
    (q : PrimeSpectrum
      Γ((orderedFamilyCommonOpen (toBase I) U.val n).toScheme, ⊤))
    (hq : IsAffineTupleQuotientPrime I n U cU q)
    (i : Fin n) :
    letI := affineTupleSectionPointResidueAlgebra I n U cU hcU q hq
    affineTuplePrimeResiduePoint I n U q ≫
        (orderedFamilyCommonOpen (toBase I) U.val n).ι ≫
        (orderedFamilyCoordinate (toBase I) n i).left ≫ toBase I =
      Spec.map (CommRingCat.ofHom
        (algebraMap K q.asIdeal.ResidueField)) := by
  letI : Algebra K q.asIdeal.ResidueField :=
    affineTupleSectionPointResidueAlgebra I n U cU hcU q hq
  have hbase := affineTupleResiduePoint_toBase I n U cU hcU q hq
  have hw := (orderedFamilyCoordinate (toBase I) n i).w
  change (orderedFamilyCoordinate (toBase I) n i).left ≫ toBase I =
    (orderedFamilyPowerOver (toBase I) n).hom at hw
  calc
    affineTuplePrimeResiduePoint I n U q ≫
        (orderedFamilyCommonOpen (toBase I) U.val n).ι ≫
        (orderedFamilyCoordinate (toBase I) n i).left ≫ toBase I =
      affineTuplePrimeResiduePoint I n U q ≫
        (orderedFamilyCommonOpen (toBase I) U.val n).ι ≫
        (orderedFamilyPowerOver (toBase I) n).hom := by
          simpa only [Category.assoc] using congrArg
            (fun z ↦ affineTuplePrimeResiduePoint I n U q ≫
              (orderedFamilyCommonOpen (toBase I) U.val n).ι ≫ z) hw
    _ = Spec.map (CommRingCat.ofHom
          (algebraMap K q.asIdeal.ResidueField)) := hbase.symm

/-- Every ground-field automorphism of the local tuple residue extension
permutes the projective coordinates of its canonical ordered point. -/
theorem affineTupleResiduePoint_galoisCoordinate
    (U : (scheme I).affineOpens)
    (cU : Spec (.of K) ⟶ commonOpenTupleQuotient (toBase I) U.val n)
    (hcU : cU ≫ commonOpenTupleQuotientToBase (toBase I) U.val n = 𝟙 _)
    (q : PrimeSpectrum
      Γ((orderedFamilyCommonOpen (toBase I) U.val n).toScheme, ⊤))
    (hq : IsAffineTupleQuotientPrime I n U cU q)
    (g : @AlgEquiv K q.asIdeal.ResidueField q.asIdeal.ResidueField _ _ _
      (affineTupleSectionPointResidueAlgebra I n U cU hcU q hq)
      (affineTupleSectionPointResidueAlgebra I n U cU hcU q hq)) :
    ∃ e : Equiv.Perm (Fin n), ∀ i : Fin n,
      (Spec.map (CommRingCat.ofHom g.toRingHom) ≫
          affineTuplePrimeResiduePoint I n U q) ≫
          (orderedFamilyCommonOpen (toBase I) U.val n).ι ≫
          (orderedFamilyCoordinate (toBase I) n i).left =
        affineTuplePrimeResiduePoint I n U q ≫
          (orderedFamilyCommonOpen (toBase I) U.val n).ι ≫
          (orderedFamilyCoordinate (toBase I) n (e i)).left := by
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
  change affineSchemeSectionQuotientPrime
      G rho hOne hMul fU hf q = cU (IsLocalRing.closedPoint K) at hq
  obtain ⟨s, hs⟩ := affineSchemeSectionPointResidue_galoisOrbit
    G rho hOne hMul fU hf cU hcU q hq g
  refine ⟨s.val, fun i ↦ ?_⟩
  change (Spec.map (CommRingCat.ofHom g.toRingHom) ≫
      affinePrimeResiduePoint q) ≫
        (orderedFamilyCommonOpen (toBase I) U.val n).ι ≫
        (orderedFamilyCoordinate (toBase I) n i).left =
      affinePrimeResiduePoint q ≫
        (orderedFamilyCommonOpen (toBase I) U.val n).ι ≫
        (orderedFamilyCoordinate (toBase I) n (s.val i)).left
  have hpower := commonOpenRightAction_toPower
    (grading I) (toBase I) n U.val s.val
  change rho s.val ≫
      (orderedFamilyCommonOpen (toBase I) U.val n).ι =
    (orderedFamilyCommonOpen (toBase I) U.val n).ι ≫
      orderedFamilyRightAction (toBase I) n s.val at hpower
  have hcoord := orderedFamilyRightAction_coordinate
    (toBase I) n s.val i
  calc
    (Spec.map (CommRingCat.ofHom g.toRingHom) ≫
        affinePrimeResiduePoint q) ≫
          (orderedFamilyCommonOpen (toBase I) U.val n).ι ≫
          (orderedFamilyCoordinate (toBase I) n i).left =
        (affinePrimeResiduePoint q ≫ rho s.val) ≫
          (orderedFamilyCommonOpen (toBase I) U.val n).ι ≫
          (orderedFamilyCoordinate (toBase I) n i).left := by rw [hs]
    _ = affinePrimeResiduePoint q ≫
          (rho s.val ≫
            (orderedFamilyCommonOpen (toBase I) U.val n).ι) ≫
          (orderedFamilyCoordinate (toBase I) n i).left := by
        simp only [Category.assoc]
    _ = affinePrimeResiduePoint q ≫
          ((orderedFamilyCommonOpen (toBase I) U.val n).ι ≫
            orderedFamilyRightAction (toBase I) n s.val) ≫
          (orderedFamilyCoordinate (toBase I) n i).left := by rw [hpower]
    _ = affinePrimeResiduePoint q ≫
          (orderedFamilyCommonOpen (toBase I) U.val n).ι ≫
          (orderedFamilyCoordinate (toBase I) n (s.val i)).left := by
        simp only [Category.assoc, hcoord]

/-- The canonical ordered residue point above a rational local quotient point
has a finite Galois residue field, and its coordinates are permuted by every
ground-field automorphism. -/
def IsAffineTupleResidueGaloisOrbit
    (U : (scheme I).affineOpens)
    (cU : Spec (.of K) ⟶ commonOpenTupleQuotient (toBase I) U.val n)
    (hcU : cU ≫ commonOpenTupleQuotientToBase (toBase I) U.val n = 𝟙 _)
    (q : PrimeSpectrum
      Γ((orderedFamilyCommonOpen (toBase I) U.val n).toScheme, ⊤))
    (hq : IsAffineTupleQuotientPrime I n U cU q) : Prop :=
  let alg := affineTupleSectionPointResidueAlgebra I n U cU hcU q hq
  @Module.Finite K q.asIdeal.ResidueField _ _ alg.toModule ∧
    @IsGalois K _ q.asIdeal.ResidueField _ alg ∧
    ∀ g : @AlgEquiv K q.asIdeal.ResidueField q.asIdeal.ResidueField _ _ _ alg alg,
      ∃ e : Equiv.Perm (Fin n), ∀ i : Fin n,
        (Spec.map (CommRingCat.ofHom g.toRingHom) ≫
            affineTuplePrimeResiduePoint I n U q) ≫
            (orderedFamilyCommonOpen (toBase I) U.val n).ι ≫
            (orderedFamilyCoordinate (toBase I) n i).left =
          affineTuplePrimeResiduePoint I n U q ≫
            (orderedFamilyCommonOpen (toBase I) U.val n).ι ≫
            (orderedFamilyCoordinate (toBase I) n (e i)).left

/-- Every rational point of the full unordered tuple quotient is represented
in a common affine chart by a canonical finite-Galois residue point whose
ordered coordinates form a Galois-stable multiset.  The local quotient point
is retained together with its equality to the original global point. -/
theorem tupleQuotient_exists_residueGaloisCoordinateOrbit
    (c : Spec (.of K) ⟶ tupleQuotient I n)
    (hc : c ≫ tupleQuotientToBase I n = 𝟙 _) :
    ∃ (U : (scheme I).affineOpens)
      (cU : Spec (.of K) ⟶ commonOpenTupleQuotient (toBase I) U.val n)
      (q : PrimeSpectrum
        Γ((orderedFamilyCommonOpen (toBase I) U.val n).toScheme, ⊤))
      (hcU : cU ≫ commonOpenTupleQuotientToBase (toBase I) U.val n = 𝟙 _)
      (hq : IsAffineTupleQuotientPrime I n U cU q),
      cU ≫ tupleQuotientAffineChart I n U = c ∧
      IsAffineTupleResidueGaloisOrbit I n U cU hcU q hq := by
  obtain ⟨L, _, _, _, _, U, aU, cU, hcUglobal, hlocal, hcUbase⟩ :=
    tupleQuotient_exists_finiteGalois_affineChartLift I n c hc
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
  have hq' : IsAffineTupleQuotientPrime I n U cU q := hq
  refine ⟨U, cU, q, hcUbase, hq', hcUglobal, ?_⟩
  change
    @Module.Finite K q.asIdeal.ResidueField _ _
        (affineTupleSectionPointResidueAlgebra
          I n U cU hcUbase q hq').toModule ∧
      @IsGalois K _ q.asIdeal.ResidueField _
        (affineTupleSectionPointResidueAlgebra
          I n U cU hcUbase q hq') ∧
      ∀ g : @AlgEquiv K q.asIdeal.ResidueField q.asIdeal.ResidueField _ _ _
          (affineTupleSectionPointResidueAlgebra
            I n U cU hcUbase q hq')
          (affineTupleSectionPointResidueAlgebra
            I n U cU hcUbase q hq'),
        ∃ e : Equiv.Perm (Fin n), ∀ i : Fin n,
          (Spec.map (CommRingCat.ofHom g.toRingHom) ≫
              affineTuplePrimeResiduePoint I n U q) ≫
              (orderedFamilyCommonOpen (toBase I) U.val n).ι ≫
              (orderedFamilyCoordinate (toBase I) n i).left =
            affineTuplePrimeResiduePoint I n U q ≫
              (orderedFamilyCommonOpen (toBase I) U.val n).ι ≫
              (orderedFamilyCoordinate (toBase I) n (e i)).left
  refine ⟨?_, ?_, ?_⟩
  · change @Module.Finite K q.asIdeal.ResidueField _ _
      (affineSchemeSectionPointResidueAlgebra
        G rho hOne hMul fU hf cU hcUbase q hq).toModule
    exact affineSchemeSectionPointResidue_moduleFinite
      G rho hOne hMul fU hf cU hcUbase q hq
  · change @IsGalois K _ q.asIdeal.ResidueField _
      (affineSchemeSectionPointResidueAlgebra
        G rho hOne hMul fU hf cU hcUbase q hq)
    exact affineSchemeSectionPointResidue_isGalois
      G rho hOne hMul fU hf cU hcUbase q hq
  · intro g
    exact affineTupleResiduePoint_galoisCoordinate
      I n U cU hcUbase q hq' g

end HomogeneousProjective
end AllCharacteristics
