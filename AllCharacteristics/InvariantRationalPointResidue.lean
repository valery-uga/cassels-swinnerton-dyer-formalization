import AllCharacteristics.GaloisBaseRingEquiv
import AllCharacteristics.InvariantResidueGalois
import AllCharacteristics.SectionResidueField

/-!
# Residue extensions above rational invariant-quotient points

For a rational point of an affine finite-group quotient, the residue field
of the quotient prime is the ground field.  Consequently the residue field
of any prime above it is a finite Galois extension of the ground field in
characteristic zero.  This is the field extension on which the ordered tuple
and its Galois permutations are read.
-/

open AlgebraicGeometry CategoryTheory
open scoped Pointwise

namespace AllCharacteristics

universe u v

/-- The quotient prime lying under a prime of the ring carrying the action. -/
noncomputable abbrev invariantQuotientPrime
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    (G : Type v) [Group G] [MulSemiringAction G A]
    [SMulCommClass G R A] (q : PrimeSpectrum A) :
    PrimeSpectrum (FixedPoints.subalgebra R A G) :=
  PrimeSpectrum.comap
    (algebraMap (FixedPoints.subalgebra R A G) A) q

section GeneralSection

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
variable (G : Type v) [Finite G] [Group G] [MulSemiringAction G A]
variable [SMulCommClass G R A]
variable {K : Type u} [Field K]

/-- The quotient-prime residue field is the section's ground field, for an
arbitrary morphism from the invariant spectrum to that field spectrum. -/
noncomputable def invariantSectionPointResidueBaseIso
    (t : affineInvariantQuotient R A G ⟶ Spec (.of K))
    (c : Spec (.of K) ⟶ affineInvariantQuotient R A G)
    (hc : c ≫ t = 𝟙 _)
    (q : PrimeSpectrum A)
    (hq : invariantQuotientPrime R A G q =
      c (IsLocalRing.closedPoint K)) :
    let p := invariantQuotientPrime R A G q
    letI : p.asIdeal.IsPrime := p.isPrime
    p.asIdeal.ResidueField ≃+* K := by
  let p := invariantQuotientPrime R A G q
  letI : p.asIdeal.IsPrime := p.isPrime
  exact sectionIdealResidueFieldIsoOfPointEq t c hc p hq

/-- The inverse base-field identification is the canonical quotient residue
point followed by the quotient's structure morphism. -/
theorem invariantSectionPointResidueBaseIso_symm_specMap
    (t : affineInvariantQuotient R A G ⟶ Spec (.of K))
    (c : Spec (.of K) ⟶ affineInvariantQuotient R A G)
    (hc : c ≫ t = 𝟙 _)
    (q : PrimeSpectrum A)
    (hq : invariantQuotientPrime R A G q =
      c (IsLocalRing.closedPoint K)) :
    let p := invariantQuotientPrime R A G q
    let e := invariantSectionPointResidueBaseIso R A G t c hc q hq
    Spec.map (CommRingCat.ofHom e.symm.toRingHom) =
      Spec.map (CommRingCat.ofHom
        (algebraMap (FixedPoints.subalgebra R A G)
          p.asIdeal.ResidueField)) ≫ t := by
  exact sectionIdealResidueFieldIsoOfPointEq_symm_specMap
    t c hc (invariantQuotientPrime R A G q) hq

/-- The ground-field algebra structure on the upstairs residue field above
an arbitrary rational section of an invariant spectrum. -/
@[instance_reducible]
noncomputable def invariantSectionPointResidueAlgebra
    (t : affineInvariantQuotient R A G ⟶ Spec (.of K))
    (c : Spec (.of K) ⟶ affineInvariantQuotient R A G)
    (hc : c ≫ t = 𝟙 _)
    (q : PrimeSpectrum A)
    (hq : invariantQuotientPrime R A G q =
      c (IsLocalRing.closedPoint K)) :
    Algebra K q.asIdeal.ResidueField := by
  let p := invariantQuotientPrime R A G q
  let h : p.asIdeal = q.asIdeal.comap
      (algebraMap (FixedPoints.subalgebra R A G) A) :=
    PrimeSpectrum.comap_asIdeal _ _
  letI : p.asIdeal.IsPrime := p.isPrime
  letI : q.asIdeal.IsPrime := q.isPrime
  letI : Algebra p.asIdeal.ResidueField q.asIdeal.ResidueField :=
    invariantPrimeResidueAlgebra p.asIdeal q.asIdeal h
  exact algebraOfBaseRingEquiv p.asIdeal.ResidueField K
    q.asIdeal.ResidueField
      (invariantSectionPointResidueBaseIso R A G t c hc q hq)

/-- The transported ground-field algebra on the upstairs residue field has
the expected scheme-theoretic structure morphism.  It is the canonical
residue point, followed by the invariant quotient and its map to the base. -/
theorem invariantSectionPointResidue_specMap_toBase
    (t : affineInvariantQuotient R A G ⟶ Spec (.of K))
    (c : Spec (.of K) ⟶ affineInvariantQuotient R A G)
    (hc : c ≫ t = 𝟙 _)
    (q : PrimeSpectrum A)
    (hq : invariantQuotientPrime R A G q =
      c (IsLocalRing.closedPoint K)) :
    letI := invariantSectionPointResidueAlgebra R A G t c hc q hq
    Spec.map (CommRingCat.ofHom
        (algebraMap K q.asIdeal.ResidueField)) =
      Spec.map (CommRingCat.ofHom
          (algebraMap A q.asIdeal.ResidueField)) ≫
        affineInvariantQuotientMap R A G ≫ t := by
  unfold affineInvariantQuotient at t c hc hq ⊢
  unfold affineInvariantQuotientMap
  let p := invariantQuotientPrime R A G q
  let h : p.asIdeal = q.asIdeal.comap
      (algebraMap (FixedPoints.subalgebra R A G) A) :=
    PrimeSpectrum.comap_asIdeal _ _
  letI : p.asIdeal.IsPrime := p.isPrime
  letI : q.asIdeal.IsPrime := q.isPrime
  letI : Algebra p.asIdeal.ResidueField q.asIdeal.ResidueField :=
    invariantPrimeResidueAlgebra p.asIdeal q.asIdeal h
  let e := invariantSectionPointResidueBaseIso R A G t c hc q hq
  letI : Algebra K q.asIdeal.ResidueField :=
    invariantSectionPointResidueAlgebra R A G t c hc q hq
  change Spec.map
      (CommRingCat.ofHom e.symm.toRingHom ≫
        CommRingCat.ofHom
          (algebraMap p.asIdeal.ResidueField q.asIdeal.ResidueField)) = _
  rw [Spec.map_comp]
  rw [invariantSectionPointResidueBaseIso_symm_specMap
    R A G t c hc q hq]
  rw [← Category.assoc, ← Category.assoc]
  apply congrArg (· ≫ t)
  change Spec.map (CommRingCat.ofHom
      (algebraMap p.asIdeal.ResidueField q.asIdeal.ResidueField)) ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap (FixedPoints.subalgebra R A G)
            p.asIdeal.ResidueField)) =
      Spec.map (CommRingCat.ofHom
          (algebraMap A q.asIdeal.ResidueField)) ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap (FixedPoints.subalgebra R A G) A))
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext x
  exact Ideal.ResidueField.map_algebraMap p.asIdeal q.asIdeal
    (algebraMap (FixedPoints.subalgebra R A G) A) h x

/-- In characteristic zero, a prime above an arbitrary rational section of
an invariant spectrum has finite residue field over the section field. -/
theorem invariantSectionPointResidue_moduleFinite
    [CharZero K]
    (t : affineInvariantQuotient R A G ⟶ Spec (.of K))
    (c : Spec (.of K) ⟶ affineInvariantQuotient R A G)
    (hc : c ≫ t = 𝟙 _)
    (q : PrimeSpectrum A)
    (hq : invariantQuotientPrime R A G q =
      c (IsLocalRing.closedPoint K)) :
    @Module.Finite K q.asIdeal.ResidueField _ _
      (invariantSectionPointResidueAlgebra R A G t c hc q hq).toModule := by
  let p := invariantQuotientPrime R A G q
  let h : p.asIdeal = q.asIdeal.comap
      (algebraMap (FixedPoints.subalgebra R A G) A) :=
    PrimeSpectrum.comap_asIdeal _ _
  letI : p.asIdeal.IsPrime := p.isPrime
  letI : q.asIdeal.IsPrime := q.isPrime
  letI : Algebra p.asIdeal.ResidueField q.asIdeal.ResidueField :=
    invariantPrimeResidueAlgebra p.asIdeal q.asIdeal h
  haveI : CharZero p.asIdeal.ResidueField :=
    (invariantSectionPointResidueBaseIso R A G t c hc q hq).toRingHom.charZero
  letI : Module.Finite p.asIdeal.ResidueField q.asIdeal.ResidueField :=
    invariantPrimeResidue_moduleFinite G p.asIdeal q.asIdeal h
  letI : Algebra K q.asIdeal.ResidueField :=
    invariantSectionPointResidueAlgebra R A G t c hc q hq
  exact moduleFinite_algebraOfBaseRingEquiv p.asIdeal.ResidueField K
    q.asIdeal.ResidueField
      (invariantSectionPointResidueBaseIso R A G t c hc q hq)

/-- In characteristic zero, a prime above an arbitrary rational section of
an invariant spectrum has Galois residue field over the section field. -/
theorem invariantSectionPointResidue_isGalois
    [CharZero K]
    (t : affineInvariantQuotient R A G ⟶ Spec (.of K))
    (c : Spec (.of K) ⟶ affineInvariantQuotient R A G)
    (hc : c ≫ t = 𝟙 _)
    (q : PrimeSpectrum A)
    (hq : invariantQuotientPrime R A G q =
      c (IsLocalRing.closedPoint K)) :
    @IsGalois K _ q.asIdeal.ResidueField _
      (invariantSectionPointResidueAlgebra R A G t c hc q hq) := by
  let p := invariantQuotientPrime R A G q
  let h : p.asIdeal = q.asIdeal.comap
      (algebraMap (FixedPoints.subalgebra R A G) A) :=
    PrimeSpectrum.comap_asIdeal _ _
  letI : p.asIdeal.IsPrime := p.isPrime
  letI : q.asIdeal.IsPrime := q.isPrime
  letI : Algebra p.asIdeal.ResidueField q.asIdeal.ResidueField :=
    invariantPrimeResidueAlgebra p.asIdeal q.asIdeal h
  haveI : CharZero p.asIdeal.ResidueField :=
    (invariantSectionPointResidueBaseIso R A G t c hc q hq).toRingHom.charZero
  letI : IsGalois p.asIdeal.ResidueField q.asIdeal.ResidueField :=
    invariantPrimeResidue_isGalois G p.asIdeal q.asIdeal h
  letI : Algebra K q.asIdeal.ResidueField :=
    invariantSectionPointResidueAlgebra R A G t c hc q hq
  exact isGalois_algebraOfBaseRingEquiv p.asIdeal.ResidueField K
    q.asIdeal.ResidueField
      (invariantSectionPointResidueBaseIso R A G t c hc q hq)

end GeneralSection

variable (K A : Type u) [Field K] [CommRing A] [Algebra K A]
variable (G : Type v) [Finite G] [Group G] [MulSemiringAction G A]
variable [SMulCommClass G K A]

/-- If the quotient prime is selected by a rational section, its
ideal-theoretic residue field is isomorphic to the ground field. -/
noncomputable def invariantRationalPointResidueBaseIso
    (c : Spec (.of K) ⟶ affineInvariantQuotient K A G)
    (hc : c ≫ affineInvariantQuotientToBase K A G = 𝟙 _)
    (q : PrimeSpectrum A)
    (hq : invariantQuotientPrime K A G q =
      c (IsLocalRing.closedPoint K)) :
    let p := invariantQuotientPrime K A G q
    letI : p.asIdeal.IsPrime := p.isPrime
    p.asIdeal.ResidueField ≃+* K := by
  let p := invariantQuotientPrime K A G q
  letI : p.asIdeal.IsPrime := p.isPrime
  exact sectionIdealResidueFieldIsoOfPointEq
    (affineInvariantQuotientToBase K A G) c hc p hq

/-- The ground-field algebra structure on the upstairs residue field induced
by a rational quotient point. -/
@[instance_reducible]
noncomputable def invariantRationalPointResidueAlgebra
    (c : Spec (.of K) ⟶ affineInvariantQuotient K A G)
    (hc : c ≫ affineInvariantQuotientToBase K A G = 𝟙 _)
    (q : PrimeSpectrum A)
    (hq : invariantQuotientPrime K A G q =
      c (IsLocalRing.closedPoint K)) :
    Algebra K q.asIdeal.ResidueField := by
  let p := invariantQuotientPrime K A G q
  let h : p.asIdeal = q.asIdeal.comap
      (algebraMap (FixedPoints.subalgebra K A G) A) :=
    PrimeSpectrum.comap_asIdeal _ _
  letI : p.asIdeal.IsPrime := p.isPrime
  letI : q.asIdeal.IsPrime := q.isPrime
  letI : Algebra p.asIdeal.ResidueField q.asIdeal.ResidueField :=
    invariantPrimeResidueAlgebra p.asIdeal q.asIdeal h
  exact algebraOfBaseRingEquiv p.asIdeal.ResidueField K
    q.asIdeal.ResidueField
      (invariantRationalPointResidueBaseIso K A G c hc q hq)

/-- In characteristic zero, the residue field above a rational point of the
finite invariant quotient is finite over the original ground field. -/
theorem invariantRationalPointResidue_moduleFinite
    [CharZero K]
    (c : Spec (.of K) ⟶ affineInvariantQuotient K A G)
    (hc : c ≫ affineInvariantQuotientToBase K A G = 𝟙 _)
    (q : PrimeSpectrum A)
    (hq : invariantQuotientPrime K A G q =
      c (IsLocalRing.closedPoint K)) :
    @Module.Finite K q.asIdeal.ResidueField _ _
      (invariantRationalPointResidueAlgebra K A G c hc q hq).toModule := by
  let p := invariantQuotientPrime K A G q
  let h : p.asIdeal = q.asIdeal.comap
      (algebraMap (FixedPoints.subalgebra K A G) A) :=
    PrimeSpectrum.comap_asIdeal _ _
  letI : p.asIdeal.IsPrime := p.isPrime
  letI : q.asIdeal.IsPrime := q.isPrime
  letI : Algebra p.asIdeal.ResidueField q.asIdeal.ResidueField :=
    invariantPrimeResidueAlgebra p.asIdeal q.asIdeal h
  haveI : CharZero p.asIdeal.ResidueField :=
    (invariantRationalPointResidueBaseIso K A G c hc q hq).toRingHom.charZero
  letI : Module.Finite p.asIdeal.ResidueField q.asIdeal.ResidueField :=
    invariantPrimeResidue_moduleFinite G p.asIdeal q.asIdeal h
  letI : Algebra K q.asIdeal.ResidueField :=
    invariantRationalPointResidueAlgebra K A G c hc q hq
  exact moduleFinite_algebraOfBaseRingEquiv p.asIdeal.ResidueField K
    q.asIdeal.ResidueField
      (invariantRationalPointResidueBaseIso K A G c hc q hq)

/-- In characteristic zero, the residue field above a rational point of the
finite invariant quotient is Galois over the original ground field. -/
theorem invariantRationalPointResidue_isGalois
    [CharZero K]
    (c : Spec (.of K) ⟶ affineInvariantQuotient K A G)
    (hc : c ≫ affineInvariantQuotientToBase K A G = 𝟙 _)
    (q : PrimeSpectrum A)
    (hq : invariantQuotientPrime K A G q =
      c (IsLocalRing.closedPoint K)) :
    @IsGalois K _ q.asIdeal.ResidueField _
      (invariantRationalPointResidueAlgebra K A G c hc q hq) := by
  let p := invariantQuotientPrime K A G q
  let h : p.asIdeal = q.asIdeal.comap
      (algebraMap (FixedPoints.subalgebra K A G) A) :=
    PrimeSpectrum.comap_asIdeal _ _
  letI : p.asIdeal.IsPrime := p.isPrime
  letI : q.asIdeal.IsPrime := q.isPrime
  letI : Algebra p.asIdeal.ResidueField q.asIdeal.ResidueField :=
    invariantPrimeResidueAlgebra p.asIdeal q.asIdeal h
  haveI : CharZero p.asIdeal.ResidueField :=
    (invariantRationalPointResidueBaseIso K A G c hc q hq).toRingHom.charZero
  letI : IsGalois p.asIdeal.ResidueField q.asIdeal.ResidueField :=
    invariantPrimeResidue_isGalois G p.asIdeal q.asIdeal h
  letI : Algebra K q.asIdeal.ResidueField :=
    invariantRationalPointResidueAlgebra K A G c hc q hq
  exact isGalois_algebraOfBaseRingEquiv p.asIdeal.ResidueField K
    q.asIdeal.ResidueField
      (invariantRationalPointResidueBaseIso K A G c hc q hq)

/-- Changing from the quotient residue field to the rational ground field
does not change the residue degree. -/
theorem invariantRationalPointResidue_finrank
    [CharZero K]
    (c : Spec (.of K) ⟶ affineInvariantQuotient K A G)
    (hc : c ≫ affineInvariantQuotientToBase K A G = 𝟙 _)
    (q : PrimeSpectrum A)
    (hq : invariantQuotientPrime K A G q =
      c (IsLocalRing.closedPoint K)) :
    let p := invariantQuotientPrime K A G q
    let h : p.asIdeal = q.asIdeal.comap
        (algebraMap (FixedPoints.subalgebra K A G) A) :=
      PrimeSpectrum.comap_asIdeal _ _
    @Module.finrank K q.asIdeal.ResidueField _ _
        (invariantRationalPointResidueAlgebra K A G c hc q hq).toModule =
      @Module.finrank p.asIdeal.ResidueField q.asIdeal.ResidueField _ _
        (invariantPrimeResidueAlgebra p.asIdeal q.asIdeal h).toModule := by
  let p := invariantQuotientPrime K A G q
  let h : p.asIdeal = q.asIdeal.comap
      (algebraMap (FixedPoints.subalgebra K A G) A) :=
    PrimeSpectrum.comap_asIdeal _ _
  letI : p.asIdeal.IsPrime := p.isPrime
  letI : q.asIdeal.IsPrime := q.isPrime
  letI : Algebra p.asIdeal.ResidueField q.asIdeal.ResidueField :=
    invariantPrimeResidueAlgebra p.asIdeal q.asIdeal h
  haveI : CharZero p.asIdeal.ResidueField :=
    (invariantRationalPointResidueBaseIso K A G c hc q hq).toRingHom.charZero
  letI : Module.Finite p.asIdeal.ResidueField q.asIdeal.ResidueField :=
    invariantPrimeResidue_moduleFinite G p.asIdeal q.asIdeal h
  letI : Algebra K q.asIdeal.ResidueField :=
    invariantRationalPointResidueAlgebra K A G c hc q hq
  exact finrank_algebraOfBaseRingEquiv p.asIdeal.ResidueField K
    q.asIdeal.ResidueField
      (invariantRationalPointResidueBaseIso K A G c hc q hq)

end AllCharacteristics
