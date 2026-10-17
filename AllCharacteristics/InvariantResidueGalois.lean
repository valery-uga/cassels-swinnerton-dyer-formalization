import Mathlib.RingTheory.Invariant.Galois
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import AllCharacteristics.AffineInvariantQuotient

/-!
# Residue fields of finite invariant quotients

For a finite group action, the residue-field extension at a point over its
quotient is normal.  In characteristic zero it is finite Galois, and every
embedding into an overfield is induced by an element of the stabilizer of
the point.  These are the algebraic facts needed to turn a rational point of
a symmetric quotient into a Galois-stable ordered tuple.
-/

namespace AllCharacteristics
universe u v

open scoped Pointwise

attribute [local instance] Ideal.Quotient.field

section

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
  (G : Type v) [Finite G] [Group G] [MulSemiringAction G B]
  [SMulCommClass G A B] [Algebra.IsInvariant A B G]
  (P : Ideal A) (Q : Ideal B) [Q.LiesOver P]
  [P.IsMaximal] [Q.IsMaximal]

include G

/-- The residue-field extension at a point of a finite invariant quotient is
normal. -/
theorem invariantQuotientResidue_normal :
    Normal (A ⧸ P) (B ⧸ Q) :=
  Ideal.Quotient.normal G P Q

/-- In characteristic zero, the residue-field extension at a point of a
finite invariant quotient is finite. -/
theorem invariantQuotientResidue_moduleFinite
    [CharZero (A ⧸ P)] :
    Module.Finite (A ⧸ P) (B ⧸ Q) := by
  letI : Normal (A ⧸ P) (B ⧸ Q) := invariantQuotientResidue_normal G P Q
  letI : Algebra.IsSeparable (A ⧸ P) (B ⧸ Q) := inferInstance
  exact Ideal.Quotient.finite_of_isInvariant G P Q

/-- In characteristic zero, the residue-field extension at a point of a
finite invariant quotient is finite Galois. -/
theorem invariantQuotientResidue_isGalois
    [CharZero (A ⧸ P)] :
    IsGalois (A ⧸ P) (B ⧸ Q) := by
  letI : Normal (A ⧸ P) (B ⧸ Q) := invariantQuotientResidue_normal G P Q
  letI : Module.Finite (A ⧸ P) (B ⧸ Q) :=
    invariantQuotientResidue_moduleFinite G P Q
  exact
    { to_normal := inferInstance
      to_isSeparable := inferInstance }

/-- Every embedding of the quotient residue field into an overfield is
induced, after the fixed inclusion, by an element of the point stabilizer. -/
theorem exists_stabilizer_inducing_residueEmbedding
    {L : Type u} [Field L]
    [Algebra (A ⧸ P) L] [Algebra (B ⧸ Q) L]
    [IsScalarTower (A ⧸ P) (B ⧸ Q) L]
    [Normal (A ⧸ P) (B ⧸ Q)]
    (e : (B ⧸ Q) →ₐ[A ⧸ P] L) :
    ∃ s : MulAction.stabilizer G Q, ∀ x : B ⧸ Q,
      algebraMap (B ⧸ Q) L
          (Ideal.Quotient.stabilizerHom Q P G s x) = e x := by
  obtain ⟨s, hs⟩ := Ideal.Quotient.stabilizerHom_surjective G P Q
    (e.restrictNormal' (B ⧸ Q))
  refine ⟨s, fun x ↦ ?_⟩
  rw [hs]
  exact e.restrictNormal_commutes (B ⧸ Q) x

end

section PrimeResidues

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
  (G : Type v) [Finite G] [Group G] [MulSemiringAction G B]
  [SMulCommClass G A B] [Algebra.IsInvariant A B G]

include G

/-- The canonical algebra structure on the residue fields of a prime and a
prime lying over it. -/
@[instance_reducible]
noncomputable def invariantPrimeResidueAlgebra
    (P : Ideal A) (Q : Ideal B) [P.IsPrime] [Q.IsPrime]
    (h : P = Q.comap (algebraMap A B)) :
    Algebra P.ResidueField Q.ResidueField :=
  (Ideal.ResidueField.map P Q (algebraMap A B) h).toAlgebra

/-- The residue-field extension at a prime of an invariant quotient is
normal, stated directly for the fraction-field residue fields used by scheme
points. -/
theorem invariantPrimeResidue_normal
    (P : Ideal A) (Q : Ideal B) [P.IsPrime] [Q.IsPrime]
    (h : P = Q.comap (algebraMap A B)) :
    letI : Q.LiesOver P := ⟨h⟩
    letI := invariantPrimeResidueAlgebra P Q h
    Normal P.ResidueField Q.ResidueField := by
  letI : Q.LiesOver P := ⟨h⟩
  let e := Ideal.ResidueField.map P Q (algebraMap A B) h
  letI : Algebra P.ResidueField Q.ResidueField := e.toAlgebra
  letI : Algebra (A ⧸ P) Q.ResidueField :=
    ((algebraMap (B ⧸ Q) Q.ResidueField).comp
      (algebraMap (A ⧸ P) (B ⧸ Q))).toAlgebra
  letI : IsScalarTower (A ⧸ P) (B ⧸ Q) Q.ResidueField :=
    IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  have hmap (x : A) :
      algebraMap P.ResidueField Q.ResidueField (algebraMap A P.ResidueField x) =
        algebraMap B Q.ResidueField (algebraMap A B x) :=
    Ideal.ResidueField.map_algebraMap P Q (algebraMap A B) h x
  letI : IsScalarTower (A ⧸ P) P.ResidueField Q.ResidueField := by
    apply IsScalarTower.of_algebraMap_eq
    rintro ⟨x⟩
    exact (hmap x).symm
  exact Ideal.IsFractionRing.normal G P Q P.ResidueField Q.ResidueField

/-- In characteristic zero, the residue-field extension at a prime of an
invariant quotient is finite. -/
theorem invariantPrimeResidue_moduleFinite
    (P : Ideal A) (Q : Ideal B) [P.IsPrime] [Q.IsPrime]
    (h : P = Q.comap (algebraMap A B)) [CharZero P.ResidueField] :
    letI := invariantPrimeResidueAlgebra P Q h
    Module.Finite P.ResidueField Q.ResidueField := by
  letI : Q.LiesOver P := ⟨h⟩
  let e := Ideal.ResidueField.map P Q (algebraMap A B) h
  letI : Algebra P.ResidueField Q.ResidueField := e.toAlgebra
  letI : Algebra (A ⧸ P) Q.ResidueField :=
    ((algebraMap (B ⧸ Q) Q.ResidueField).comp
      (algebraMap (A ⧸ P) (B ⧸ Q))).toAlgebra
  letI : IsScalarTower (A ⧸ P) (B ⧸ Q) Q.ResidueField :=
    IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  have hmap (x : A) :
      algebraMap P.ResidueField Q.ResidueField (algebraMap A P.ResidueField x) =
        algebraMap B Q.ResidueField (algebraMap A B x) :=
    Ideal.ResidueField.map_algebraMap P Q (algebraMap A B) h x
  letI : IsScalarTower (A ⧸ P) P.ResidueField Q.ResidueField := by
    apply IsScalarTower.of_algebraMap_eq
    rintro ⟨x⟩
    exact (hmap x).symm
  letI : Normal P.ResidueField Q.ResidueField :=
    Ideal.IsFractionRing.normal G P Q P.ResidueField Q.ResidueField
  letI : Algebra.IsSeparable P.ResidueField Q.ResidueField := inferInstance
  exact Ideal.IsFractionRing.finite_of_isInvariant
    G P Q P.ResidueField Q.ResidueField

/-- In characteristic zero, the residue-field extension at a prime of an
invariant quotient is finite Galois. -/
theorem invariantPrimeResidue_isGalois
    (P : Ideal A) (Q : Ideal B) [P.IsPrime] [Q.IsPrime]
    (h : P = Q.comap (algebraMap A B)) [CharZero P.ResidueField] :
    letI := invariantPrimeResidueAlgebra P Q h
    IsGalois P.ResidueField Q.ResidueField := by
  letI : Algebra P.ResidueField Q.ResidueField :=
    invariantPrimeResidueAlgebra P Q h
  letI : Normal P.ResidueField Q.ResidueField :=
    invariantPrimeResidue_normal G P Q h
  letI : Module.Finite P.ResidueField Q.ResidueField :=
    invariantPrimeResidue_moduleFinite G P Q h
  exact
    { to_normal := inferInstance
      to_isSeparable := inferInstance }

/-- The action of the prime stabilizer on the corresponding residue field. -/
noncomputable def invariantPrimeResidueStabilizerHom
    (P : Ideal A) (Q : Ideal B) [P.IsPrime] [Q.IsPrime]
    (h : P = Q.comap (algebraMap A B)) :
    letI := invariantPrimeResidueAlgebra P Q h
    MulAction.stabilizer G Q →* Gal(Q.ResidueField/P.ResidueField) := by
  letI : Algebra P.ResidueField Q.ResidueField :=
    invariantPrimeResidueAlgebra P Q h
  letI : Q.LiesOver P := ⟨h⟩
  letI : Algebra (A ⧸ P) Q.ResidueField :=
    ((algebraMap (B ⧸ Q) Q.ResidueField).comp
      (algebraMap (A ⧸ P) (B ⧸ Q))).toAlgebra
  letI : IsScalarTower (A ⧸ P) (B ⧸ Q) Q.ResidueField :=
    IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  have hmap (x : A) :
      algebraMap P.ResidueField Q.ResidueField (algebraMap A P.ResidueField x) =
        algebraMap B Q.ResidueField (algebraMap A B x) :=
    Ideal.ResidueField.map_algebraMap P Q (algebraMap A B) h x
  letI : IsScalarTower (A ⧸ P) P.ResidueField Q.ResidueField := by
    apply IsScalarTower.of_algebraMap_eq
    rintro ⟨x⟩
    exact (hmap x).symm
  exact IsFractionRing.stabilizerHom
    G P Q P.ResidueField Q.ResidueField

/-- On elements coming from the original ring, the residue-field
stabilizer action is the original ring action. -/
theorem invariantPrimeResidueStabilizerHom_algebraMap
    (P : Ideal A) (Q : Ideal B) [P.IsPrime] [Q.IsPrime]
    (h : P = Q.comap (algebraMap A B))
    (s : MulAction.stabilizer G Q) (x : B) :
    letI := invariantPrimeResidueAlgebra P Q h
    invariantPrimeResidueStabilizerHom G P Q h s
        (algebraMap B Q.ResidueField x) =
      algebraMap B Q.ResidueField (s.val • x) := by
  letI : Algebra P.ResidueField Q.ResidueField :=
    invariantPrimeResidueAlgebra P Q h
  letI : Q.LiesOver P := ⟨h⟩
  letI : Algebra (A ⧸ P) Q.ResidueField :=
    ((algebraMap (B ⧸ Q) Q.ResidueField).comp
      (algebraMap (A ⧸ P) (B ⧸ Q))).toAlgebra
  letI : IsScalarTower (A ⧸ P) (B ⧸ Q) Q.ResidueField :=
    IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  have hmap (a : A) :
      algebraMap P.ResidueField Q.ResidueField (algebraMap A P.ResidueField a) =
        algebraMap B Q.ResidueField (algebraMap A B a) :=
    Ideal.ResidueField.map_algebraMap P Q (algebraMap A B) h a
  letI : IsScalarTower (A ⧸ P) P.ResidueField Q.ResidueField := by
    apply IsScalarTower.of_algebraMap_eq
    rintro ⟨a⟩
    exact (hmap a).symm
  change IsFractionRing.stabilizerHom G P Q P.ResidueField Q.ResidueField s
      (algebraMap B Q.ResidueField x) =
    algebraMap B Q.ResidueField (s.val • x)
  simpa only [Ideal.algebraMap_quotient_residueField_mk] using
    IsFractionRing.stabilizerHom_apply_apply_mk
      G P Q P.ResidueField Q.ResidueField s x

/-- Every automorphism of the prime residue-field extension is induced by
an element of the prime stabilizer. -/
theorem invariantPrimeResidueStabilizerHom_surjective
    (P : Ideal A) (Q : Ideal B) [P.IsPrime] [Q.IsPrime]
    (h : P = Q.comap (algebraMap A B)) :
    letI := invariantPrimeResidueAlgebra P Q h
    Function.Surjective (invariantPrimeResidueStabilizerHom G P Q h) := by
  letI : Algebra P.ResidueField Q.ResidueField :=
    invariantPrimeResidueAlgebra P Q h
  letI : Q.LiesOver P := ⟨h⟩
  letI : Algebra (A ⧸ P) Q.ResidueField :=
    ((algebraMap (B ⧸ Q) Q.ResidueField).comp
      (algebraMap (A ⧸ P) (B ⧸ Q))).toAlgebra
  letI : IsScalarTower (A ⧸ P) (B ⧸ Q) Q.ResidueField :=
    IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  have hmap (x : A) :
      algebraMap P.ResidueField Q.ResidueField (algebraMap A P.ResidueField x) =
        algebraMap B Q.ResidueField (algebraMap A B x) :=
    Ideal.ResidueField.map_algebraMap P Q (algebraMap A B) h x
  letI : IsScalarTower (A ⧸ P) P.ResidueField Q.ResidueField := by
    apply IsScalarTower.of_algebraMap_eq
    rintro ⟨x⟩
    exact (hmap x).symm
  exact IsFractionRing.stabilizerHom_surjective
    G P Q P.ResidueField Q.ResidueField

/-- Every embedding of a prime residue field into an overfield is induced,
after the fixed inclusion, by an element of the stabilizer of that prime. -/
theorem exists_stabilizer_inducing_primeResidueEmbedding
    (P : Ideal A) (Q : Ideal B) [P.IsPrime] [Q.IsPrime]
    (h : P = Q.comap (algebraMap A B)) :
    letI := invariantPrimeResidueAlgebra P Q h
    ∀ {L : Type u} [Field L]
      [Algebra P.ResidueField L] [Algebra Q.ResidueField L]
      [IsScalarTower P.ResidueField Q.ResidueField L]
      [Normal P.ResidueField Q.ResidueField]
      (e : Q.ResidueField →ₐ[P.ResidueField] L),
      ∃ s : MulAction.stabilizer G Q, ∀ x : Q.ResidueField,
        algebraMap Q.ResidueField L
            (invariantPrimeResidueStabilizerHom G P Q h s x) = e x := by
  letI : Algebra P.ResidueField Q.ResidueField :=
    invariantPrimeResidueAlgebra P Q h
  intro L _ _ _ _ _ e
  obtain ⟨s, hs⟩ := invariantPrimeResidueStabilizerHom_surjective G P Q h
    (e.restrictNormal' Q.ResidueField)
  refine ⟨s, fun x ↦ ?_⟩
  rw [hs]
  exact e.restrictNormal_commutes Q.ResidueField x

end PrimeResidues

section AffineInvariantPrime

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
  (G : Type v) [Finite G] [Group G] [MulSemiringAction G A]
  [SMulCommClass G R A]

/-- The canonical residue-field algebra at a point of the concrete affine
invariant quotient. -/
@[instance_reducible]
noncomputable def affineInvariantPrimeResidueAlgebra
    (q : PrimeSpectrum A) :
    let p : PrimeSpectrum (FixedPoints.subalgebra R A G) :=
      affineInvariantQuotientMap R A G q
    Algebra p.asIdeal.ResidueField q.asIdeal.ResidueField := by
  let P := (affineInvariantQuotientMap R A G q).asIdeal
  let Q := q.asIdeal
  letI : P.IsPrime := (affineInvariantQuotientMap R A G q).isPrime
  letI : Q.IsPrime := q.isPrime
  have h : P = Q.comap
      (algebraMap (FixedPoints.subalgebra R A G) A) := rfl
  exact invariantPrimeResidueAlgebra P Q h

/-- The residue-field extension at a point of the concrete affine invariant
quotient is normal. -/
theorem affineInvariantPrimeResidue_normal
    (q : PrimeSpectrum A) :
    let p : PrimeSpectrum (FixedPoints.subalgebra R A G) :=
      affineInvariantQuotientMap R A G q
    letI := affineInvariantPrimeResidueAlgebra R A G q
    Normal p.asIdeal.ResidueField q.asIdeal.ResidueField := by
  let P := (affineInvariantQuotientMap R A G q).asIdeal
  let Q := q.asIdeal
  letI : P.IsPrime := (affineInvariantQuotientMap R A G q).isPrime
  letI : Q.IsPrime := q.isPrime
  have h : P = Q.comap
      (algebraMap (FixedPoints.subalgebra R A G) A) := rfl
  exact invariantPrimeResidue_normal G P Q h

/-- In characteristic zero, the residue-field extension at a point of the
concrete affine invariant quotient is finite. -/
theorem affineInvariantPrimeResidue_moduleFinite
    (q : PrimeSpectrum A)
    [CharZero
      (let p : PrimeSpectrum (FixedPoints.subalgebra R A G) :=
        affineInvariantQuotientMap R A G q
       p.asIdeal.ResidueField)] :
    let p : PrimeSpectrum (FixedPoints.subalgebra R A G) :=
      affineInvariantQuotientMap R A G q
    letI := affineInvariantPrimeResidueAlgebra R A G q
    Module.Finite p.asIdeal.ResidueField q.asIdeal.ResidueField := by
  let P := (affineInvariantQuotientMap R A G q).asIdeal
  let Q := q.asIdeal
  letI : P.IsPrime := (affineInvariantQuotientMap R A G q).isPrime
  letI : Q.IsPrime := q.isPrime
  have h : P = Q.comap
      (algebraMap (FixedPoints.subalgebra R A G) A) := rfl
  exact invariantPrimeResidue_moduleFinite G P Q h

/-- In characteristic zero, the residue-field extension at a point of the
concrete affine invariant quotient is finite Galois. -/
theorem affineInvariantPrimeResidue_isGalois
    (q : PrimeSpectrum A)
    [CharZero
      (let p : PrimeSpectrum (FixedPoints.subalgebra R A G) :=
        affineInvariantQuotientMap R A G q
       p.asIdeal.ResidueField)] :
    let p : PrimeSpectrum (FixedPoints.subalgebra R A G) :=
      affineInvariantQuotientMap R A G q
    letI := affineInvariantPrimeResidueAlgebra R A G q
    IsGalois p.asIdeal.ResidueField q.asIdeal.ResidueField := by
  let P := (affineInvariantQuotientMap R A G q).asIdeal
  let Q := q.asIdeal
  letI : P.IsPrime := (affineInvariantQuotientMap R A G q).isPrime
  letI : Q.IsPrime := q.isPrime
  have h : P = Q.comap
      (algebraMap (FixedPoints.subalgebra R A G) A) := rfl
  exact invariantPrimeResidue_isGalois G P Q h

end AffineInvariantPrime

end AllCharacteristics
