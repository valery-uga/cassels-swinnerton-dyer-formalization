import PfaffianDescent.VoisinSelectedSplitPencilComparison
import AllCharacteristics.ProjectiveBaseChange

/-!
# Relative homogeneous triple intersections of arbitrary degrees

The projective three-equation family, its actual coefficient base-change
isomorphism, and transfer from a finite specialized fiber to a generic finite
neighborhood. This extends the degree-(3,2,2) construction to degree-(3,3,3)
and other homogeneous regular intersections, without a supplied openness
or base-change certificate.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open CategoryTheory.Limits
open AllCharacteristics.HomogeneousProjective

universe u v

attribute [local instance] MvPolynomial.gradedAlgebra

variable {a b c : ℕ}

noncomputable def relativeHomogeneousTripleIntersectionHomogeneousIdeal
    {R : Type u} [CommRing R]
    (p q r : MvPolynomial (Fin 4) R)
    (hp : p.IsHomogeneous a) (hq : q.IsHomogeneous b)
    (hr : r.IsHomogeneous c) :
    HomogeneousIdeal (homogeneousSubmodule (Fin 4) R) :=
  ⟨Ideal.span ({p, q, r} : Set (MvPolynomial (Fin 4) R)), by
    apply Ideal.homogeneous_span
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl
    · exact ⟨a, hp⟩
    · exact ⟨b, hq⟩
    · exact ⟨c, hr⟩⟩

noncomputable abbrev relativeHomogeneousTripleIntersectionFamily
    {R : Type u} [CommRing R]
    (p q r : MvPolynomial (Fin 4) R)
    (hp : p.IsHomogeneous a) (hq : q.IsHomogeneous b)
    (hr : r.IsHomogeneous c) : Scheme.{u} :=
  scheme (relativeHomogeneousTripleIntersectionHomogeneousIdeal p q r hp hq hr)

noncomputable abbrev relativeHomogeneousTripleIntersectionToBase
    {R : Type u} [CommRing R]
    (p q r : MvPolynomial (Fin 4) R)
    (hp : p.IsHomogeneous a) (hq : q.IsHomogeneous b)
    (hr : r.IsHomogeneous c) :
    relativeHomogeneousTripleIntersectionFamily p q r hp hq hr ⟶ Spec (.of R) :=
  toBase (relativeHomogeneousTripleIntersectionHomogeneousIdeal p q r hp hq hr)

instance relativeHomogeneousTripleIntersectionToBase_isProper
    {R : Type u} [CommRing R]
    (p q r : MvPolynomial (Fin 4) R)
    (hp : p.IsHomogeneous a) (hq : q.IsHomogeneous b)
    (hr : r.IsHomogeneous c) :
    IsProper (relativeHomogeneousTripleIntersectionToBase p q r hp hq hr) := by
  dsimp [relativeHomogeneousTripleIntersectionToBase]
  infer_instance

theorem relativeHomogeneousTripleIntersectionHomogeneousIdeal_map
    {R : Type u} [CommRing R]
    {S : Type u} [CommRing S]
    (f : R →+* S)
    (p q r : MvPolynomial (Fin 4) R)
    (hp : p.IsHomogeneous a) (hq : q.IsHomogeneous b)
    (hr : r.IsHomogeneous c) :
    (relativeHomogeneousTripleIntersectionHomogeneousIdeal p q r hp hq hr).toIdeal.map
      (MvPolynomial.map f) =
    (relativeHomogeneousTripleIntersectionHomogeneousIdeal
      (p.map f) (q.map f) (r.map f)
      (hp.map f) (hq.map f) (hr.map f)).toIdeal := by
  rw [relativeHomogeneousTripleIntersectionHomogeneousIdeal,
    relativeHomogeneousTripleIntersectionHomogeneousIdeal, Ideal.map_span]
  simp [Set.image_insert_eq, Set.image_singleton]

noncomputable def relativeHomogeneousTripleIntersectionBaseChangeIso
    {R : Type u} [CommRing R]
    {S : Type u} [CommRing S]
    (f : R →+* S)
    (p q r : MvPolynomial (Fin 4) R)
    (hp : p.IsHomogeneous a) (hq : q.IsHomogeneous b)
    (hr : r.IsHomogeneous c) :
    relativeHomogeneousTripleIntersectionFamily
      (p.map f) (q.map f) (r.map f)
      (hp.map f) (hq.map f) (hr.map f) ≅
    pullback (relativeHomogeneousTripleIntersectionToBase p q r hp hq hr)
      (Spec.map (CommRingCat.ofHom f)) := by
  apply projectiveBaseChangeIso f
    (relativeHomogeneousTripleIntersectionHomogeneousIdeal p q r hp hq hr)
    (relativeHomogeneousTripleIntersectionHomogeneousIdeal
      (p.map f) (q.map f) (r.map f)
      (hp.map f) (hq.map f) (hr.map f))
  exact relativeHomogeneousTripleIntersectionHomogeneousIdeal_map f p q r hp hq hr

/-- A finite specialization gives a finite fibre of the relative family. -/
theorem relativeHomogeneousTripleIntersection_finiteFibre_of_finiteSpecialization
    {R : Type u} [CommRing R]
    {F : Type u} [Field F]
    (f : R →+* F)
    (p q r : MvPolynomial (Fin 4) R)
    (hp : p.IsHomogeneous a) (hq : q.IsHomogeneous b)
    (hr : r.IsHomogeneous c)
    [IsFinite (toBase (relativeHomogeneousTripleIntersectionHomogeneousIdeal
      (p.map f) (q.map f) (r.map f)
      (hp.map f) (hq.map f) (hr.map f)))] :
    ((relativeHomogeneousTripleIntersectionToBase p q r hp hq hr) ⁻¹'
      {Spec.map (CommRingCat.ofHom f) (IsLocalRing.closedPoint F)}).Finite := by
  let J := relativeHomogeneousTripleIntersectionHomogeneousIdeal
    (p.map f) (q.map f) (r.map f)
    (hp.map f) (hq.map f) (hr.map f)
  let g := Spec.map (CommRingCat.ofHom f)
  let e := relativeHomogeneousTripleIntersectionBaseChangeIso f p q r hp hq hr
  have hArtinian : IsArtinianScheme (scheme J) := finiteScheme_isArtinian (toBase J)
  letI := hArtinian
  have hsource : (Set.range (e.hom ≫
      pullback.fst (relativeHomogeneousTripleIntersectionToBase p q r hp hq hr) g)).Finite :=
    by simpa only [Set.image_univ] using
      (Set.finite_univ.image (e.hom ≫
        pullback.fst (relativeHomogeneousTripleIntersectionToBase p q r hp hq hr) g))
  have hrange : Set.range g = {g (IsLocalRing.closedPoint F)} := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact Set.mem_singleton_iff.mpr (congrArg g (Subsingleton.elim x _))
    · intro hy
      exact ⟨IsLocalRing.closedPoint F, hy.symm⟩
  have he : Set.range (e.hom ≫
      pullback.fst (relativeHomogeneousTripleIntersectionToBase p q r hp hq hr) g) =
      (relativeHomogeneousTripleIntersectionToBase p q r hp hq hr) ⁻¹'
        {g (IsLocalRing.closedPoint F)} := by
    have hbase : Set.range
        (pullback.fst (relativeHomogeneousTripleIntersectionToBase p q r hp hq hr) g) =
        (relativeHomogeneousTripleIntersectionToBase p q r hp hq hr) ⁻¹'
          {g (IsLocalRing.closedPoint F)} := by
      rw [AlgebraicGeometry.Scheme.Pullback.range_fst, hrange]
    rw [← hbase]
    ext x
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨e.hom w, Scheme.Hom.comp_apply ..⟩
    · rintro ⟨z, hz⟩
      obtain ⟨w, rfl⟩ := e.hom.surjective z
      exact ⟨w, by simpa only [Scheme.Hom.comp_apply] using hz⟩
  exact he ▸ hsource

theorem relativeHomogeneousTripleIntersectionHomogeneousIdeal_eq_triple
    {F : Type u} [Field F]
    (p q r : MvPolynomial (Fin 4) F)
    (hp : p.IsHomogeneous a) (hq : q.IsHomogeneous b)
    (hr : r.IsHomogeneous c) :
    relativeHomogeneousTripleIntersectionHomogeneousIdeal p q r hp hq hr =
      tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr := by
  apply HomogeneousIdeal.ext
  rfl

/-- A finite classical triple intersection gives a finite fibre of the
relative family, without requiring an instance phrased in relative terms. -/
theorem relativeHomogeneousTripleIntersection_finiteFibre_of_finiteTripleSpecialization
    {R : Type u} [CommRing R]
    {F : Type u} [Field F]
    (f : R →+* F)
    (p q r : MvPolynomial (Fin 4) R)
    (hp : p.IsHomogeneous a) (hq : q.IsHomogeneous b)
    (hr : r.IsHomogeneous c)
    [IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal
      (p.map f) (q.map f) (r.map f)
      (hp.map f) (hq.map f) (hr.map f)))] :
    ((relativeHomogeneousTripleIntersectionToBase p q r hp hq hr) ⁻¹'
      {Spec.map (CommRingCat.ofHom f) (IsLocalRing.closedPoint F)}).Finite := by
  haveI : IsFinite (toBase (relativeHomogeneousTripleIntersectionHomogeneousIdeal
      (p.map f) (q.map f) (r.map f)
      (hp.map f) (hq.map f) (hr.map f))) := by
    rw [relativeHomogeneousTripleIntersectionHomogeneousIdeal_eq_triple]
    infer_instance
  exact relativeHomogeneousTripleIntersection_finiteFibre_of_finiteSpecialization
    f p q r hp hq hr

/-- A finite fibre gives a finite neighborhood of the generic point. -/
theorem relativeHomogeneousTripleIntersection_exists_genericFiniteNeighborhood
    {R : Type u} [CommRing R] [IsDomain R]
    (p q r : MvPolynomial (Fin 4) R)
    (hp : p.IsHomogeneous a) (hq : q.IsHomogeneous b)
    (hr : r.IsHomogeneous c)
    (y : Spec (.of R))
    (hy : ((relativeHomogeneousTripleIntersectionToBase p q r hp hq hr) ⁻¹' {y}).Finite) :
    ∃ V : (Spec (.of R)).Opens,
      genericPoint (Spec (.of R)) ∈ V ∧
      IsFinite ((relativeHomogeneousTripleIntersectionToBase p q r hp hq hr) ∣_ V) := by
  exact exists_genericPoint_finite_restriction_of_one_finite_fibre
    (relativeHomogeneousTripleIntersectionToBase p q r hp hq hr) y hy

theorem relativeHomogeneousTripleIntersection_exists_genericFiniteNeighborhood_of_finiteTripleSpecialization
    {R : Type u} [CommRing R] [IsDomain R]
    {F : Type u} [Field F]
    (f : R →+* F)
    (p q r : MvPolynomial (Fin 4) R)
    (hp : p.IsHomogeneous a) (hq : q.IsHomogeneous b)
    (hr : r.IsHomogeneous c)
    [IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal
      (p.map f) (q.map f) (r.map f)
      (hp.map f) (hq.map f) (hr.map f)))] :
    ∃ V : (Spec (.of R)).Opens,
      genericPoint (Spec (.of R)) ∈ V ∧
      IsFinite ((relativeHomogeneousTripleIntersectionToBase p q r hp hq hr) ∣_ V) := by
  exact relativeHomogeneousTripleIntersection_exists_genericFiniteNeighborhood
    p q r hp hq hr
    (Spec.map (CommRingCat.ofHom f) (IsLocalRing.closedPoint F))
    (relativeHomogeneousTripleIntersection_finiteFibre_of_finiteTripleSpecialization
      f p q r hp hq hr)

end PfaffianDescent
