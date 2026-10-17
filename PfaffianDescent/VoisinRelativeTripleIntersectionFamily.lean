import PfaffianDescent.VoisinSelectedSplitPencilComparison
import AllCharacteristics.ProjectiveBaseChange

/-!
# A cubic--quadric--quadric family over an affine ring

The local quadratic frame has coefficients in a determinant localization.
This file makes its three-equation projective family over that ring, and
identifies each coefficient specialization with the corresponding fiber.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open CategoryTheory.Limits
open AllCharacteristics.HomogeneousProjective

universe u v

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable def relativeTripleIntersectionHomogeneousIdeal
    {R : Type u} [CommRing R]
    (p q r : MvPolynomial (Fin 4) R)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hr : r.IsHomogeneous 2) :
    HomogeneousIdeal (homogeneousSubmodule (Fin 4) R) :=
  ⟨Ideal.span ({p, q, r} : Set (MvPolynomial (Fin 4) R)), by
    apply Ideal.homogeneous_span
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl
    · exact ⟨3, hp⟩
    · exact ⟨2, hq⟩
    · exact ⟨2, hr⟩⟩

noncomputable abbrev relativeTripleIntersectionFamily
    {R : Type u} [CommRing R]
    (p q r : MvPolynomial (Fin 4) R)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hr : r.IsHomogeneous 2) : Scheme.{u} :=
  scheme (relativeTripleIntersectionHomogeneousIdeal p q r hp hq hr)

noncomputable abbrev relativeTripleIntersectionToBase
    {R : Type u} [CommRing R]
    (p q r : MvPolynomial (Fin 4) R)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hr : r.IsHomogeneous 2) :
    relativeTripleIntersectionFamily p q r hp hq hr ⟶ Spec (.of R) :=
  toBase (relativeTripleIntersectionHomogeneousIdeal p q r hp hq hr)

instance relativeTripleIntersectionToBase_isProper
    {R : Type u} [CommRing R]
    (p q r : MvPolynomial (Fin 4) R)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hr : r.IsHomogeneous 2) :
    IsProper (relativeTripleIntersectionToBase p q r hp hq hr) := by
  dsimp [relativeTripleIntersectionToBase]
  infer_instance

theorem relativeTripleIntersectionHomogeneousIdeal_map
    {R : Type u} [CommRing R]
    {S : Type u} [CommRing S]
    (f : R →+* S)
    (p q r : MvPolynomial (Fin 4) R)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hr : r.IsHomogeneous 2) :
    (relativeTripleIntersectionHomogeneousIdeal p q r hp hq hr).toIdeal.map
      (MvPolynomial.map f) =
    (relativeTripleIntersectionHomogeneousIdeal
      (p.map f) (q.map f) (r.map f)
      (hp.map f) (hq.map f) (hr.map f)).toIdeal := by
  rw [relativeTripleIntersectionHomogeneousIdeal,
    relativeTripleIntersectionHomogeneousIdeal, Ideal.map_span]
  simp [Set.image_insert_eq, Set.image_singleton]

noncomputable def relativeTripleIntersectionBaseChangeIso
    {R : Type u} [CommRing R]
    {S : Type u} [CommRing S]
    (f : R →+* S)
    (p q r : MvPolynomial (Fin 4) R)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hr : r.IsHomogeneous 2) :
    relativeTripleIntersectionFamily
      (p.map f) (q.map f) (r.map f)
      (hp.map f) (hq.map f) (hr.map f) ≅
    pullback (relativeTripleIntersectionToBase p q r hp hq hr)
      (Spec.map (CommRingCat.ofHom f)) := by
  apply projectiveBaseChangeIso f
    (relativeTripleIntersectionHomogeneousIdeal p q r hp hq hr)
    (relativeTripleIntersectionHomogeneousIdeal
      (p.map f) (q.map f) (r.map f)
      (hp.map f) (hq.map f) (hr.map f))
  exact relativeTripleIntersectionHomogeneousIdeal_map f p q r hp hq hr

/-- A finite specialization gives a finite fibre of the relative family. -/
theorem relativeTripleIntersection_finiteFibre_of_finiteSpecialization
    {R : Type u} [CommRing R]
    {F : Type u} [Field F]
    (f : R →+* F)
    (p q r : MvPolynomial (Fin 4) R)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hr : r.IsHomogeneous 2)
    [IsFinite (toBase (relativeTripleIntersectionHomogeneousIdeal
      (p.map f) (q.map f) (r.map f)
      (hp.map f) (hq.map f) (hr.map f)))] :
    ((relativeTripleIntersectionToBase p q r hp hq hr) ⁻¹'
      {Spec.map (CommRingCat.ofHom f) (IsLocalRing.closedPoint F)}).Finite := by
  let J := relativeTripleIntersectionHomogeneousIdeal
    (p.map f) (q.map f) (r.map f)
    (hp.map f) (hq.map f) (hr.map f)
  let g := Spec.map (CommRingCat.ofHom f)
  let e := relativeTripleIntersectionBaseChangeIso f p q r hp hq hr
  have hArtinian : IsArtinianScheme (scheme J) := finiteScheme_isArtinian (toBase J)
  letI := hArtinian
  have hsource : (Set.range (e.hom ≫
      pullback.fst (relativeTripleIntersectionToBase p q r hp hq hr) g)).Finite :=
    by simpa only [Set.image_univ] using
      (Set.finite_univ.image (e.hom ≫
        pullback.fst (relativeTripleIntersectionToBase p q r hp hq hr) g))
  have hrange : Set.range g = {g (IsLocalRing.closedPoint F)} := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact Set.mem_singleton_iff.mpr (congrArg g (Subsingleton.elim x _))
    · intro hy
      exact ⟨IsLocalRing.closedPoint F, hy.symm⟩
  have he : Set.range (e.hom ≫
      pullback.fst (relativeTripleIntersectionToBase p q r hp hq hr) g) =
      (relativeTripleIntersectionToBase p q r hp hq hr) ⁻¹'
        {g (IsLocalRing.closedPoint F)} := by
    have hbase : Set.range
        (pullback.fst (relativeTripleIntersectionToBase p q r hp hq hr) g) =
        (relativeTripleIntersectionToBase p q r hp hq hr) ⁻¹'
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

theorem relativeTripleIntersectionHomogeneousIdeal_eq_triple
    {F : Type u} [Field F]
    (p q r : MvPolynomial (Fin 4) F)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hr : r.IsHomogeneous 2) :
    relativeTripleIntersectionHomogeneousIdeal p q r hp hq hr =
      tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr := by
  apply HomogeneousIdeal.ext
  rfl

/-- A finite classical triple intersection gives a finite fibre of the
relative family, without requiring an instance phrased in relative terms. -/
theorem relativeTripleIntersection_finiteFibre_of_finiteTripleSpecialization
    {R : Type u} [CommRing R]
    {F : Type u} [Field F]
    (f : R →+* F)
    (p q r : MvPolynomial (Fin 4) R)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hr : r.IsHomogeneous 2)
    [IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal
      (p.map f) (q.map f) (r.map f)
      (hp.map f) (hq.map f) (hr.map f)))] :
    ((relativeTripleIntersectionToBase p q r hp hq hr) ⁻¹'
      {Spec.map (CommRingCat.ofHom f) (IsLocalRing.closedPoint F)}).Finite := by
  haveI : IsFinite (toBase (relativeTripleIntersectionHomogeneousIdeal
      (p.map f) (q.map f) (r.map f)
      (hp.map f) (hq.map f) (hr.map f))) := by
    rw [relativeTripleIntersectionHomogeneousIdeal_eq_triple]
    infer_instance
  exact relativeTripleIntersection_finiteFibre_of_finiteSpecialization
    f p q r hp hq hr

/-- A finite fibre gives a finite neighborhood of the generic point. -/
theorem relativeTripleIntersection_exists_genericFiniteNeighborhood
    {R : Type u} [CommRing R] [IsDomain R]
    (p q r : MvPolynomial (Fin 4) R)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hr : r.IsHomogeneous 2)
    (y : Spec (.of R))
    (hy : ((relativeTripleIntersectionToBase p q r hp hq hr) ⁻¹' {y}).Finite) :
    ∃ V : (Spec (.of R)).Opens,
      genericPoint (Spec (.of R)) ∈ V ∧
      IsFinite ((relativeTripleIntersectionToBase p q r hp hq hr) ∣_ V) := by
  exact exists_genericPoint_finite_restriction_of_one_finite_fibre
    (relativeTripleIntersectionToBase p q r hp hq hr) y hy

theorem relativeTripleIntersection_exists_genericFiniteNeighborhood_of_finiteTripleSpecialization
    {R : Type u} [CommRing R] [IsDomain R]
    {F : Type u} [Field F]
    (f : R →+* F)
    (p q r : MvPolynomial (Fin 4) R)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hr : r.IsHomogeneous 2)
    [IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal
      (p.map f) (q.map f) (r.map f)
      (hp.map f) (hq.map f) (hr.map f)))] :
    ∃ V : (Spec (.of R)).Opens,
      genericPoint (Spec (.of R)) ∈ V ∧
      IsFinite ((relativeTripleIntersectionToBase p q r hp hq hr) ∣_ V) := by
  exact relativeTripleIntersection_exists_genericFiniteNeighborhood
    p q r hp hq hr
    (Spec.map (CommRingCat.ofHom f) (IsLocalRing.closedPoint F))
    (relativeTripleIntersection_finiteFibre_of_finiteTripleSpecialization
      f p q r hp hq hr)

end PfaffianDescent
