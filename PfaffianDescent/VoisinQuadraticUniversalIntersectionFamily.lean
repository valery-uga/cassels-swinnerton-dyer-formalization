import PfaffianDescent.VoisinQuadraticJacobianUniversalFamily
import PfaffianDescent.VoisinProperQuasiFiniteFibreOpen
import AllCharacteristics.ProjectiveBaseChange
import PfaffianDescent.IntrinsicFiniteCycle
import PfaffianDescent.TripleCompleteIntersectionLength

/-!
# The full universal cubic--quadric--quadric intersection

The existing universal Jacobian family records singular members. This file
exposes the complete-intersection family itself over the same affine
parameter cone. It is projective, hence proper, and its homogeneous ideal
specializes to the literal cubic--quadric--quadric ideal in every field fibre.
-/

namespace PfaffianDescent

open AlgebraicGeometry MvPolynomial
open CategoryTheory.Limits
open CategoryTheory
open AllCharacteristics.HomogeneousProjective

universe u

variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable def cubicTwoQuadricUniversalIntersectionEquationSet
    {n : ℕ} (p q : MvPolynomial (Fin 4) K)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 2) :
    Set (MvPolynomial (Fin 4) (MvPolynomial (Fin n) K)) :=
  {p.map C, q.map C, cubicTwoQuadricUniversalQuadric v}

theorem cubicTwoQuadricUniversalIntersectionEquationSet_homogeneous
    {n : ℕ} (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 2) :
    ∀ s ∈ cubicTwoQuadricUniversalIntersectionEquationSet p q v,
      ∃ d, s.IsHomogeneous d := by
  intro s hs
  simp only [cubicTwoQuadricUniversalIntersectionEquationSet,
    Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  rcases hs with rfl | rfl | rfl
  · exact ⟨3, hp.map C⟩
  · exact ⟨2, hq.map C⟩
  · exact ⟨2, cubicTwoQuadricUniversalQuadric_isHomogeneous v⟩

noncomputable def cubicTwoQuadricUniversalIntersectionIdeal
    {n : ℕ} (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 2) :
    HomogeneousIdeal
      (homogeneousSubmodule (Fin 4) (MvPolynomial (Fin n) K)) :=
  ⟨Ideal.span (cubicTwoQuadricUniversalIntersectionEquationSet p q v),
    Ideal.homogeneous_span _ _
      (cubicTwoQuadricUniversalIntersectionEquationSet_homogeneous
        p q hp hq v)⟩

noncomputable abbrev cubicTwoQuadricUniversalIntersectionFamily
    {n : ℕ} (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 2) : Scheme.{u} :=
  scheme (cubicTwoQuadricUniversalIntersectionIdeal p q hp hq v)

noncomputable abbrev cubicTwoQuadricUniversalIntersectionToCone
    {n : ℕ} (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 2) :
    cubicTwoQuadricUniversalIntersectionFamily p q hp hq v ⟶
      Spec (.of (MvPolynomial (Fin n) K)) :=
  toBase (cubicTwoQuadricUniversalIntersectionIdeal p q hp hq v)

instance cubicTwoQuadricUniversalIntersectionToCone_isProper
    {n : ℕ} (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 2) :
    IsProper (cubicTwoQuadricUniversalIntersectionToCone p q hp hq v) := by
  dsimp [cubicTwoQuadricUniversalIntersectionToCone]
  infer_instance

/-- The full universal ideal specializes to precisely the three equations,
without any Jacobian equations or extra saturation assumption. -/
theorem cubicTwoQuadricUniversalIntersectionIdeal_map
    {L : Type u} [Field L] {n : ℕ}
    (f : K →+* L)
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 2)
    (c : Fin n → L) :
    (cubicTwoQuadricUniversalIntersectionIdeal p q hp hq v).toIdeal.map
      (MvPolynomial.map (MvPolynomial.eval₂Hom f c)) =
      tripleCompleteIntersectionIdeal (p.map f) (q.map f)
        ((cubicTwoQuadricUniversalQuadric v).map
          (MvPolynomial.eval₂Hom f c)) := by
  have hfc : (MvPolynomial.eval₂Hom f c).comp C = f := by
    ext a
    simp
  rw [cubicTwoQuadricUniversalIntersectionIdeal,
    tripleCompleteIntersectionIdeal, Ideal.map_span]
  simp [cubicTwoQuadricUniversalIntersectionEquationSet,
    Set.image_insert_eq, Set.image_singleton, MvPolynomial.map_map, hfc]

/-- The projective scheme cut out by a specialized cubic and two quadrics is
the actual base change of the full universal intersection family. -/
noncomputable def cubicTwoQuadricUniversalIntersectionBaseChangeIso
    {L : Type u} [Field L] {n : ℕ}
    (f : K →+* L)
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 2)
    (c : Fin n → L) :
    scheme (tripleCompleteIntersectionHomogeneousIdeal
      (p.map f) (q.map f)
      ((cubicTwoQuadricUniversalQuadric v).map (MvPolynomial.eval₂Hom f c))
      (hp.map f) (hq.map f)
      ((cubicTwoQuadricUniversalQuadric_isHomogeneous v).map
        (MvPolynomial.eval₂Hom f c))) ≅
    pullback (cubicTwoQuadricUniversalIntersectionToCone p q hp hq v)
      (Spec.map (CommRingCat.ofHom (MvPolynomial.eval₂Hom f c))) := by
  apply projectiveBaseChangeIso (MvPolynomial.eval₂Hom f c)
    (cubicTwoQuadricUniversalIntersectionIdeal p q hp hq v)
    (tripleCompleteIntersectionHomogeneousIdeal
      (p.map f) (q.map f)
      ((cubicTwoQuadricUniversalQuadric v).map (MvPolynomial.eval₂Hom f c))
      (hp.map f) (hq.map f)
      ((cubicTwoQuadricUniversalQuadric_isHomogeneous v).map
        (MvPolynomial.eval₂Hom f c)))
  exact (cubicTwoQuadricUniversalIntersectionIdeal_map f p q hp hq v c).trans
    (tripleCompleteIntersectionHomogeneousIdeal_toIdeal _ _ _ _ _ _).symm

/-- A finite specialized projective intersection supplies a finite fibre of
the actual universal family at its field-valued parameter. -/
theorem cubicTwoQuadricUniversalIntersection_finiteFibre_of_finiteSpecialization
    {L : Type u} [Field L] {n : ℕ}
    (f : K →+* L)
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 2)
    (c : Fin n → L)
    [IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal
      (p.map f) (q.map f)
      ((cubicTwoQuadricUniversalQuadric v).map (MvPolynomial.eval₂Hom f c))
      (hp.map f) (hq.map f)
      ((cubicTwoQuadricUniversalQuadric_isHomogeneous v).map
        (MvPolynomial.eval₂Hom f c))))] :
    ((cubicTwoQuadricUniversalIntersectionToCone p q hp hq v) ⁻¹'
      {Spec.map (CommRingCat.ofHom (MvPolynomial.eval₂Hom f c))
        (IsLocalRing.closedPoint L)}).Finite := by
  let J := tripleCompleteIntersectionHomogeneousIdeal
    (p.map f) (q.map f)
    ((cubicTwoQuadricUniversalQuadric v).map (MvPolynomial.eval₂Hom f c))
    (hp.map f) (hq.map f)
    ((cubicTwoQuadricUniversalQuadric_isHomogeneous v).map
      (MvPolynomial.eval₂Hom f c))
  let g := Spec.map (CommRingCat.ofHom (MvPolynomial.eval₂Hom f c))
  let e := cubicTwoQuadricUniversalIntersectionBaseChangeIso f p q hp hq v c
  have hArtinian : IsArtinianScheme (scheme J) := finiteScheme_isArtinian (toBase J)
  letI := hArtinian
  have hsource : (Set.range (e.hom ≫
      pullback.fst (cubicTwoQuadricUniversalIntersectionToCone p q hp hq v) g)).Finite :=
    by simpa only [Set.image_univ] using
      (Set.finite_univ.image (e.hom ≫
        pullback.fst (cubicTwoQuadricUniversalIntersectionToCone p q hp hq v) g))
  have hrange : Set.range g = {g (IsLocalRing.closedPoint L)} := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact Set.mem_singleton_iff.mpr (congrArg g (Subsingleton.elim x _))
    · intro hy
      exact ⟨IsLocalRing.closedPoint L, hy.symm⟩
  have he : Set.range (e.hom ≫
      pullback.fst (cubicTwoQuadricUniversalIntersectionToCone p q hp hq v) g) =
      (cubicTwoQuadricUniversalIntersectionToCone p q hp hq v) ⁻¹'
        {g (IsLocalRing.closedPoint L)} := by
    have hbase : Set.range
        (pullback.fst (cubicTwoQuadricUniversalIntersectionToCone p q hp hq v) g) =
        (cubicTwoQuadricUniversalIntersectionToCone p q hp hq v) ⁻¹'
          {g (IsLocalRing.closedPoint L)} := by
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

/-- One finite member makes the full universal intersection finite on an
open neighborhood of the generic quadratic parameter. This is the exact
generic-transfer conclusion needed after constructing a single proper
intersection witness. -/
theorem cubicTwoQuadricUniversalIntersection_exists_genericFiniteNeighborhood
    {n : ℕ} (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 2)
    (y : Spec (.of (MvPolynomial (Fin n) K)))
    (hy : ((cubicTwoQuadricUniversalIntersectionToCone p q hp hq v) ⁻¹' {y}).Finite) :
    ∃ V : (Spec (.of (MvPolynomial (Fin n) K))).Opens,
      genericPoint (Spec (.of (MvPolynomial (Fin n) K))) ∈ V ∧
      IsFinite ((cubicTwoQuadricUniversalIntersectionToCone p q hp hq v) ∣_ V) := by
  exact exists_genericPoint_finite_restriction_of_one_finite_fibre
    (cubicTwoQuadricUniversalIntersectionToCone p q hp hq v) y hy

/-- A regular specialized cubic--quadric--quadric member makes the actual
universal family finite on an open neighborhood of its generic parameter. -/
theorem cubicTwoQuadricUniversalIntersection_exists_genericFiniteNeighborhood_of_regularSpecialization
    {L : Type u} [Field L] {n : ℕ}
    (f : K →+* L)
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 2)
    (c : Fin n → L)
    (hp0 : p.map f ≠ 0) (hq0 : q.map f ≠ 0)
    (hrel : IsRelPrime (p.map f) (q.map f))
    (hregular : ∀ x : MvPolynomial (Fin 4) L,
      (cubicTwoQuadricUniversalQuadric v).map (MvPolynomial.eval₂Hom f c) * x ∈
        Ideal.span ({p.map f, q.map f} : Set (MvPolynomial (Fin 4) L)) →
      x ∈ Ideal.span ({p.map f, q.map f} : Set (MvPolynomial (Fin 4) L))) :
    ∃ V : (Spec (.of (MvPolynomial (Fin n) K))).Opens,
      genericPoint (Spec (.of (MvPolynomial (Fin n) K))) ∈ V ∧
      IsFinite ((cubicTwoQuadricUniversalIntersectionToCone p q hp hq v) ∣_ V) := by
  letI : IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal
      (p.map f) (q.map f)
      ((cubicTwoQuadricUniversalQuadric v).map (MvPolynomial.eval₂Hom f c))
      (hp.map f) (hq.map f)
      ((cubicTwoQuadricUniversalQuadric_isHomogeneous v).map
        (MvPolynomial.eval₂Hom f c)))) :=
    cubic_two_quadrics_intersection_finite _ _ _ _ _ _ hp0 hq0 hrel hregular
  exact cubicTwoQuadricUniversalIntersection_exists_genericFiniteNeighborhood
    p q hp hq v _
    (cubicTwoQuadricUniversalIntersection_finiteFibre_of_finiteSpecialization
      f p q hp hq v c)

end PfaffianDescent
