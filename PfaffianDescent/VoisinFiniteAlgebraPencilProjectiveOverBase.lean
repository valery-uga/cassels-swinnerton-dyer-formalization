import PfaffianDescent.VoisinFiniteAlgebraPencilProjectiveDescent
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import PfaffianDescent.VoisinFiniteFieldBaseChangeDescent

/-! Projective base-change comparisons retaining their map to the extension field. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A projective comparison accompanied by its equality over the base field. -/
structure TripleProjectiveComparisonOverBase
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hr : r.IsHomogeneous 2)
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) L)) where
  iso : scheme I ≅ pullback (relativeTripleIntersectionToBase
    p q r hp hq hr) (Spec.map (CommRingCat.ofHom (algebraMap K L)))
  hom_snd : iso.hom ≫ pullback.snd (relativeTripleIntersectionToBase
    p q r hp hq hr) (Spec.map (CommRingCat.ofHom (algebraMap K L))) =
    toBase I

/-- Equality with the coefficient-changed triple ideal yields the canonical
base-preserving projective comparison. -/
noncomputable def tripleProjectiveComparisonOverBase_of_ideal_eq
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hr : r.IsHomogeneous 2)
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) L))
    (hI : I = relativeTripleIntersectionHomogeneousIdeal
      (p.map (algebraMap K L)) (q.map (algebraMap K L))
      (r.map (algebraMap K L)) (hp.map (algebraMap K L))
      (hq.map (algebraMap K L)) (hr.map (algebraMap K L))) :
    TripleProjectiveComparisonOverBase p q r hp hq hr I := by
  subst I
  refine ⟨relativeTripleIntersectionBaseChangeIso
    (algebraMap K L) p q r hp hq hr, ?_⟩
  exact projectiveBaseChangeIso_hom_snd _ _ _
    (relativeTripleIntersectionHomogeneousIdeal_map
      (algebraMap K L) p q r hp hq hr)

/-- The intrinsic ordered intersection has a base-preserving isomorphism
with the pullback of the unordered quadratic-pencil intersection. -/
noncomputable def quadraticHomogeneousPair_intrinsicProjectiveComparisonOverBase
    {K A L : Type u} [Field K] [CommRing A] [Algebra K A]
    [Field L] [Algebra K L]
    (φ : Fin 8 → A →ₐ[K] L)
    (hφ : Function.Injective (fun t : A => fun i => φ i t))
    (x : Fin 4 → A)
    (q : Fin 2 → homogeneousSubmodule (Fin 4) K 2)
    (hq : LinearIndependent K q)
    (hzero : ∀ i, (q i).1.eval₂ (algebraMap K A) x = 0)
    (m : Fin 8 ↪ Monomials (Fin 4) 2)
    (hminor : IsUnit (eightPointQuadraticEvaluationMinor m
      (fun i j => φ i (x j))).det)
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) :
    TripleProjectiveComparisonOverBase
      p (q 0).1 (q 1).1 hp (q 0).2 (q 1).2
      (intrinsicEightPointTripleHomogeneousIdeal
        (p.map (algebraMap K L)) (hp.map (algebraMap K L))
        (fun i j => φ i (x j))) :=
  tripleProjectiveComparisonOverBase_of_ideal_eq
    p (q 0).1 (q 1).1 hp (q 0).2 (q 1).2 _
    (quadraticHomogeneousPair_intrinsicHomogeneousIdeal_eq_relative
      φ hφ x q hq hzero m hminor p hp)

/-- Finiteness of the intrinsic ordered intersection transfers to the
pullback of the unordered pencil along the ordered field extension. -/
theorem TripleProjectiveComparisonOverBase.isFinite_pullback
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hr : r.IsHomogeneous 2)
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) L))
    (C : TripleProjectiveComparisonOverBase p q r hp hq hr I)
    [IsFinite (toBase I)] :
    IsFinite (pullback.snd (relativeTripleIntersectionToBase p q r hp hq hr)
      (Spec.map (CommRingCat.ofHom (algebraMap K L)))) := by
  haveI : IsFinite (C.iso.hom ≫
      pullback.snd (relativeTripleIntersectionToBase p q r hp hq hr)
        (Spec.map (CommRingCat.ofHom (algebraMap K L)))) := by
    rw [C.hom_snd]
    infer_instance
  haveI : IsFinite (C.iso.inv ≫ (C.iso.hom ≫
      pullback.snd (relativeTripleIntersectionToBase p q r hp hq hr)
        (Spec.map (CommRingCat.ofHom (algebraMap K L))))) := inferInstance
  simpa only [Iso.inv_hom_id_assoc] using this

/-- Intrinsic ordered-fiber finiteness now descends all the way to the
unordered cubic--quadratic-pencil intersection over its coefficient field. -/
theorem TripleProjectiveComparisonOverBase.isFinite_unordered
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hr : r.IsHomogeneous 2)
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) L))
    (C : TripleProjectiveComparisonOverBase p q r hp hq hr I)
    [IsFinite (toBase I)] :
    IsFinite (relativeTripleIntersectionToBase p q r hp hq hr) := by
  letI : IsFinite (pullback.snd
      (relativeTripleIntersectionToBase p q r hp hq hr)
      (Spec.map (CommRingCat.ofHom (algebraMap K L)))) :=
    C.isFinite_pullback p q r hp hq hr I
  exact isFinite_of_isFinite_fieldBaseChange (L := L)
    (relativeTripleIntersectionToBase p q r hp hq hr)

end PfaffianDescent
