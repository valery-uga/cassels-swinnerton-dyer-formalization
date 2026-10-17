import PfaffianDescent.VoisinRelativeTripleIntersectionFamily
import PfaffianDescent.VoisinGenericTripleFinite
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! An equality with a specialized relative triple-intersection ideal
identifies its projective scheme with the actual pullback fiber. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable def intrinsicIdeal_scheme_iso_relativeTripleBaseChange
    {R F : Type u} [CommRing R] [Field F]
    (g : R →+* F)
    (p q r : MvPolynomial (Fin 4) R)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hr : r.IsHomogeneous 2)
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) F))
    (hI : I = relativeTripleIntersectionHomogeneousIdeal
      (p.map g) (q.map g) (r.map g)
      (hp.map g) (hq.map g) (hr.map g)) :
    scheme I ≅
      pullback (relativeTripleIntersectionToBase p q r hp hq hr)
        (Spec.map (CommRingCat.ofHom g)) := by
  subst I
  exact relativeTripleIntersectionBaseChangeIso g p q r hp hq hr

/-- The comparison with the actual pullback fiber preserves its map to
the residue field. -/
theorem intrinsicIdeal_scheme_iso_relativeTripleBaseChange_hom_snd
    {R F : Type u} [CommRing R] [Field F]
    (g : R →+* F)
    (p q r : MvPolynomial (Fin 4) R)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hr : r.IsHomogeneous 2)
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) F))
    (hI : I = relativeTripleIntersectionHomogeneousIdeal
      (p.map g) (q.map g) (r.map g)
      (hp.map g) (hq.map g) (hr.map g)) :
    (intrinsicIdeal_scheme_iso_relativeTripleBaseChange
      g p q r hp hq hr I hI).hom ≫
      pullback.snd (relativeTripleIntersectionToBase p q r hp hq hr)
        (Spec.map (CommRingCat.ofHom g)) = toBase I := by
  subst I
  exact projectiveBaseChangeIso_hom_snd _ _ _
    (relativeTripleIntersectionHomogeneousIdeal_map g p q r hp hq hr)

/-- Finiteness of the intrinsic field scheme transfers to the actual
base-change fiber of the relative triple intersection. -/
theorem intrinsicIdeal_isFinite_relativeTripleBaseChange
    {R F : Type u} [CommRing R] [Field F]
    (g : R →+* F)
    (p q r : MvPolynomial (Fin 4) R)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hr : r.IsHomogeneous 2)
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) F))
    (hI : I = relativeTripleIntersectionHomogeneousIdeal
      (p.map g) (q.map g) (r.map g)
      (hp.map g) (hq.map g) (hr.map g))
    [IsFinite (toBase I)] :
    IsFinite (pullback.snd (relativeTripleIntersectionToBase
      p q r hp hq hr) (Spec.map (CommRingCat.ofHom g))) := by
  let e := intrinsicIdeal_scheme_iso_relativeTripleBaseChange
    g p q r hp hq hr I hI
  have hbase : e.hom ≫ pullback.snd
      (relativeTripleIntersectionToBase p q r hp hq hr)
      (Spec.map (CommRingCat.ofHom g)) = toBase I :=
    intrinsicIdeal_scheme_iso_relativeTripleBaseChange_hom_snd
      g p q r hp hq hr I hI
  haveI : IsFinite (e.hom ≫ pullback.snd
      (relativeTripleIntersectionToBase p q r hp hq hr)
      (Spec.map (CommRingCat.ofHom g))) := by
    rw [hbase]
    infer_instance
  haveI : IsFinite (e.inv ≫ (e.hom ≫ pullback.snd
      (relativeTripleIntersectionToBase p q r hp hq hr)
      (Spec.map (CommRingCat.ofHom g)))) := inferInstance
  simpa only [Iso.inv_hom_id_assoc] using this

/-- The actual intrinsic field scheme is finite when its relative triple
family is finite near the generic point and the field point is generic. -/
theorem intrinsicIdeal_isFinite_at_injectiveFieldPoint_of_finiteNeighborhood
    {R F : Type u} [CommRing R] [IsDomain R] [Field F]
    (p q r : MvPolynomial (Fin 4) R)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hr : r.IsHomogeneous 2)
    (V : (Spec (.of R)).Opens)
    (hη : genericPoint (Spec (.of R)) ∈ V)
    [IsFinite ((relativeTripleIntersectionToBase p q r hp hq hr) ∣_ V)]
    (g : R →+* F) (hg : Function.Injective g)
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) F))
    (hI : I = relativeTripleIntersectionHomogeneousIdeal
      (p.map g) (q.map g) (r.map g)
      (hp.map g) (hq.map g) (hr.map g)) :
    IsFinite (toBase I) := by
  rw [hI]
  exact relativeTripleIntersection_isFinite_at_injectiveFieldPoint_of_finiteNeighborhood
    p q r hp hq hr V hη g hg

end PfaffianDescent
