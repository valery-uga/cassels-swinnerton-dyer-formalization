import PfaffianDescent.VoisinRelativeTripleIntersectionFamily
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! Finiteness of a cubic--two-quadrics family survives coefficient base change. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A finite relative cubic--two-quadrics intersection remains finite after
any change of its coefficient ring. -/
theorem relativeTripleIntersection_isFinite_map
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S)
    (p q r : MvPolynomial (Fin 4) R)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hr : r.IsHomogeneous 2)
    [IsFinite (relativeTripleIntersectionToBase p q r hp hq hr)] :
    IsFinite (relativeTripleIntersectionToBase
      (p.map f) (q.map f) (r.map f)
      (hp.map f) (hq.map f) (hr.map f)) := by
  let e := relativeTripleIntersectionBaseChangeIso f p q r hp hq hr
  have he : e.hom ≫ pullback.snd
      (relativeTripleIntersectionToBase p q r hp hq hr)
      (Spec.map (CommRingCat.ofHom f)) =
      relativeTripleIntersectionToBase
        (p.map f) (q.map f) (r.map f)
        (hp.map f) (hq.map f) (hr.map f) := by
    exact projectiveBaseChangeIso_hom_snd _ _ _
      (relativeTripleIntersectionHomogeneousIdeal_map f p q r hp hq hr)
  rw [← he]
  infer_instance

end PfaffianDescent
