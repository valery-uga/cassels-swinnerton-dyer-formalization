import PfaffianDescent.TripleQuadricsFiniteRegularity
import PfaffianDescent.VoisinFiniteFieldBaseChangeDescent

/-! Descent of finite cubic--two-quadric intersections along field extension. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- If the coefficient extension of a homogeneous triple intersection is
finite, then the original projective intersection is finite. -/
theorem tripleCompleteIntersection_isFinite_of_isFinite_coefficientExtension
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (p q r : MvPolynomial (Fin 4) K) {a b c : ℕ}
    (hp : p.IsHomogeneous a) (hq : q.IsHomogeneous b)
    (hr : r.IsHomogeneous c)
    [IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal
      (p.map (algebraMap K L)) (q.map (algebraMap K L))
      (r.map (algebraMap K L)) (hp.map (algebraMap K L))
      (hq.map (algebraMap K L)) (hr.map (algebraMap K L))))] :
    IsFinite (toBase
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) := by
  let I := tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr
  let J := tripleCompleteIntersectionHomogeneousIdeal
    (p.map (algebraMap K L)) (q.map (algebraMap K L))
    (r.map (algebraMap K L)) (hp.map (algebraMap K L))
    (hq.map (algebraMap K L)) (hr.map (algebraMap K L))
  have hIJ : I.toIdeal.map (MvPolynomial.map (algebraMap K L)) = J.toIdeal :=
    tripleCompleteIntersection_map_coefficientExtension p q r hp hq hr
  let g : Spec (.of L) ⟶ Spec (.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K L))
  let e : scheme J ≅ pullback (toBase I) g :=
    projectiveBaseChangeIso (algebraMap K L) I J hIJ
  have he : e.hom ≫ pullback.snd (toBase I) g = toBase J :=
    projectiveBaseChangeIso_hom_snd (algebraMap K L) I J hIJ
  haveI : IsFinite (e.inv ≫ (e.hom ≫ pullback.snd (toBase I) g)) := by
    rw [he]
    infer_instance
  haveI : IsFinite (pullback.snd (toBase I) g) := by
    simpa only [Iso.inv_hom_id_assoc] using
      (inferInstance : IsFinite
        (e.inv ≫ (e.hom ≫ pullback.snd (toBase I) g)))
  exact isFinite_of_isFinite_fieldBaseChange (L := L) (toBase I)

end PfaffianDescent
