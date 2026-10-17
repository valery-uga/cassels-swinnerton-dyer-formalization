import PfaffianDescent.HomogeneousInterpolationCorrection

/-!
An actual finite specialization of an interpolation-corrected cubic pair
gives a finite neighborhood of the generic parameter. Both corrected
equations vanish at the marked configuration by construction.
-/

namespace PfaffianDescent

open MvPolynomial AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem cubicInterpolationCorrectedPair_exists_genericFiniteNeighborhood
    {R : Type u} [CommRing R] [IsDomain R]
    {F : Type u} [Field F] {n : ℕ}
    (f : R →+* F)
    (frame : Fin n → MvPolynomial (Fin 4) R) (x : Fin n → Fin 4 → R)
    (hframe : ∀ i, (frame i).IsHomogeneous 3)
    (hdet : IsUnit (homogeneousFrameEvaluationMatrix frame x).det)
    (p q r : MvPolynomial (Fin 4) R)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3) (hr : r.IsHomogeneous 3)
    (hqzero : ∀ i, (q.map f).eval (fun j => f (x i j)) = 0)
    (hrzero : ∀ i, (r.map f).eval (fun j => f (x i j)) = 0)
    [IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal
      (p.map f) (q.map f) (r.map f) (hp.map f) (hq.map f) (hr.map f)))] :
    let Q := homogeneousInterpolationCorrection frame x q
    let T := homogeneousInterpolationCorrection frame x r
    let hQ := homogeneousInterpolationCorrection_isHomogeneous frame x q hframe hq
    let hT := homogeneousInterpolationCorrection_isHomogeneous frame x r hframe hr
    (∀ i, Q.eval (x i) = 0 ∧ T.eval (x i) = 0) ∧
      ∃ V : (Spec (.of R)).Opens,
        genericPoint (Spec (.of R)) ∈ V ∧
        IsFinite ((relativeHomogeneousTripleIntersectionToBase p Q T hp hQ hT) ∣_ V) := by
  dsimp only
  let Q := homogeneousInterpolationCorrection frame x q
  let T := homogeneousInterpolationCorrection frame x r
  have hQ := homogeneousInterpolationCorrection_isHomogeneous frame x q hframe hq
  have hT := homogeneousInterpolationCorrection_isHomogeneous frame x r hframe hr
  have hQmap : Q.map f = q.map f :=
    homogeneousInterpolationCorrection_map_eq f frame x q hqzero
  have hTmap : T.map f = r.map f :=
    homogeneousInterpolationCorrection_map_eq f frame x r hrzero
  have hideal :
      tripleCompleteIntersectionHomogeneousIdeal
        (p.map f) (Q.map f) (T.map f) (hp.map f) (hQ.map f) (hT.map f) =
      tripleCompleteIntersectionHomogeneousIdeal
        (p.map f) (q.map f) (r.map f) (hp.map f) (hq.map f) (hr.map f) := by
    apply HomogeneousIdeal.ext
    simp only [tripleCompleteIntersectionHomogeneousIdeal_toIdeal,
      tripleCompleteIntersectionIdeal, hQmap, hTmap]
  letI : IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal
      (p.map f) (Q.map f) (T.map f) (hp.map f) (hQ.map f) (hT.map f))) := by
    rw [hideal]
    infer_instance
  refine ⟨?_, ?_⟩
  · intro i
    exact ⟨homogeneousInterpolationCorrection_eval_zero frame x q hdet i,
      homogeneousInterpolationCorrection_eval_zero frame x r hdet i⟩
  · exact relativeHomogeneousTripleIntersection_exists_genericFiniteNeighborhood_of_finiteTripleSpecialization
      f p Q T hp hQ hT

end PfaffianDescent
