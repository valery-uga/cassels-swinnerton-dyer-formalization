import PfaffianDescent.HomogeneousInterpolationCorrectedFiniteFamily
import PfaffianDescent.HomogeneousMonomialMinorOpenChart

/-!
A finite specialization with independent marked cubic evaluations gives an
actual corrected cubic pair on a nonempty determinant open. The monomial
frame, its determinant, its localization and its specialization lift are
constructed internally from the marked evaluation map.
-/

namespace PfaffianDescent

open MvPolynomial AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable def homogeneousMinorMonomialFrame
    {R : Type u} [CommRing R] {n d : ℕ}
    (m : Fin n ↪ Monomials (Fin 4) d) : Fin n → MvPolynomial (Fin 4) R :=
  fun i => MvPolynomial.monomial (m i).1 1

theorem homogeneousMinorMonomialFrame_isHomogeneous
    {R : Type u} [CommRing R] {n d : ℕ}
    (m : Fin n ↪ Monomials (Fin 4) d) (i : Fin n) :
    (homogeneousMinorMonomialFrame (R := R) m i).IsHomogeneous d :=
  isHomogeneous_monomial 1 (m i).2

theorem homogeneousMinorMonomialFrame_evaluationMatrix
    {R : Type u} [CommRing R] {n d : ℕ}
    (m : Fin n ↪ Monomials (Fin 4) d) (x : Fin n → Fin 4 → R) :
    homogeneousFrameEvaluationMatrix (homogeneousMinorMonomialFrame m) x =
      homogeneousPointEvaluationMinor m x := rfl

noncomputable def homogeneousMinorCorrectedPolynomial
    {R : Type u} [CommRing R] {n d : ℕ}
    (m : Fin n ↪ Monomials (Fin 4) d) (x : Fin n → Fin 4 → R)
    (q : MvPolynomial (Fin 4) R) :
    MvPolynomial (Fin 4) (Localization.Away (homogeneousMinorDet m x)) :=
  homogeneousInterpolationCorrection (homogeneousMinorMonomialFrame m)
    (fun i j => algebraMap R (Localization.Away (homogeneousMinorDet m x)) (x i j))
    (q.map (algebraMap R (Localization.Away (homogeneousMinorDet m x))))

theorem homogeneousMinorCorrectedPolynomial_isHomogeneous
    {R : Type u} [CommRing R] {n d : ℕ}
    (m : Fin n ↪ Monomials (Fin 4) d) (x : Fin n → Fin 4 → R)
    (q : MvPolynomial (Fin 4) R) (hq : q.IsHomogeneous d) :
    (homogeneousMinorCorrectedPolynomial m x q).IsHomogeneous d :=
  homogeneousInterpolationCorrection_isHomogeneous _ _ _
    (homogeneousMinorMonomialFrame_isHomogeneous m) (hq.map _)

set_option backward.isDefEq.respectTransparency false in
theorem homogeneousMinorCorrectedPolynomial_eval_zero
    {R : Type u} [CommRing R] {n d : ℕ}
    (m : Fin n ↪ Monomials (Fin 4) d) (x : Fin n → Fin 4 → R)
    (q : MvPolynomial (Fin 4) R) (i : Fin n) :
    (homogeneousMinorCorrectedPolynomial m x q).eval
      (fun j => algebraMap R (Localization.Away (homogeneousMinorDet m x)) (x i j)) = 0 := by
  let S := Localization.Away (homogeneousMinorDet m x)
  let a := algebraMap R S
  have hdet : IsUnit (homogeneousFrameEvaluationMatrix
      (homogeneousMinorMonomialFrame (R := S) m) (fun i j => a (x i j))).det := by
    rw [homogeneousMinorMonomialFrame_evaluationMatrix,
      ← homogeneousPointEvaluationMinor_map]
    exact homogeneousMinor_isUnit_on_principalOpen m x
  exact homogeneousInterpolationCorrection_eval_zero
    (homogeneousMinorMonomialFrame (R := S) m) (fun i j => a (x i j)) (q.map a) hdet i

set_option backward.isDefEq.respectTransparency false in
theorem cubicMinorCorrectedPair_exists_genericFiniteNeighborhood
    {R : Type u} [CommRing R] [IsDomain R]
    {F : Type u} [Field F] {n : ℕ}
    (f : R →+* F) (m : Fin n ↪ Monomials (Fin 4) 3)
    (x : Fin n → Fin 4 → R)
    (hm : IsUnit (homogeneousPointEvaluationMinor m (fun i j => f (x i j))).det)
    (p q r : MvPolynomial (Fin 4) R)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3) (hr : r.IsHomogeneous 3)
    (hqzero : ∀ i, (q.map f).eval (fun j => f (x i j)) = 0)
    (hrzero : ∀ i, (r.map f).eval (fun j => f (x i j)) = 0)
    [IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal
      (p.map f) (q.map f) (r.map f) (hp.map f) (hq.map f) (hr.map f)))] :
    let S := Localization.Away (homogeneousMinorDet m x)
    letI : IsDomain S := Localization.Away.isDomain
      (homogeneousMinorDet_ne_zero_of_specialized_unit m x f hm)
    ∃ V : (Spec (.of S)).Opens,
      genericPoint (Spec (.of S)) ∈ V ∧
      IsFinite ((relativeHomogeneousTripleIntersectionToBase
        (p.map (algebraMap R S))
        (homogeneousMinorCorrectedPolynomial m x q)
        (homogeneousMinorCorrectedPolynomial m x r)
        (hp.map (algebraMap R S))
        (homogeneousMinorCorrectedPolynomial_isHomogeneous m x q hq)
        (homogeneousMinorCorrectedPolynomial_isHomogeneous m x r hr)) ∣_ V) := by
  dsimp only
  let S := Localization.Away (homogeneousMinorDet m x)
  letI : IsDomain S := Localization.Away.isDomain
    (homogeneousMinorDet_ne_zero_of_specialized_unit m x f hm)
  let a := algebraMap R S
  let fS := homogeneousMinorSelectedPointLift m x f hm
  have hcomp : fS.comp a = f := homogeneousMinorSelectedPointLift_comp m x f hm
  have hmap (s : MvPolynomial (Fin 4) R) : (s.map a).map fS = s.map f := by
    rw [MvPolynomial.map_map, hcomp]
  have hxmap (i : Fin n) (j : Fin 4) : fS (a (x i j)) = f (x i j) :=
    congrArg (fun g : R →+* F => g (x i j)) hcomp
  have hideal :
      tripleCompleteIntersectionHomogeneousIdeal
        ((p.map a).map fS) ((q.map a).map fS) ((r.map a).map fS)
        ((hp.map a).map fS) ((hq.map a).map fS) ((hr.map a).map fS) =
      tripleCompleteIntersectionHomogeneousIdeal
        (p.map f) (q.map f) (r.map f) (hp.map f) (hq.map f) (hr.map f) := by
    apply HomogeneousIdeal.ext
    simp only [tripleCompleteIntersectionHomogeneousIdeal_toIdeal,
      tripleCompleteIntersectionIdeal, hmap]
  letI : IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal
      ((p.map a).map fS) ((q.map a).map fS) ((r.map a).map fS)
      ((hp.map a).map fS) ((hq.map a).map fS) ((hr.map a).map fS))) := by
    rw [hideal]
    infer_instance
  have hqS : ∀ i, ((q.map a).map fS).eval (fun j => fS (a (x i j))) = 0 := by
    intro i
    simpa only [hmap, hxmap] using hqzero i
  have hrS : ∀ i, ((r.map a).map fS).eval (fun j => fS (a (x i j))) = 0 := by
    intro i
    simpa only [hmap, hxmap] using hrzero i
  have hframe : ∀ j, (homogeneousMinorMonomialFrame (R := S) m j).IsHomogeneous 3 :=
    homogeneousMinorMonomialFrame_isHomogeneous m
  have hdet : IsUnit (homogeneousFrameEvaluationMatrix
      (homogeneousMinorMonomialFrame m) (fun i j => a (x i j))).det := by
    rw [homogeneousMinorMonomialFrame_evaluationMatrix,
      ← homogeneousPointEvaluationMinor_map]
    exact homogeneousMinor_isUnit_on_principalOpen m x
  exact (cubicInterpolationCorrectedPair_exists_genericFiniteNeighborhood
    fS (homogeneousMinorMonomialFrame m) (fun i j => a (x i j)) hframe hdet
    (p.map a) (q.map a) (r.map a) (hp.map a) (hq.map a) (hr.map a) hqS hrS).2

/-- Independent marked cubic values and an actual finite specialization
construct a finite generic corrected pair, without any supplied minor or
interpolation-frame certificate. -/
theorem cubicMonomialCorrection_exists_genericFiniteNeighborhood_of_finiteWitness
    {R : Type u} [CommRing R] [IsDomain R]
    {F : Type u} [Field F] {n : ℕ}
    (f : R →+* F) (x : Fin n → Fin 4 → R)
    (hsurj : Function.Surjective (homogeneousSectionRestriction (K := F)
      (fun j i => f (x i j)) 3))
    (p q r : MvPolynomial (Fin 4) R)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3) (hr : r.IsHomogeneous 3)
    (hqzero : ∀ i, (q.map f).eval (fun j => f (x i j)) = 0)
    (hrzero : ∀ i, (r.map f).eval (fun j => f (x i j)) = 0)
    [IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal
      (p.map f) (q.map f) (r.map f) (hp.map f) (hq.map f) (hr.map f)))] :
    ∃ (m : Fin n ↪ Monomials (Fin 4) 3) (hdet : homogeneousMinorDet m x ≠ 0),
      let S := Localization.Away (homogeneousMinorDet m x)
      letI : IsDomain S := Localization.Away.isDomain hdet
      (∀ i, (homogeneousMinorCorrectedPolynomial m x q).eval
          (fun j => algebraMap R S (x i j)) = 0 ∧
        (homogeneousMinorCorrectedPolynomial m x r).eval
          (fun j => algebraMap R S (x i j)) = 0) ∧
      ∃ V : (Spec (.of S)).Opens,
        genericPoint (Spec (.of S)) ∈ V ∧
        IsFinite ((relativeHomogeneousTripleIntersectionToBase
          (p.map (algebraMap R S))
          (homogeneousMinorCorrectedPolynomial m x q)
          (homogeneousMinorCorrectedPolynomial m x r)
          (hp.map (algebraMap R S))
          (homogeneousMinorCorrectedPolynomial_isHomogeneous m x q hq)
          (homogeneousMinorCorrectedPolynomial_isHomogeneous m x r hr)) ∣_ V) := by
  obtain ⟨m, hm⟩ := exists_unit_homogeneousPointEvaluationMinor_of_restriction
    n 3 (fun i j => f (x i j)) hsurj
  have hdet := homogeneousMinorDet_ne_zero_of_specialized_unit m x f hm
  refine ⟨m, hdet, ?_, ?_⟩
  · intro i
    exact ⟨homogeneousMinorCorrectedPolynomial_eval_zero m x q i,
      homogeneousMinorCorrectedPolynomial_eval_zero m x r i⟩
  · exact cubicMinorCorrectedPair_exists_genericFiniteNeighborhood
      f m x hm p q r hp hq hr hqzero hrzero

end PfaffianDescent
