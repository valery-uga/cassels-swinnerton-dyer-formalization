import PfaffianDescent.CubicFullJetEvaluationMatrix

/-!
Coefficient-map compatibility and the actual determinant localization of
the full seventeen-condition cubic interpolation matrix.
-/

namespace PfaffianDescent

open MvPolynomial Module
open AllCharacteristics.UniversalHomogeneous

universe u v
set_option backward.isDefEq.respectTransparency false

theorem homogeneousFullJetEvaluationMatrix_map
    {R : Type u} [CommRing R] {S : Type v} [CommRing S]
    (f : R →+* S) (d : ℕ) (x : Fin 11 → Fin 4 → R)
    (v : Fin 3 → Fin 4 → Fin 2 → R) :
    (homogeneousFullJetEvaluationMatrix d x v).map f =
      homogeneousFullJetEvaluationMatrix d (fun i j => f (x i j))
        (fun i j t => f (v i j t)) := by
  ext r m
  rcases r with i | ⟨i, t⟩
  · simp [homogeneousFullJetEvaluationMatrix, MvPolynomial.map_eval,
      MvPolynomial.map_monomial, Function.comp_def]
  · change f (∑ j : Fin 4, (pderiv j (monomial m.1 (1 : R))).eval
      (x (i.castAdd 8)) * v i j t) =
      ∑ j : Fin 4, (pderiv j (monomial m.1 (1 : S))).eval
        (fun k => f (x (i.castAdd 8) k)) * f (v i j t)
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j _
    have he : MvPolynomial.map f (pderiv j (monomial m.1 (1 : R))) =
        pderiv j (monomial m.1 (1 : S)) := by
      rw [← MvPolynomial.pderiv_map, MvPolynomial.map_monomial, map_one]
    rw [map_mul, MvPolynomial.map_eval, he]
    rfl

theorem homogeneousFullJetEvaluationMinor_map
    {R : Type u} [CommRing R] {S : Type v} [CommRing S] {d : ℕ}
    (f : R →+* S) (m : CubicFullJetCondition ↪ Monomials (Fin 4) d)
    (x : Fin 11 → Fin 4 → R) (v : Fin 3 → Fin 4 → Fin 2 → R) :
    (homogeneousFullJetEvaluationMinor m x v).map f =
      homogeneousFullJetEvaluationMinor m (fun i j => f (x i j))
        (fun i j t => f (v i j t)) := by
  have h := homogeneousFullJetEvaluationMatrix_map f d x v
  exact congrArg (fun M => M.submatrix id m) h

noncomputable def homogeneousFullJetMinorDet
    {R : Type u} [CommRing R] {d : ℕ}
    (m : CubicFullJetCondition ↪ Monomials (Fin 4) d)
    (x : Fin 11 → Fin 4 → R) (v : Fin 3 → Fin 4 → Fin 2 → R) : R :=
  (homogeneousFullJetEvaluationMinor m x v).det

theorem homogeneousFullJetMinorDet_ne_zero_of_specialized_unit
    {R : Type u} [CommRing R] {F : Type v} [Field F] {d : ℕ}
    (m : CubicFullJetCondition ↪ Monomials (Fin 4) d)
    (x : Fin 11 → Fin 4 → R) (v : Fin 3 → Fin 4 → Fin 2 → R)
    (f : R →+* F)
    (h : IsUnit (homogeneousFullJetEvaluationMinor m (fun i j => f (x i j))
      (fun i j t => f (v i j t))).det) :
    homogeneousFullJetMinorDet m x v ≠ 0 := by
  intro hz
  have heq : f (homogeneousFullJetMinorDet m x v) =
      (homogeneousFullJetEvaluationMinor m (fun i j => f (x i j))
        (fun i j t => f (v i j t))).det := by
    rw [homogeneousFullJetMinorDet, RingHom.map_det,
      RingHom.mapMatrix_apply, homogeneousFullJetEvaluationMinor_map]
  rw [hz, map_zero] at heq
  exact h.ne_zero heq.symm

theorem homogeneousFullJetMinor_isUnit_on_principalOpen
    {R : Type u} [CommRing R] {d : ℕ}
    (m : CubicFullJetCondition ↪ Monomials (Fin 4) d)
    (x : Fin 11 → Fin 4 → R) (v : Fin 3 → Fin 4 → Fin 2 → R) :
    IsUnit ((homogeneousFullJetEvaluationMinor m x v).map
      (algebraMap R (Localization.Away (homogeneousFullJetMinorDet m x v)))).det := by
  have hmap : ((homogeneousFullJetEvaluationMinor m x v).map
      (algebraMap R (Localization.Away (homogeneousFullJetMinorDet m x v)))).det =
      algebraMap R (Localization.Away (homogeneousFullJetMinorDet m x v))
        (homogeneousFullJetMinorDet m x v) := by
    change (RingHom.mapMatrix
      (algebraMap R (Localization.Away (homogeneousFullJetMinorDet m x v)))
      (homogeneousFullJetEvaluationMinor m x v)).det = _
    rw [← RingHom.map_det]
    rfl
  rw [hmap]
  exact IsLocalization.Away.algebraMap_isUnit (homogeneousFullJetMinorDet m x v)

noncomputable def homogeneousFullJetMinorSelectedPointLift
    {R : Type u} [CommRing R] {F : Type v} [Field F] {d : ℕ}
    (m : CubicFullJetCondition ↪ Monomials (Fin 4) d)
    (x : Fin 11 → Fin 4 → R) (v : Fin 3 → Fin 4 → Fin 2 → R)
    (f : R →+* F)
    (h : IsUnit (homogeneousFullJetEvaluationMinor m (fun i j => f (x i j))
      (fun i j t => f (v i j t))).det) :
    Localization.Away (homogeneousFullJetMinorDet m x v) →+* F :=
  IsLocalization.Away.lift (homogeneousFullJetMinorDet m x v) (by
    change IsUnit (f (homogeneousFullJetEvaluationMinor m x v).det)
    rw [RingHom.map_det, RingHom.mapMatrix_apply, homogeneousFullJetEvaluationMinor_map]
    exact h)

theorem homogeneousFullJetMinorSelectedPointLift_comp
    {R : Type u} [CommRing R] {F : Type v} [Field F] {d : ℕ}
    (m : CubicFullJetCondition ↪ Monomials (Fin 4) d)
    (x : Fin 11 → Fin 4 → R) (v : Fin 3 → Fin 4 → Fin 2 → R)
    (f : R →+* F)
    (h : IsUnit (homogeneousFullJetEvaluationMinor m (fun i j => f (x i j))
      (fun i j t => f (v i j t))).det) :
    (homogeneousFullJetMinorSelectedPointLift m x v f h).comp
      (algebraMap R (Localization.Away (homogeneousFullJetMinorDet m x v))) = f := by
  unfold homogeneousFullJetMinorSelectedPointLift
  exact IsLocalization.Away.lift_comp
    (x := homogeneousFullJetMinorDet m x v)
    (S := Localization.Away (homogeneousFullJetMinorDet m x v)) (g := f) _

end PfaffianDescent
