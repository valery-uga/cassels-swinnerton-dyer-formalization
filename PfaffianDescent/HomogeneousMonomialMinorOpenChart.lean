import PfaffianDescent.HomogeneousMonomialEvaluationMinor

/-!
The actual principal open of a homogeneous monomial evaluation minor.
An invertible field-valued specialization factors through this localization,
and the marked evaluation matrix is invertible there.
-/

namespace PfaffianDescent

open AllCharacteristics.UniversalHomogeneous

universe u v

noncomputable def homogeneousMinorDet
    {R : Type u} [CommRing R] {n d : ℕ}
    (m : Fin n ↪ Monomials (Fin 4) d)
    (x : Fin n → Fin 4 → R) : R :=
  (homogeneousPointEvaluationMinor m x).det

theorem homogeneousMinorDet_ne_zero_of_specialized_unit
    {R : Type u} [CommRing R] {F : Type v} [Field F] {n d : ℕ}
    (m : Fin n ↪ Monomials (Fin 4) d)
    (x : Fin n → Fin 4 → R) (f : R →+* F)
    (h : IsUnit (homogeneousPointEvaluationMinor m
      (fun i j => f (x i j))).det) :
    homogeneousMinorDet m x ≠ 0 := by
  intro hz
  have heq : f (homogeneousMinorDet m x) =
      (homogeneousPointEvaluationMinor m (fun i j => f (x i j))).det := by
    rw [homogeneousMinorDet, RingHom.map_det,
      RingHom.mapMatrix_apply, homogeneousPointEvaluationMinor_map]
  rw [hz, map_zero] at heq
  exact h.ne_zero heq.symm

theorem homogeneousMinor_isUnit_on_principalOpen
    {R : Type u} [CommRing R] {n d : ℕ}
    (m : Fin n ↪ Monomials (Fin 4) d)
    (x : Fin n → Fin 4 → R) :
    IsUnit ((homogeneousPointEvaluationMinor m x).map
      (algebraMap R (Localization.Away (homogeneousMinorDet m x)))).det := by
  have hmap : ((homogeneousPointEvaluationMinor m x).map
      (algebraMap R (Localization.Away (homogeneousMinorDet m x)))).det =
      algebraMap R (Localization.Away (homogeneousMinorDet m x))
        (homogeneousMinorDet m x) := by
    change (RingHom.mapMatrix
      (algebraMap R (Localization.Away (homogeneousMinorDet m x)))
      (homogeneousPointEvaluationMinor m x)).det = _
    rw [← RingHom.map_det]
    rfl
  rw [hmap]
  exact IsLocalization.Away.algebraMap_isUnit (homogeneousMinorDet m x)

noncomputable def homogeneousMinorSelectedPointLift
    {R : Type u} [CommRing R] {F : Type v} [Field F] {n d : ℕ}
    (m : Fin n ↪ Monomials (Fin 4) d)
    (x : Fin n → Fin 4 → R) (f : R →+* F)
    (h : IsUnit (homogeneousPointEvaluationMinor m
      (fun i j => f (x i j))).det) :
    Localization.Away (homogeneousMinorDet m x) →+* F :=
  IsLocalization.Away.lift (homogeneousMinorDet m x) (by
    change IsUnit (f (homogeneousPointEvaluationMinor m x).det)
    rw [RingHom.map_det, RingHom.mapMatrix_apply,
      homogeneousPointEvaluationMinor_map]
    exact h)

theorem homogeneousMinorSelectedPointLift_comp
    {R : Type u} [CommRing R] {F : Type v} [Field F] {n d : ℕ}
    (m : Fin n ↪ Monomials (Fin 4) d)
    (x : Fin n → Fin 4 → R) (f : R →+* F)
    (h : IsUnit (homogeneousPointEvaluationMinor m
      (fun i j => f (x i j))).det) :
    (homogeneousMinorSelectedPointLift m x f h).comp
      (algebraMap R (Localization.Away (homogeneousMinorDet m x))) = f := by
  unfold homogeneousMinorSelectedPointLift
  exact IsLocalization.Away.lift_comp
    (x := homogeneousMinorDet m x)
    (S := Localization.Away (homogeneousMinorDet m x))
    (g := f) _

end PfaffianDescent
