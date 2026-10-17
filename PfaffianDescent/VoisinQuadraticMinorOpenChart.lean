import PfaffianDescent.VoisinQuadraticKernelPolynomial
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# The principal open of a selected quadratic minor

The chosen minor is invertible in the localization at its determinant.
Every field-valued specialization where the determinant is invertible
factors through this same principal open.
-/

namespace PfaffianDescent

open AllCharacteristics.UniversalHomogeneous

universe u v

noncomputable def quadraticMinorDet
    {R : Type u} [CommRing R]
    (m : Fin 8 ↪ Monomials (Fin 4) 2)
    (y : Fin 8 → Fin 4 → R) : R :=
  (eightPointQuadraticEvaluationMinor m y).det

theorem quadraticMinorDet_ne_zero_of_specialized_unit
    {R : Type u} [CommRing R]
    {F : Type v} [Field F]
    (m : Fin 8 ↪ Monomials (Fin 4) 2)
    (y : Fin 8 → Fin 4 → R)
    (f : R →+* F)
    (h : IsUnit (eightPointQuadraticEvaluationMinor m
      (fun k j => f (y k j))).det) :
    quadraticMinorDet m y ≠ 0 := by
  intro hz
  have heq : f (quadraticMinorDet m y) =
      (eightPointQuadraticEvaluationMinor m
        (fun k j => f (y k j))).det := by
    rw [quadraticMinorDet, RingHom.map_det,
      RingHom.mapMatrix_apply, eightPointQuadraticEvaluationMinor_map]
  rw [hz, map_zero] at heq
  exact h.ne_zero heq.symm

theorem quadraticMinor_isUnit_on_principalOpen
    {R : Type u} [CommRing R]
    (m : Fin 8 ↪ Monomials (Fin 4) 2)
    (y : Fin 8 → Fin 4 → R) :
    IsUnit ((eightPointQuadraticEvaluationMinor m y).map
      (algebraMap R (Localization.Away (quadraticMinorDet m y)))).det := by
  have hmap : ((eightPointQuadraticEvaluationMinor m y).map
      (algebraMap R (Localization.Away (quadraticMinorDet m y)))).det =
      algebraMap R (Localization.Away (quadraticMinorDet m y))
        (quadraticMinorDet m y) := by
    change (RingHom.mapMatrix
      (algebraMap R (Localization.Away (quadraticMinorDet m y)))
      (eightPointQuadraticEvaluationMinor m y)).det = _
    rw [← RingHom.map_det]
    rfl
  rw [hmap]
  exact IsLocalization.Away.algebraMap_isUnit (quadraticMinorDet m y)

noncomputable def quadraticMinorSelectedPointLift
    {R : Type u} [CommRing R]
    {F : Type v} [Field F]
    (m : Fin 8 ↪ Monomials (Fin 4) 2)
    (y : Fin 8 → Fin 4 → R)
    (f : R →+* F)
    (h : IsUnit (eightPointQuadraticEvaluationMinor m
      (fun k j => f (y k j))).det) :
    Localization.Away (quadraticMinorDet m y) →+* F :=
  IsLocalization.Away.lift (quadraticMinorDet m y) (by
    change IsUnit (f (eightPointQuadraticEvaluationMinor m y).det)
    rw [RingHom.map_det, RingHom.mapMatrix_apply,
      eightPointQuadraticEvaluationMinor_map]
    exact h)

theorem quadraticMinorSelectedPointLift_comp
    {R : Type u} [CommRing R]
    {F : Type v} [Field F]
    (m : Fin 8 ↪ Monomials (Fin 4) 2)
    (y : Fin 8 → Fin 4 → R)
    (f : R →+* F)
    (h : IsUnit (eightPointQuadraticEvaluationMinor m
      (fun k j => f (y k j))).det) :
    (quadraticMinorSelectedPointLift m y f h).comp
      (algebraMap R (Localization.Away (quadraticMinorDet m y))) = f := by
  unfold quadraticMinorSelectedPointLift
  exact IsLocalization.Away.lift_comp
    (x := quadraticMinorDet m y)
    (S := Localization.Away (quadraticMinorDet m y))
    (g := f) _

/-- Injective evaluation at a field point remains injective on the
quadratic-minor principal open. -/
theorem quadraticMinorSelectedPointLift_injective
    {R : Type u} [CommRing R]
    {F : Type v} [Field F]
    (m : Fin 8 ↪ Monomials (Fin 4) 2)
    (y : Fin 8 → Fin 4 → R)
    (f : R →+* F)
    (h : IsUnit (eightPointQuadraticEvaluationMinor m
      (fun k j => f (y k j))).det)
    (hf : Function.Injective f) :
    Function.Injective (quadraticMinorSelectedPointLift m y f h) := by
  let g := quadraticMinorSelectedPointLift m y f h
  apply (IsLocalization.injective_iff_map_algebraMap_eq
    (M := Submonoid.powers (quadraticMinorDet m y)) g).2
  intro a b
  constructor
  · exact congrArg g
  · intro hab
    have hab' : f a = f b := by
      rw [← quadraticMinorSelectedPointLift_comp m y f h]
      exact hab
    exact congrArg (algebraMap R
      (Localization.Away (quadraticMinorDet m y))) (hf hab')

end PfaffianDescent
