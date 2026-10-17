import PfaffianDescent.VoisinQuadraticKernelSpecialization
import PfaffianDescent.VoisinRelativeTripleFiniteBaseChange

/-! Finite selected triple families remain finite at a field point of the minor chart. -/

namespace PfaffianDescent

open AlgebraicGeometry MvPolynomial
open AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

/-- Specializing a finite selected cubic--two-quadrics family to a field
point of its determinant open preserves finiteness. -/
theorem selectedRelativeTriple_isFinite_at_fieldPoint
    {R : Type u} [CommRing R]
    {F : Type u} [Field F]
    (m : Fin 8 ↪ Monomials (Fin 4) 2)
    (y : Fin 8 → Fin 4 → R)
    (p : MvPolynomial (Fin 4)
      (Localization.Away (quadraticMinorDet m y)))
    (hp : p.IsHomogeneous 3)
    [IsFinite (relativeTripleIntersectionToBase p
      (quadraticSelectedOpenPolynomial m y 0)
      (quadraticSelectedOpenPolynomial m y 1) hp
      (quadraticSelectedOpenPolynomial_isHomogeneous m y 0)
      (quadraticSelectedOpenPolynomial_isHomogeneous m y 1))]
    (f : R →+* F)
    (hm : IsUnit (eightPointQuadraticEvaluationMinor m
      (fun k j => f (y k j))).det) :
    let g := quadraticMinorSelectedPointLift m y f hm
    IsFinite (relativeTripleIntersectionToBase
      (p.map g)
      ((quadraticSelectedOpenPolynomial m y 0).map g)
      ((quadraticSelectedOpenPolynomial m y 1).map g)
      (hp.map g)
      ((quadraticSelectedOpenPolynomial_isHomogeneous m y 0).map g)
      ((quadraticSelectedOpenPolynomial_isHomogeneous m y 1).map g)) := by
  dsimp only
  exact relativeTripleIntersection_isFinite_map
    (R := Localization.Away (quadraticMinorDet m y)) (S := F)
    (quadraticMinorSelectedPointLift m y f hm) p
    (quadraticSelectedOpenPolynomial m y 0)
    (quadraticSelectedOpenPolynomial m y 1) hp
    (quadraticSelectedOpenPolynomial_isHomogeneous m y 0)
    (quadraticSelectedOpenPolynomial_isHomogeneous m y 1)

end PfaffianDescent
