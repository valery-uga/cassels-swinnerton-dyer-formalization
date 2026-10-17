import PfaffianDescent.VoisinSelectedIntrinsicFieldIdeal
import PfaffianDescent.VoisinSelectedRelativeFieldFinite
import PfaffianDescent.VoisinIntrinsicIdealFiniteTransfer

/-! Finiteness of the intrinsic triple at a selected field point. -/

namespace PfaffianDescent

open AlgebraicGeometry MvPolynomial
open AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A finite selected relative triple family has a finite intrinsic triple
fiber at every field-valued point of its determinant open. -/
theorem selectedIntrinsicEightPointTriple_isFinite_at_fieldPoint
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
    IsFinite (toBase (intrinsicEightPointTripleHomogeneousIdeal
      (p.map g) (hp.map g) (fun k j => f (y k j)))) := by
  dsimp only
  let g := quadraticMinorSelectedPointLift m y f hm
  have hfin : IsFinite (relativeTripleIntersectionToBase
      (p.map g)
      ((quadraticSelectedOpenPolynomial m y 0).map g)
      ((quadraticSelectedOpenPolynomial m y 1).map g)
      (hp.map g)
      ((quadraticSelectedOpenPolynomial_isHomogeneous m y 0).map g)
      ((quadraticSelectedOpenPolynomial_isHomogeneous m y 1).map g)) :=
    selectedRelativeTriple_isFinite_at_fieldPoint m y p hp f hm
  letI := hfin
  exact isFinite_toBase_of_eq_relativeTripleIdeal
    (p.map g)
    ((quadraticSelectedOpenPolynomial m y 0).map g)
    ((quadraticSelectedOpenPolynomial m y 1).map g)
    (hp.map g)
    ((quadraticSelectedOpenPolynomial_isHomogeneous m y 0).map g)
    ((quadraticSelectedOpenPolynomial_isHomogeneous m y 1).map g)
    (intrinsicEightPointTripleHomogeneousIdeal
      (p.map g) (hp.map g) (fun k j => f (y k j)))
    (selectedIntrinsicEightPointTripleHomogeneousIdeal_eq_specializedFrame
      m y p hp f hm)

end PfaffianDescent
