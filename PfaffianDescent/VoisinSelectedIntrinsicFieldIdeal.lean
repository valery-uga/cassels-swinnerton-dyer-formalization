import PfaffianDescent.VoisinSelectedFrameRelabel
import PfaffianDescent.VoisinRelativeTripleFiniteBaseChange

/-! A finite selected chart family has finite intrinsic fibers at every field point of its minor open. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u v

attribute [local instance] MvPolynomial.gradedAlgebra

/-- At a field-valued point of the selected minor open, the specialized
two-equation frame generates the intrinsic homogeneous ideal. -/
theorem selectedIntrinsicEightPointTripleHomogeneousIdeal_eq_specializedFrame
    {R : Type u} [CommRing R]
    {F : Type v} [Field F]
    (m : Fin 8 ↪ Monomials (Fin 4) 2)
    (y : Fin 8 → Fin 4 → R)
    (p : MvPolynomial (Fin 4)
      (Localization.Away (quadraticMinorDet m y)))
    (hp : p.IsHomogeneous 3)
    (f : R →+* F)
    (hm : IsUnit (eightPointQuadraticEvaluationMinor m
      (fun k j => f (y k j))).det) :
    let g := quadraticMinorSelectedPointLift m y f hm
    intrinsicEightPointTripleHomogeneousIdeal
      (p.map g) (hp.map g) (fun k j => f (y k j)) =
      relativeTripleIntersectionHomogeneousIdeal
        (p.map g)
        ((quadraticSelectedOpenPolynomial m y 0).map g)
        ((quadraticSelectedOpenPolynomial m y 1).map g)
        (hp.map g)
        ((quadraticSelectedOpenPolynomial_isHomogeneous m y 0).map g)
        ((quadraticSelectedOpenPolynomial_isHomogeneous m y 1).map g) := by
  dsimp only
  let g := quadraticMinorSelectedPointLift m y f hm
  apply HomogeneousIdeal.ext
  rw [intrinsicEightPointTripleHomogeneousIdeal_toIdeal]
  have h := intrinsicEightPointTripleIdeal_eq_specializedSelectedFrame
    m y f hm (p.map g)
  have hrange : Set.range (fun i : Fin 2 =>
      (quadraticSelectedOpenPolynomial m y i).map g) =
      { (quadraticSelectedOpenPolynomial m y 0).map g,
        (quadraticSelectedOpenPolynomial m y 1).map g } := by
    ext t
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · intro ht
      rcases ht with ht | ht
      · exact ⟨0, ht.symm⟩
      · exact ⟨1, ht.symm⟩
  rw [hrange] at h
  exact h

end PfaffianDescent
