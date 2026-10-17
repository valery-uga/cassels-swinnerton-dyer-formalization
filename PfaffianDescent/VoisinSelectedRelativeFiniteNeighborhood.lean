import PfaffianDescent.VoisinRelativeTripleIntersectionFamily

/-!
# Finiteness near the selected split fibre

The determinant-open quadratic frame defines two regular equations.  If its
selected specialization is the normalized split eight-point witness, the
corresponding relative triple intersection is finite near the generic point.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A finite specialization cut out by any independent pair spanning the
full quadratic vanishing kernel makes the selected relative frame finite on
an open neighborhood of its generic point. -/
theorem quadraticSelectedOpenFrame_exists_genericFiniteNeighborhood_of_pair
    {R : Type u} [CommRing R] [IsDomain R]
    {F : Type u} [Field F]
    (m : Fin 8 ↪ Monomials (Fin 4) 2)
    (x : Fin 8 → Fin 4 → R)
    (f : R →+* F)
    (hm : IsUnit (eightPointQuadraticEvaluationMinor m
      (fun k j => f (x k j))).det)
    [IsDomain (Localization.Away (quadraticMinorDet m x))]
    (y : Fin 8 → Fin 4 → F) (c : Fin 4 → F)
    (hc : ∀ k, (homogeneousLinearForm c).eval (y k) ≠ 0)
    (hfx : ∀ k j, f (x k j) = normalizedVectorInLinearChart c (y k) j)
    (hsurj : Function.Surjective
      (homogeneousSectionRestriction (K := F)
        (fun j k => y k j : Fin 4 → Fin 8 → F) 2))
    (q r : MvPolynomial (Fin 4) F)
    (hq : q.IsHomogeneous 2) (hr : r.IsHomogeneous 2)
    (hlin : LinearIndependent F
      ![(⟨q, hq⟩ : homogeneousSubmodule (Fin 4) F 2), ⟨r, hr⟩])
    (hquad : ∀ k, q.eval (y k) = 0 ∧ r.eval (y k) = 0)
    (p : MvPolynomial (Fin 4)
      (Localization.Away (quadraticMinorDet m x)))
    (hp : p.IsHomogeneous 3)
    [IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal
      (p.map (quadraticMinorSelectedPointLift m x f hm)) q r
      (hp.map (quadraticMinorSelectedPointLift m x f hm)) hq hr))] :
    ∃ V : (Spec (.of (Localization.Away (quadraticMinorDet m x)))).Opens,
      genericPoint (Spec (.of (Localization.Away (quadraticMinorDet m x)))) ∈ V ∧
      IsFinite ((relativeTripleIntersectionToBase p
        (quadraticSelectedOpenPolynomial m x 0)
        (quadraticSelectedOpenPolynomial m x 1)
        hp
        (quadraticSelectedOpenPolynomial_isHomogeneous m x 0)
        (quadraticSelectedOpenPolynomial_isHomogeneous m x 1)) ∣_ V) := by
  let g := quadraticMinorSelectedPointLift m x f hm
  let q₀ := quadraticSelectedOpenPolynomial m x 0
  let q₁ := quadraticSelectedOpenPolynomial m x 1
  have heq : tripleCompleteIntersectionHomogeneousIdeal
      (p.map g) (q₀.map g) (q₁.map g)
      (hp.map g)
      ((quadraticSelectedOpenPolynomial_isHomogeneous m x 0).map g)
      ((quadraticSelectedOpenPolynomial_isHomogeneous m x 1).map g) =
    tripleCompleteIntersectionHomogeneousIdeal
      (p.map g) q r (hp.map g) hq hr := by
    simpa only [g, q₀, q₁,
      quadraticSelectedOpenPolynomial_map_selectedPoint,
      quadraticSelectedOpenBasisSpecializedHomogeneous] using
      (quadraticSelectedOpenBasisSpecialized_ideal_eq_quadratic_pair
        m x f hm y c hc hfx q r hq hr hlin hsurj hquad
          (p.map g) (hp.map g))
  haveI : IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal
      (p.map g) (q₀.map g) (q₁.map g)
      (hp.map g)
      ((quadraticSelectedOpenPolynomial_isHomogeneous m x 0).map g)
      ((quadraticSelectedOpenPolynomial_isHomogeneous m x 1).map g))) := by
    rw [heq]
    infer_instance
  exact relativeTripleIntersection_exists_genericFiniteNeighborhood_of_finiteTripleSpecialization
    g p q₀ q₁ hp
    (quadraticSelectedOpenPolynomial_isHomogeneous m x 0)
    (quadraticSelectedOpenPolynomial_isHomogeneous m x 1)

theorem quadraticSelectedOpenFrame_exists_genericFiniteNeighborhood
    {R : Type u} [CommRing R] [IsDomain R]
    {F : Type u} [Field F]
    (m : Fin 8 ↪ Monomials (Fin 4) 2)
    (x : Fin 8 → Fin 4 → R)
    (f : R →+* F)
    (hm : IsUnit (eightPointQuadraticEvaluationMinor m
      (fun k j => f (x k j))).det)
    [IsDomain (Localization.Away (quadraticMinorDet m x))]
    (y : Fin 8 → Fin 4 → F) (c : Fin 4 → F)
    (hc : ∀ k, (homogeneousLinearForm c).eval (y k) ≠ 0)
    (hfx : ∀ k j, f (x k j) = normalizedVectorInLinearChart c (y k) j)
    (hsurj : Function.Surjective
      (homogeneousSectionRestriction (K := F)
        (fun j k => y k j : Fin 4 → Fin 8 → F) 2))
    (hquad : ∀ k,
      (X 1 * X 2 : MvPolynomial (Fin 4) F).eval (y k) = 0 ∧
      (X 3 * (X 1 + X 2 + X 3) : MvPolynomial (Fin 4) F).eval (y k) = 0)
    (p : MvPolynomial (Fin 4)
      (Localization.Away (quadraticMinorDet m x)))
    (hp : p.IsHomogeneous 3)
    [IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal
      (p.map (quadraticMinorSelectedPointLift m x f hm))
      (splitQuadraticPencil F 0).1 (splitQuadraticPencil F 1).1
      (hp.map (quadraticMinorSelectedPointLift m x f hm))
      (splitQuadraticPencil F 0).2 (splitQuadraticPencil F 1).2))] :
    ∃ V : (Spec (.of (Localization.Away (quadraticMinorDet m x)))).Opens,
      genericPoint (Spec (.of (Localization.Away (quadraticMinorDet m x)))) ∈ V ∧
      IsFinite ((relativeTripleIntersectionToBase p
        (quadraticSelectedOpenPolynomial m x 0)
        (quadraticSelectedOpenPolynomial m x 1)
        hp
        (quadraticSelectedOpenPolynomial_isHomogeneous m x 0)
        (quadraticSelectedOpenPolynomial_isHomogeneous m x 1)) ∣_ V) := by
  let g := quadraticMinorSelectedPointLift m x f hm
  let q₀ := quadraticSelectedOpenPolynomial m x 0
  let q₁ := quadraticSelectedOpenPolynomial m x 1
  have heq : tripleCompleteIntersectionHomogeneousIdeal
      (p.map g) (q₀.map g) (q₁.map g)
      (hp.map g)
      ((quadraticSelectedOpenPolynomial_isHomogeneous m x 0).map g)
      ((quadraticSelectedOpenPolynomial_isHomogeneous m x 1).map g) =
    tripleCompleteIntersectionHomogeneousIdeal
      (p.map g)
      (splitQuadraticPencil F 0).1 (splitQuadraticPencil F 1).1
      (hp.map g)
      (splitQuadraticPencil F 0).2 (splitQuadraticPencil F 1).2 := by
    simpa only [g, q₀, q₁,
      quadraticSelectedOpenPolynomial_map_selectedPoint,
      quadraticSelectedOpenBasisSpecializedHomogeneous] using
      (quadraticSelectedOpenBasisSpecialized_ideal_eq_split
        m x f hm y c hc hfx hsurj hquad (p.map g) (hp.map g))
  haveI : IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal
      (p.map g) (q₀.map g) (q₁.map g)
      (hp.map g)
      ((quadraticSelectedOpenPolynomial_isHomogeneous m x 0).map g)
      ((quadraticSelectedOpenPolynomial_isHomogeneous m x 1).map g))) := by
    rw [heq]
    infer_instance
  exact relativeTripleIntersection_exists_genericFiniteNeighborhood_of_finiteTripleSpecialization
    g p q₀ q₁ hp
    (quadraticSelectedOpenPolynomial_isHomogeneous m x 0)
    (quadraticSelectedOpenPolynomial_isHomogeneous m x 1)

end PfaffianDescent
