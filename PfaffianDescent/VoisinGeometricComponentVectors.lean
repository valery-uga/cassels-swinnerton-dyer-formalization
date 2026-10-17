import PfaffianDescent.VoisinGenericEightGeometricCoordinates

/-! Component vectors of a geometric finite-algebra presentation. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Evaluating the geometric coordinate algebra at one labeled component
gives a normalized vector representing the component of the actual
projective immersion. -/
theorem GeometricDetectingEightCoordinates.componentVector_projectivePoint
    {Q A L : Type u} [Field Q] [CommRing A] [Algebra Q A]
    [Field L] [Algebra Q L]
    (φ : Fin 8 → A →ₐ[Q] L)
    (j : Spec (.of A) ⟶ Proj (homogeneousSubmodule (Fin 4) Q))
    (d : GeometricDetectingEightCoordinates φ j)
    (k : Fin 8) :
    let I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) Q) := ⊥
    let z : CoordinateRing I := Ideal.Quotient.mk I.toIdeal d.ell
    let hz : z ∈ grading I 1 :=
      polynomial_class_mem_grading I d.ell d.ellHomogeneous
    let y : Fin 4 → L := fun r => φ k (d.x r)
    let heL : ∀ q ∈ I.toIdeal,
      (eval₂Hom (algebraMap Q L) y) q = 0 := by
        intro q hq
        exact (Ideal.mem_bot.mp hq).symm ▸ map_zero _
    ∃ (hzOneL : (Ideal.Quotient.lift I.toIdeal
      (eval₂Hom (algebraMap Q L) y) heL) z = 1),
      linearNormalizedPointAt I y heL z hz hzOneL ≫
        quotientProjMap I =
          Spec.map (CommRingCat.ofHom (φ k).toRingHom) ≫ j := by
  dsimp only
  let I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) Q) := ⊥
  let z : CoordinateRing I := Ideal.Quotient.mk I.toIdeal d.ell
  let hz : z ∈ grading I 1 :=
    polynomial_class_mem_grading I d.ell d.ellHomogeneous
  let y : Fin 4 → L := fun r => φ k (d.x r)
  let heL : ∀ q ∈ I.toIdeal,
      (eval₂Hom (algebraMap Q L) y) q = 0 := by
    intro q hq
    exact (Ideal.mem_bot.mp hq).symm ▸ map_zero _
  have hellEval : d.ell.eval₂ (algebraMap Q A) d.x = 1 := d.ellOne
  have hzOneL : (Ideal.Quotient.lift I.toIdeal
      (eval₂Hom (algebraMap Q L) y) heL) z = 1 := by
    change d.ell.eval₂ (algebraMap Q L) (fun r => φ k (d.x r)) = 1
    exact eval₂_algebraHom_eq_one_of_eq_one (φ k) d.x d.ell hellEval
  refine ⟨hzOneL, ?_⟩
  have hnat := linearNormalizedPointAt_naturality I d.x d.he
    (φ k) y (fun _ => rfl) heL z hz d.ellOne hzOneL
  rw [hnat, Category.assoc, d.point_eq]

end PfaffianDescent
