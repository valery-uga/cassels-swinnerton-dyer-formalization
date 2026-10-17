import PfaffianDescent.VoisinGeometricComponentVectors

/-! Transport a geometric component vector through an ambient projective map. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- If a labeled component of the actual immersion maps to a specified
ambient point, then its evaluated normalized vector maps to that same point. -/
theorem GeometricDetectingEightCoordinates.componentVector_ambientPoint
    {Q A L : Type u} [Field Q] [CommRing A] [Algebra Q A]
    [Field L] [Algebra Q L]
    (φ : Fin 8 → A →ₐ[Q] L)
    (j : Spec (.of A) ⟶ Proj (homogeneousSubmodule (Fin 4) Q))
    (d : GeometricDetectingEightCoordinates φ j)
    (k : Fin 8) {X : Scheme.{u}}
    (g : Proj (homogeneousSubmodule (Fin 4) Q) ⟶ X)
    (marked : Spec (.of L) ⟶ X)
    (hmarked : (Spec.map (CommRingCat.ofHom (φ k).toRingHom) ≫ j) ≫ g =
      marked) :
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
      (linearNormalizedPointAt I y heL z hz hzOneL ≫
        quotientProjMap I) ≫ g = marked := by
  obtain ⟨hzOneL, hpoint⟩ :=
    d.componentVector_projectivePoint φ j k
  refine ⟨hzOneL, ?_⟩
  rw [hpoint]
  exact hmarked

end PfaffianDescent
