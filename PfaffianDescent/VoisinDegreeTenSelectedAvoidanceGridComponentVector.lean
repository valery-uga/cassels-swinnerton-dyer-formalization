import PfaffianDescent.VoisinGenericCubicSixteenEvaluation
import PfaffianDescent.NormalizedChartAlgebraTransport
import PfaffianDescent.VoisinGeometricComponentVectors

/-! Evaluating any native normalized chart at a component reconstructs
that component's exact projective point. -/
noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false in
theorem voisinDegreeTenSelectedAvoidance_normalizedChart_componentVector
    {Q A L : Type u} [Field Q] [CommRing A] [Algebra Q A]
    [Field L] [Algebra Q L]
    (φ : A →ₐ[Q] L)
    (j : Spec (.of A) ⟶ Proj (homogeneousSubmodule (Fin 4) Q))
    (T : NormalizedAmbientChart Q A (Fin 4)
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) Q)) j) :
    let I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) Q) := ⊥
    let z : CoordinateRing I := Ideal.Quotient.mk I.toIdeal T.ell
    let hz : z ∈ grading I 1 := polynomial_class_mem_grading I T.ell T.hell
    let y : Fin 4 → L := fun r => φ (T.x r)
    let heL : ∀ q ∈ I.toIdeal,
      (eval₂Hom (algebraMap Q L) y) q = 0 := by
        intro q hq
        exact (Ideal.mem_bot.mp hq).symm ▸ map_zero _
    ∃ (hzOneL : (Ideal.Quotient.lift I.toIdeal
      (eval₂Hom (algebraMap Q L) y) heL) z = 1),
      linearNormalizedPointAt I y heL z hz hzOneL ≫ quotientProjMap I =
        Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ j := by
  dsimp only
  let I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) Q) := ⊥
  let z : CoordinateRing I := Ideal.Quotient.mk I.toIdeal T.ell
  let hz : z ∈ grading I 1 := polynomial_class_mem_grading I T.ell T.hell
  let y : Fin 4 → L := fun r => φ (T.x r)
  let heL : ∀ q ∈ I.toIdeal,
      (eval₂Hom (algebraMap Q L) y) q = 0 := by
    intro q hq
    exact (Ideal.mem_bot.mp hq).symm ▸ map_zero _
  have hellEval : T.ell.eval₂ (algebraMap Q A) T.x = 1 := T.hellOne
  have hzOneL : (Ideal.Quotient.lift I.toIdeal
      (eval₂Hom (algebraMap Q L) y) heL) z = 1 := by
    change T.ell.eval₂ (algebraMap Q L) y = 1
    exact eval₂_algebraHom_eq_one_of_eq_one φ T.x T.ell hellEval
  refine ⟨hzOneL, ?_⟩
  have hnat := linearNormalizedPointAt_naturality I T.x T.he
    φ y (fun _ => rfl) heL z hz T.hellOne hzOneL
  rw [hnat, Category.assoc, T.hpoint]

end PfaffianDescent
