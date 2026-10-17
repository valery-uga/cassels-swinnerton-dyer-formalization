import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceGridComponentRatios
import PfaffianDescent.VoisinChartSchemePointNormalized

/-! Native component ratios equal the actual values of the selected
chart-zero coordinate functions. -/
noncomputable section
open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false in
theorem voisinDegreeTenSelectedAvoidance_nativeComponent_ratios_at_actualChartPoint
    {K Q A L : Type u} [Field K] [Field Q] [CommRing A]
    [Algebra Q A] [Field L] [Algebra K L] [Algebra Q L]
    (f : K →+* Q) (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (φ : A →ₐ[Q] L) (j : Spec (.of A) ⟶ Proj (homogeneousSubmodule (Fin 4) Q))
    (T : NormalizedAmbientChart Q A (Fin 4) (⊥ : HomogeneousIdeal
      (homogeneousSubmodule (Fin 4) Q)) j)
    (t : Spec (.of L) ⟶ Spec (.of (Away (grading (equationIdeal p hp))
      (coordinate (equationIdeal p hp) 0))))
    (hbase : (Spec.preimage t).hom.comp
      (GradedChart.baseMap (grading (equationIdeal p hp))
        (z := coordinate (equationIdeal p hp) 0)) = algebraMap K L)
    (hpoint : (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ j) ≫
        ambientCoefficientMap f =
      (t ≫ Proj.awayι (grading (equationIdeal p hp))
        (coordinate (equationIdeal p hp) 0) (coordinate_mem (equationIdeal p hp) 0)
        (by decide : 0 < 1)) ≫ hypersurfaceToAmbient p hp) :
    ∀ i, (φ (T.x 0))⁻¹ * φ (T.x i) =
      (Spec.preimage t).hom (linearChartCoordinate (equationIdeal p hp)
        (coordinate (equationIdeal p hp) 0) (coordinate_mem (equationIdeal p hp) 0) i) := by
  obtain ⟨hnorm, he, hOne, hnormalized⟩ := chartSchemePoint_normalizedPointAt
    (equationIdeal p hp) (coordinate (equationIdeal p hp) 0)
    (coordinate_mem (equationIdeal p hp) 0) (X 0) (isHomogeneous_X K 0) rfl t hbase
  have hv : (Spec.preimage t).hom
      (linearChartCoordinate (equationIdeal p hp) (coordinate (equationIdeal p hp) 0)
        (coordinate_mem (equationIdeal p hp) 0) 0) = 1 := by
    simpa only [MvPolynomial.eval₂_X] using hnorm
  exact voisinDegreeTenSelectedAvoidance_nativeComponent_ratios_of_exactMarkedPoint
    f p hp φ j T _ hv he hOne (by rw [hnormalized]; exact hpoint)

end PfaffianDescent
