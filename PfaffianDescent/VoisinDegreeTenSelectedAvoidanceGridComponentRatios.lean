import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceGridComponentVector
import PfaffianDescent.VoisinSelectedCanonicalChartRatios

/-! Exact component projective-point equality yields literal chart-zero
ratios for any native normalized ambient chart. -/
noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false in
theorem voisinDegreeTenSelectedAvoidance_nativeComponent_ratios_of_exactMarkedPoint
    {K Q A L : Type u} [Field K] [Field Q] [CommRing A]
    [Algebra Q A] [Field L] [Algebra K L] [Algebra Q L]
    (f : K →+* Q) (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (φ : A →ₐ[Q] L) (j : Spec (.of A) ⟶ Proj (homogeneousSubmodule (Fin 4) Q))
    (T : NormalizedAmbientChart Q A (Fin 4) (⊥ : HomogeneousIdeal
      (homogeneousSubmodule (Fin 4) Q)) j)
    (v : Fin 4 → L) (hv : v 0 = 1)
    (he : ∀ q ∈ (equationIdeal p hp).toIdeal,
      q.eval₂ (algebraMap K L) v = 0)
    (hOne : (Ideal.Quotient.lift (equationIdeal p hp).toIdeal
      (eval₂Hom (algebraMap K L) v) he) (coordinate (equationIdeal p hp) 0) = 1)
    (hpoint : (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ j) ≫
        ambientCoefficientMap f =
      linearNormalizedPointAt (equationIdeal p hp) v he
        (coordinate (equationIdeal p hp) 0) (coordinate_mem (equationIdeal p hp) 0)
        hOne ≫ hypersurfaceToAmbient p hp) :
    ∀ i, (φ (T.x 0))⁻¹ * φ (T.x i) = v i := by
  obtain ⟨hyOne, hyPoint⟩ :=
    voisinDegreeTenSelectedAvoidance_normalizedChart_componentVector φ j T
  have hr := selectedCanonical_normalizedCoordinateRatios_eq
    f p hp v (X 0) (isHomogeneous_X K 0) he hOne
    (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) Q))
    (fun i => φ (T.x i)) T.ell T.hell
    (by intro q hq; rw [Ideal.mem_bot.mp hq]; exact MvPolynomial.eval₂_zero _ _) hyOne
    (by rw [hyPoint]; exact hpoint) 0 (by rw [hv]; exact one_ne_zero)
  intro i
  simpa only [hv, inv_one, one_mul] using hr i

end PfaffianDescent
