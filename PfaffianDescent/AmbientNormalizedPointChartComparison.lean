import PfaffianDescent.AmbientTensorNormalizedChartSquare
import PfaffianDescent.ActualQuarticTensorIntrinsicQuadraticSystem

/-! The intrinsic-series point and direct ambient chart point are the SAME
actual projective morphism. This prevents an abstract coordinate-algebra
presentation from being silently substituted for the original embedding. -/

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics.HomogeneousProjective
open scoped TensorProduct
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem linearNormalizedPoint_toAmbient_eq_coordinateChartPoint
    {K A : Type u} [Field K] [CommRing A] [Algebra K A]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (x : Fin 4 → A) (j : Fin 4) (hx : x j = 1)
    (he : ∀ p ∈ I.toIdeal, p.eval₂ (algebraMap K A) x = 0) :
    linearNormalizedPoint I x (X j) (isHomogeneous_X K j)
      (by simpa only [eval₂_X] using hx) he ≫ quotientProjMap I =
      ambientNormalizedCoordinateChartPoint x j hx := by
  let hell := isHomogeneous_X K j
  let hOne : (X j : MvPolynomial (Fin 4) K).eval₂ (algebraMap K A) x = 1 :=
    by simpa only [eval₂_X] using hx
  obtain ⟨g, hcoordinates, hpoint⟩ :=
    exists_coordinateChartMap_eq_linearNormalizedPoint I x (X j) hell hOne he
      j (1 : Aˣ) hx.symm
  have hbase : g.comp (chartBaseMap I j) = algebraMap K A := by
    have h := congrArg (fun t => t ≫ toBase I) hpoint
    rw [Category.assoc, chartι_toBase, ← Spec.map_comp,
      linearNormalizedPoint_toBase] at h
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h)
  have hcoords : (fun r => g (chartCoordinate I j r)) = x := by
    funext r
    simpa using hcoordinates r
  calc
    linearNormalizedPoint I x (X j) hell hOne he ≫ quotientProjMap I =
        Spec.map (CommRingCat.ofHom g) ≫ chartι I j ≫ quotientProjMap I := by
      rw [← hpoint, Category.assoc]
    _ = ambientNormalizedCoordinateChartPoint
        (fun r => g (chartCoordinate I j r)) j
          (by rw [chartCoordinate_self, map_one]) :=
      (ambientNormalizedCoordinateChartPoint_eq_original_chart I j g hbase).symm
    _ = ambientNormalizedCoordinateChartPoint x j hx := by
      cases hcoords
      rfl

namespace QuarticNet
variable {k L K A : Type u} [Field k] [Field L] [Field K] [CommRing A]
  [Algebra k L] [Algebra k K] [Algebra k A]

/-- The actual tensor point used in the full intrinsic quadratic-system
comparison equals the direct ordinary ambient tensor chart point. -/
theorem actualQuarticTensorNormalizedToProjective_toAmbient
    (eA : A ≃ₐ[k] DualNumber L) (x : Fin 4 → A)
    (b : Basis (Fin 4) k L) (v : Fin 4 → L)
    (hx : ∀ r, eA (x r) = TrivSqZeroExt.inl (b r) + TrivSqZeroExt.inr (v r))
    (hb : b 0 = 1) (hv : v 0 = 0) :
    actualQuarticTensorNormalizedToProjective (K := K) eA x b v hx hb hv ≫
        quotientProjMap ⊥ =
      ambientNormalizedCoordinateChartPoint (fun r => (1 : K) ⊗ₜ[k] x r) 0
        (actualQuarticTensor_zero_coordinate_eq_one eA x b v hx hb hv) := by
  unfold actualQuarticTensorNormalizedToProjective
  exact linearNormalizedPoint_toAmbient_eq_coordinateChartPoint ⊥ _ 0
    (actualQuarticTensor_zero_coordinate_eq_one eA x b v hx hb hv) _

end QuarticNet
end PfaffianDescent
