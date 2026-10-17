import PfaffianDescent.AmbientTensorNormalizedChartSquare

/-! Naturality of the literal ordinary projective coordinate chart under
an actual coordinate-algebra homomorphism. -/

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem ambientNormalizedCoordinateChartPoint_algHom
    {K A B : Type u} [Field K] [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B]
    (phi : A →ₐ[K] B) (x : Fin 4 → A) (j : Fin 4) (hx : x j = 1) :
    ambientNormalizedCoordinateChartPoint (F := K) (fun r => phi (x r)) j
        (by rw [hx, map_one]) =
      Spec.map (CommRingCat.ofHom phi.toRingHom) ≫
        ambientNormalizedCoordinateChartPoint (F := K) x j hx := by
  have hbase : phi.toRingHom.comp (algebraMap K A) = algebraMap K B := by
    ext c
    exact phi.commutes c
  have hmap : ambientNormalizedCoordinateChartMap (F := K) (fun r => phi (x r)) j
      (by rw [hx, map_one]) =
      phi.toRingHom.comp (ambientNormalizedCoordinateChartMap (F := K) x j hx) := by
    apply RingHom.ext
    intro a
    obtain ⟨p, rfl⟩ := ambientChartEvaluation_surjective (R := K) j a
    rw [RingHom.comp_apply, ambientNormalizedCoordinateChartMap_eval,
      ambientNormalizedCoordinateChartMap_eval]
    change p.eval₂ (algebraMap K B) (fun r => phi (x r)) =
      phi (p.eval₂ (algebraMap K A) x)
    change p.eval₂ (algebraMap K B) (fun r => phi (x r)) =
      phi.toRingHom (p.eval₂ (algebraMap K A) x)
    rw [hom_eval₂, hbase]
    rfl
  unfold ambientNormalizedCoordinateChartPoint
  rw [hmap, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]

end PfaffianDescent
