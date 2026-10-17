import PfaffianDescent.AmbientNormalizedPointChartComparison

/-! A linear-normalized projective point, reconstructed in any actual unit
coordinate chart. This compares embeddings with different normalizers. -/

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem linearNormalizedPoint_toAmbient_eq_unit_coordinateChartPoint
    {K A : Type u} [Field K] [CommRing A] [Algebra K A]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (x : Fin 4 → A) (ell : MvPolynomial (Fin 4) K)
    (hell : ell.IsHomogeneous 1) (hOne : ell.eval₂ (algebraMap K A) x = 1)
    (he : ∀ p ∈ I.toIdeal, p.eval₂ (algebraMap K A) x = 0)
    (j : Fin 4) (u : Aˣ) (hu : (u : A) = x j) :
    linearNormalizedPoint I x ell hell hOne he ≫ quotientProjMap I =
      ambientNormalizedCoordinateChartPoint (F := K)
        (fun r => (↑(u⁻¹) : A) * x r) j (by rw [← hu]; simp) := by
  obtain ⟨g, hcoordinates, hpoint⟩ :=
    exists_coordinateChartMap_eq_linearNormalizedPoint I x ell hell hOne he j u hu
  have hbase : g.comp (chartBaseMap I j) = algebraMap K A := by
    have h := congrArg (fun t => t ≫ toBase I) hpoint
    rw [Category.assoc, chartι_toBase, ← Spec.map_comp,
      linearNormalizedPoint_toBase] at h
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h)
  have hcoords : (fun r => g (chartCoordinate I j r)) =
      (fun r => (↑(u⁻¹) : A) * x r) := funext hcoordinates
  calc
    _ = Spec.map (CommRingCat.ofHom g) ≫ chartι I j ≫ quotientProjMap I := by
      rw [← hpoint, Category.assoc]
    _ = ambientNormalizedCoordinateChartPoint
        (fun r => g (chartCoordinate I j r)) j
          (by rw [chartCoordinate_self, map_one]) :=
      (ambientNormalizedCoordinateChartPoint_eq_original_chart I j g hbase).symm
    _ = _ := by
      have hcongr (a b : Fin 4 → A) (ha : a j = 1) (hb : b j = 1)
          (hab : a = b) : ambientNormalizedCoordinateChartPoint (F := K) a j ha =
            ambientNormalizedCoordinateChartPoint (F := K) b j hb := by
        subst b
        rfl
      exact hcongr _ _ _ _ hcoords

end PfaffianDescent
