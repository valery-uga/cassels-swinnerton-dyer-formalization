import PfaffianDescent.VoisinNormalizedPointAtCompatibility
import AllCharacteristics.HomogeneousProjectiveAmbient

/-! Ordinary ambient coordinate charts for normalized hypersurface points. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A normalized hypersurface vector with nonzero `j`-th coordinate gives
an ordinary ambient `j`-chart map. Its normalized chart coordinates are
exactly the ratios of the original vector coordinates. -/
theorem exists_ambientCoordinateChart_of_linearNormalizedPoint
    {K F : Type u} [Field K] [Field F] [Algebra K F]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (x : Fin 4 → F) (ell : MvPolynomial (Fin 4) K)
    (hell : ell.IsHomogeneous 1)
    (hxell : ell.eval₂ (algebraMap K F) x = 1)
    (he : ∀ q ∈ (equationIdeal p hp).toIdeal,
      q.eval₂ (algebraMap K F) x = 0)
    (j : Fin 4) (hxj : x j ≠ 0) :
    ∃ g : Away (homogeneousSubmodule (Fin 4) K) (X j) →+* F,
      (Spec.map (CommRingCat.ofHom g) ≫
        Proj.awayι (homogeneousSubmodule (Fin 4) K) (X j)
          (isHomogeneous_X K j) (by decide : 0 < 1) =
        linearNormalizedPoint (equationIdeal p hp) x ell hell hxell he ≫
          hypersurfaceToAmbient p hp) ∧
      ∀ i : Fin 4,
        g (AllCharacteristics.GradedChart.normalized
          (homogeneousSubmodule (Fin 4) K) (isHomogeneous_X K j)
          (X i) (isHomogeneous_X K i)) = (x j)⁻¹ * x i := by
  let u : Fˣ := Units.mk0 (x j) hxj
  obtain ⟨gH, hcoord, hpoint⟩ :=
    exists_coordinateChartMap_eq_linearNormalizedPoint
      (equationIdeal p hp) x ell hell hxell he j u rfl
  let g := gH.comp (hypersurfaceAmbientChartMap p hp j)
  refine ⟨g, ?_, ?_⟩
  · calc
      Spec.map (CommRingCat.ofHom g) ≫
          Proj.awayι (homogeneousSubmodule (Fin 4) K) (X j)
            (isHomogeneous_X K j) (by decide : 0 < 1) =
        (Spec.map (CommRingCat.ofHom gH) ≫
          Spec.map (CommRingCat.ofHom (hypersurfaceAmbientChartMap p hp j))) ≫
          Proj.awayι (homogeneousSubmodule (Fin 4) K) (X j)
            (isHomogeneous_X K j) (by decide : 0 < 1) := by
              rw [← Spec.map_comp]
              rfl
      _ = (Spec.map (CommRingCat.ofHom gH) ≫
          chartι (equationIdeal p hp) j) ≫ hypersurfaceToAmbient p hp := by
            calc
              _ = Spec.map (CommRingCat.ofHom gH) ≫
                  (Spec.map (CommRingCat.ofHom
                    (hypersurfaceAmbientChartMap p hp j)) ≫
                    Proj.awayι (homogeneousSubmodule (Fin 4) K) (X j)
                      (isHomogeneous_X K j) (by decide : 0 < 1)) := by
                        rw [Category.assoc]
              _ = Spec.map (CommRingCat.ofHom gH) ≫
                  (chartι (equationIdeal p hp) j ≫
                    hypersurfaceToAmbient p hp) := by
                      rw [chartι_comp_hypersurfaceToAmbient]
              _ = _ := (Category.assoc _ _ _).symm
      _ = _ := by rw [hpoint]
  · intro i
    change gH (hypersurfaceAmbientChartMap p hp j
      (AllCharacteristics.GradedChart.normalized
        (homogeneousSubmodule (Fin 4) K) (isHomogeneous_X K j)
        (X i) (isHomogeneous_X K i))) = _
    rw [hypersurfaceAmbientChartMap_coordinate, hcoord]
    simp [u]

/-- The same ambient chart presentation for the explicit chart-element
normalized-point constructor used by the selected generic configuration. -/
theorem exists_ambientCoordinateChart_of_linearNormalizedPointAt
    {K F : Type u} [Field K] [Field F] [Algebra K F]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (x : Fin 4 → F) (ell : MvPolynomial (Fin 4) K)
    (hell : ell.IsHomogeneous 1)
    (he : ∀ q ∈ (equationIdeal p hp).toIdeal,
      q.eval₂ (algebraMap K F) x = 0)
    (hzOne : (Ideal.Quotient.lift (equationIdeal p hp).toIdeal
      (eval₂Hom (algebraMap K F) x) he)
        (Ideal.Quotient.mk (equationIdeal p hp).toIdeal ell) = 1)
    (j : Fin 4) (hxj : x j ≠ 0) :
    ∃ g : Away (homogeneousSubmodule (Fin 4) K) (X j) →+* F,
      (Spec.map (CommRingCat.ofHom g) ≫
        Proj.awayι (homogeneousSubmodule (Fin 4) K) (X j)
          (isHomogeneous_X K j) (by decide : 0 < 1) =
        linearNormalizedPointAt (equationIdeal p hp) x he
          (Ideal.Quotient.mk (equationIdeal p hp).toIdeal ell)
          (polynomial_class_mem_grading (equationIdeal p hp) ell hell)
          hzOne ≫ hypersurfaceToAmbient p hp) ∧
      ∀ i : Fin 4,
        g (AllCharacteristics.GradedChart.normalized
          (homogeneousSubmodule (Fin 4) K) (isHomogeneous_X K j)
          (X i) (isHomogeneous_X K i)) = (x j)⁻¹ * x i := by
  obtain ⟨g, hg, hcoord⟩ :=
    exists_ambientCoordinateChart_of_linearNormalizedPoint
      p hp x ell hell hzOne he j hxj
  refine ⟨g, ?_, hcoord⟩
  rw [hg, linearNormalizedPointAt_mk_eq_linearNormalizedPoint]

end PfaffianDescent
