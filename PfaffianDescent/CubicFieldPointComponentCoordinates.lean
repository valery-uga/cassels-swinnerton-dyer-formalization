import PfaffianDescent.CubicFieldPointComponentChart
import PfaffianDescent.VoisinNormalizedAmbientCoordinateChart
import PfaffianDescent.VoisinNormalizedPointChartNonzero

/-! Actual field-point chart coordinates equal the selected component's
projective coordinate ratios; coordinate nonvanishing is proved internally. -/

noncomputable section
namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open AllCharacteristics.HomogeneousProjective

universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem cubicFieldPoint_component_coordinates_eq_selected_ratios
    {K F L E : Type u} [Field K] [Field F] [Field L] [Field E] [Algebra K E]
    (f : K →+* F)
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : MvPolynomial (Fin 4) F) (hP : P.IsHomogeneous 3)
    (i : Spec (.of L) ⟶ hypersurface P hP) (j : Fin 4)
    (g : ChartRing (equationIdeal P hP) j →+* L)
    (hg : Spec.map (CommRingCat.ofHom g) ≫ chartι (equationIdeal P hP) j = i)
    (α : L →+* E) (x : Fin 4 → E)
    (ell : MvPolynomial (Fin 4) K) (hell : ell.IsHomogeneous 1)
    (he : ∀ q ∈ (equationIdeal p hp).toIdeal, q.eval₂ (algebraMap K E) x = 0)
    (hzOne : (Ideal.Quotient.lift (equationIdeal p hp).toIdeal
      (eval₂Hom (algebraMap K E) x) he)
        (Ideal.Quotient.mk (equationIdeal p hp).toIdeal ell) = 1)
    (hpoint : Spec.map (CommRingCat.ofHom α) ≫ i ≫
        hypersurfaceToAmbient P hP ≫ ambientCoefficientMap f =
      linearNormalizedPointAt (equationIdeal p hp) x he
        (Ideal.Quotient.mk (equationIdeal p hp).toIdeal ell)
        (polynomial_class_mem_grading (equationIdeal p hp) ell hell) hzOne ≫
        hypersurfaceToAmbient p hp) :
    x j ≠ 0 ∧ ∀ r : Fin 4,
      α (g (chartCoordinate (equationIdeal P hP) j r)) = (x j)⁻¹ * x r := by
  let gE : ChartRing (equationIdeal P hP) j →+* E := α.comp g
  let aChart := (hypersurfaceAmbientChartMap P hP j).comp (ambientCoefficientChartMap f j)
  let raw : Away (homogeneousSubmodule (Fin 4) K) (X j) →+* E := gE.comp aChart
  let z := Ideal.Quotient.mk (equationIdeal p hp).toIdeal ell
  let hz := polynomial_class_mem_grading (equationIdeal p hp) ell hell
  let norm := linearNormalizedPointAt (equationIdeal p hp) x he z hz hzOne
  have hE : Spec.map (CommRingCat.ofHom gE) ≫ chartι (equationIdeal P hP) j =
      Spec.map (CommRingCat.ofHom α) ≫ i := by
    change Spec.map (CommRingCat.ofHom g ≫ CommRingCat.ofHom α) ≫ _ = _
    rw [Spec.map_comp, Category.assoc, hg]
  have hnormalized : Spec.map (CommRingCat.ofHom gE) ≫
      (chartι (equationIdeal P hP) j ≫ hypersurfaceToAmbient P hP ≫
        ambientCoefficientMap f) = norm ≫ hypersurfaceToAmbient p hp := by
    rw [← Category.assoc, hE, Category.assoc]
    exact hpoint
  have hraw : Spec.map (CommRingCat.ofHom gE) ≫
      (chartι (equationIdeal P hP) j ≫ hypersurfaceToAmbient P hP ≫
        ambientCoefficientMap f) =
      Spec.map (CommRingCat.ofHom raw) ≫
        Proj.awayι (homogeneousSubmodule (Fin 4) K) (X j)
          (isHomogeneous_X K j) (by decide : 0 < 1) := by
    rw [chartι_comp_hypersurfaceToAmbient_comp_ambientCoefficientMap,
      ← Category.assoc, ← Spec.map_comp]
    rfl
  have hnraw := hnormalized.symm.trans hraw
  have hopen : (norm ≫ hypersurfaceToAmbient p hp) (IsLocalRing.closedPoint E) ∈
      Proj.basicOpen (homogeneousSubmodule (Fin 4) K) (X j) := by
    rw [hnraw]
    have hmem : (Spec.map (CommRingCat.ofHom raw) ≫
        Proj.awayι (homogeneousSubmodule (Fin 4) K) (X j)
          (isHomogeneous_X K j) (by decide : 0 < 1)) (IsLocalRing.closedPoint E) ∈
        (Proj.awayι (homogeneousSubmodule (Fin 4) K) (X j)
          (isHomogeneous_X K j) (by decide : 0 < 1)).opensRange :=
      ⟨(Spec.map (CommRingCat.ofHom raw)) (IsLocalRing.closedPoint E), rfl⟩
    exact (Proj.opensRange_awayι (homogeneousSubmodule (Fin 4) K) (X j)
      (isHomogeneous_X K j) (by decide : 0 < 1)) ▸ hmem
  have hxj := normalizedPointAt_coordinate_ne_zero_of_ambient_basicOpen
    (equationIdeal p hp) x ell hell he hzOne j hopen
  obtain ⟨gK, hgK, hcoordK⟩ := exists_ambientCoordinateChart_of_linearNormalizedPointAt
    p hp x ell hell he hzOne j hxj
  refine ⟨hxj, ?_⟩
  intro r
  have hcomparison : Spec.map (CommRingCat.ofHom gE) ≫
      (chartι (equationIdeal P hP) j ≫ hypersurfaceToAmbient P hP ≫
        ambientCoefficientMap f) =
      Spec.map (CommRingCat.ofHom gK) ≫
        Proj.awayι (homogeneousSubmodule (Fin 4) K) (X j)
          (isHomogeneous_X K j) (by decide : 0 < 1) :=
    hnormalized.trans hgK.symm
  exact (hypersurfaceChartCoordinate_eq_of_ambient_eq f P hP j r gE gK hcomparison).trans
    (hcoordK r)

end PfaffianDescent
