import PfaffianDescent.CubicFieldPointComponentChart
import PfaffianDescent.VoisinNormalizedAmbientCoordinateChart

/-! Construct an actual ground cubic chart from a selected component
represented by its actual normalized projective coordinates. -/

noncomputable section
namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open AllCharacteristics.HomogeneousProjective

universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem cubicFieldPoint_exists_chart_from_selected_component
    {K F L E : Type u} [Field K] [Field F] [Field L] [Field E]
    [Algebra K E] [Algebra F L] [Algebra F E]
    (f : K →+* F)
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : MvPolynomial (Fin 4) F) (hP : P.IsHomogeneous 3)
    (i : Spec (.of L) ⟶ hypersurface P hP)
    (hi : i ≫ hypersurfaceToBase P hP = Spec.map (CommRingCat.ofHom (algebraMap F L)))
    (α : L →ₐ[F] E) (x : Fin 4 → E)
    (ell : MvPolynomial (Fin 4) K) (hell : ell.IsHomogeneous 1)
    (he : ∀ q ∈ (equationIdeal p hp).toIdeal, q.eval₂ (algebraMap K E) x = 0)
    (hzOne : (Ideal.Quotient.lift (equationIdeal p hp).toIdeal
      (eval₂Hom (algebraMap K E) x) he)
        (Ideal.Quotient.mk (equationIdeal p hp).toIdeal ell) = 1)
    (hpoint : Spec.map (CommRingCat.ofHom α.toRingHom) ≫ i ≫
        hypersurfaceToAmbient P hP ≫ ambientCoefficientMap f =
      linearNormalizedPointAt (equationIdeal p hp) x he
        (Ideal.Quotient.mk (equationIdeal p hp).toIdeal ell)
        (polynomial_class_mem_grading (equationIdeal p hp) ell hell) hzOne ≫
        hypersurfaceToAmbient p hp) (j : Fin 4) (hxj : x j ≠ 0) :
    ∃ g : ChartRing (equationIdeal P hP) j →+* L,
      g.comp (chartBaseMap (equationIdeal P hP) j) = algebraMap F L ∧
      Spec.map (CommRingCat.ofHom g) ≫ chartι (equationIdeal P hP) j = i ∧
      ∀ r : Fin 4, α (g (chartCoordinate (equationIdeal P hP) j r)) = (x j)⁻¹ * x r := by
  have hcoeff : CommRingCat.ofHom (algebraMap F L) ≫ CommRingCat.ofHom α.toRingHom =
      CommRingCat.ofHom (algebraMap F E) := by
    ext r
    exact α.commutes r
  have hbase : (Spec.map (CommRingCat.ofHom α.toRingHom) ≫ i) ≫
      hypersurfaceToBase P hP = Spec.map (CommRingCat.ofHom (algebraMap F E)) := by
    rw [Category.assoc, hi, ← Spec.map_comp, hcoeff]
  obtain ⟨gK, hgK, hcoordK⟩ := exists_ambientCoordinateChart_of_linearNormalizedPointAt
    p hp x ell hell he hzOne j hxj
  have hambient : (Spec.map (CommRingCat.ofHom α.toRingHom) ≫ i) ≫
      hypersurfaceToAmbient P hP ≫ ambientCoefficientMap f =
      Spec.map (CommRingCat.ofHom gK) ≫
        Proj.awayι (homogeneousSubmodule (Fin 4) K) (X j)
          (isHomogeneous_X K j) (by decide : 0 < 1) := by
    simpa only [Category.assoc] using hpoint.trans hgK.symm
  obtain ⟨gE, _, hgE, hcoordE, _⟩ :=
    exists_chart_hom_and_coordinates_eq_of_ambient_eq f P hP (algebraMap F E)
      (Spec.map (CommRingCat.ofHom α.toRingHom) ≫ i) hbase j gK hambient
  obtain ⟨g, hgb, hgi, hαg⟩ := cubicFieldPoint_exists_chart_from_component
    P hP i hi α.toRingHom j gE hgE
  refine ⟨g, hgb, hgi, ?_⟩
  intro r
  change (α.toRingHom.comp g) (chartCoordinate (equationIdeal P hP) j r) = _
  rw [hαg, hcoordE, hcoordK]

end PfaffianDescent
