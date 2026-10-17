import PfaffianDescent.CubicFieldPointSelectedComponentChart
import PfaffianDescent.CubicFieldPointComponentCoordinates
import PfaffianDescent.CubicHomogeneousChartRestriction
import PfaffianDescent.CubicElevenPointGroundDerivativeSpan

/-! Full interpolation on actual labeled components yields the original
closed-point cubic kernel, its dimension, and its six derivative span. -/

noncomputable section
namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization Module
open AllCharacteristics.HomogeneousProjective

universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem cubicFieldPointElevenInterpolation_exists_chart_kernel
    {K F L E : Type u} [Field K] [Field F] [Field L] [Field E]
    [Algebra K E] [Algebra F L] [Algebra F E] [FiniteDimensional F L]
    (f : K →+* F)
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : MvPolynomial (Fin 4) F) (hP : P.IsHomogeneous 3)
    (i : Spec (.of L) ⟶ hypersurface P hP)
    (hi : i ≫ hypersurfaceToBase P hP = Spec.map (CommRingCat.ofHom (algebraMap F L)))
    (hL : finrank F L = 11) (α : Fin 11 → (L →ₐ[F] E))
    (x : Fin 11 → Fin 4 → E)
    (ell : MvPolynomial (Fin 4) K) (hell : ell.IsHomogeneous 1)
    (he : ∀ k q, q ∈ (equationIdeal p hp).toIdeal → q.eval₂ (algebraMap K E) (x k) = 0)
    (hzOne : ∀ k, (Ideal.Quotient.lift (equationIdeal p hp).toIdeal
      (eval₂Hom (algebraMap K E) (x k)) (he k))
        (Ideal.Quotient.mk (equationIdeal p hp).toIdeal ell) = 1)
    (hpoint : ∀ k, Spec.map (CommRingCat.ofHom (α k).toRingHom) ≫ i ≫
        hypersurfaceToAmbient P hP ≫ ambientCoefficientMap f =
      linearNormalizedPointAt (equationIdeal p hp) (x k) (he k)
        (Ideal.Quotient.mk (equationIdeal p hp).toIdeal ell)
        (polynomial_class_mem_grading (equationIdeal p hp) ell hell) (hzOne k) ≫
        hypersurfaceToAmbient p hp)
    (j : Fin 4) (hxj : x 0 j ≠ 0)
    (y : Fin 11 → Fin 4 → E) (scale : Fin 11 → E)
    (hy : ∀ k r, y k r = scale k * x k r)
    (J : Fin 3 → Fin 4 → CubicSurfaceFirstJet E)
    (hresidue : ∀ k r, (J k r).fst = y (k.castAdd 8) r)
    (hfull : Function.Surjective (cubicElevenPointFullJetRestriction y J)) :
    ∃ g : ChartRing (equationIdeal P hP) j →+* L,
      g.comp (chartBaseMap (equationIdeal P hP) j) = algebraMap F L ∧
      Spec.map (CommRingCat.ofHom g) ≫ chartι (equationIdeal P hP) j = i ∧
      let R := cubicHomogeneousChartRestriction (equationIdeal P hP)
        (coordinate (equationIdeal P hP) j) (coordinate_mem (equationIdeal P hP) j) g
      (∀ q, R q = 0 → cubicElevenPointValueRestriction y
        (voisinDegreeTenSelectedAvoidance_mapCubicSection (L := E) q) = 0) ∧
      finrank F R.ker = 9 ∧
      ∀ B : Basis (Fin 9) F R.ker,
        Submodule.span E (Set.range (fun k : Fin 9 => fun r : Fin 3 =>
          (aeval (J r) ((B k).1.1.map (algebraMap F E))).snd)) = ⊤ := by
  obtain ⟨g, hgb, hgi, _⟩ := cubicFieldPoint_exists_chart_from_selected_component
    f p hp P hP i hi (α 0) (x 0) ell hell (he 0) (hzOne 0) (hpoint 0) j hxj
  let I := equationIdeal P hP
  let z := coordinate I j
  let hz := coordinate_mem I j
  let R := cubicHomogeneousChartRestriction I z hz g
  have hcoordinates : ∀ k, x k j ≠ 0 ∧ ∀ r,
      α k (g (linearChartCoordinate I z hz r)) = (x k j)⁻¹ * x k r := by
    intro k
    exact cubicFieldPoint_component_coordinates_eq_selected_ratios
      f p hp P hP i j g hgi (α k).toRingHom (x k) ell hell (he k) (hzOne k) (hpoint k)
  have hycoords : ∀ k r, y k r = (scale k * x k j) *
      α k (g (linearChartCoordinate I z hz r)) := by
    intro k r
    rw [hy, (hcoordinates k).2]
    calc
      scale k * x k r = scale k * (x k j * (x k j)⁻¹) * x k r := by
        rw [mul_inv_cancel₀ (hcoordinates k).1, mul_one]
      _ = (scale k * x k j) * ((x k j)⁻¹ * x k r) := by ring
  have hmem : ∀ q, R q = 0 → cubicElevenPointValueRestriction y
      (voisinDegreeTenSelectedAvoidance_mapCubicSection (L := E) q) = 0 := by
    intro q hq
    exact cubicHomogeneousChartRestriction_mem_elevenPointKernel I z hz g α y
      (fun k => scale k * x k j) hycoords q hq
  have hvalues := cubicElevenPointValueRestriction_surjective_of_fullJets y J hresidue hfull
  have hdim := cubicElevenPoint_groundKernel_finrank_of_split_values R hL.le y hvalues hmem
  refine ⟨g, hgb, hgi, hmem, hdim, ?_⟩
  intro B
  exact cubicElevenPoint_groundKernel_derivativeFamily_spans R hL.le y J
    hresidue hfull hmem B

end PfaffianDescent
