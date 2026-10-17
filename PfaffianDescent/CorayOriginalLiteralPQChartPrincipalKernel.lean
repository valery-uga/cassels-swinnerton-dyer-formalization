import PfaffianDescent.CorayCubicSecondEquationActualCurveUnit
import AllCharacteristics.AffineChartPresentation

/-! Literal homogeneous p/q curve restriction has exactly the normalized
q principal ideal in the ORIGINAL cubic coordinate chart. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

/-- The native quotient-chart kernel is its literal homogeneous chart
presentation ideal evaluated in the original chart. No kernel premise. -/
theorem homogeneousQuotient_chartKernel_eq_presentationImage001
    {K : Type u} [CommRing K] {σ : Type}
    (I J : HomogeneousIdeal (homogeneousSubmodule σ K))
    (hIJ : I.toIdeal ≤ J.toIdeal) (j : σ) :
    RingHom.ker (PfaffianDescent.chartQuotientMap I J hIJ j) =
      (chartPresentationIdeal J j).map (eval₂Hom (chartBaseMap I j) (chartCoordinate I j)) := by
  let f := PfaffianDescent.chartQuotientMap I J hIJ j
  let evI := eval₂Hom (chartBaseMap I j) (chartCoordinate I j)
  let evJ := eval₂Hom (chartBaseMap J j) (chartCoordinate J j)
  have hComp : f.comp evI = evJ := by
    apply RingHom.ext
    intro p
    exact PfaffianDescent.chartQuotientMap_eval₂ I J hIJ j p
  have hKernel : RingHom.ker evJ = chartPresentationIdeal J j := chartEvaluation_ker J j
  apply le_antisymm
  · intro x hx
    obtain ⟨p, rfl⟩ := eval₂_chartCoordinate_surjective I j x
    apply Ideal.mem_map_of_mem evI
    rw [← hKernel]
    change evJ p = 0
    rw [← hComp]
    exact hx
  · rw [Ideal.map_le_iff_le_comap]
    intro p hp
    change f (evI p) = 0
    rw [← RingHom.comp_apply, hComp]
    have hpKernel : p ∈ RingHom.ker evJ := by simpa only [hKernel] using hp
    exact hpKernel

/-- The exact chart kernel of the SAME original (p,q) curve is generated
by the normalized polynomial q itself, including all nilpotents/multiplicity. -/
theorem cubicSecondEquation_chartQuotientMap_ker_eq_normalizedEquation001
    {K : Type u} [Field K]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (n : ℕ) (hq : q.IsHomogeneous n) (j : Fin 4) :
    RingHom.ker (PfaffianDescent.chartQuotientMap (equationIdeal p hp)
      (projectiveIntersectionIdeal p q hp hq) le_sup_left j) =
        Ideal.span ({q.eval₂ (chartBaseMap (equationIdeal p hp) j)
          (chartCoordinate (equationIdeal p hp) j)} : Set (ChartRing (equationIdeal p hp) j)) := by
  let I := equationIdeal p hp
  let J := projectiveIntersectionIdeal p q hp hq
  let evI := eval₂Hom (chartBaseMap I j) (chartCoordinate I j)
  have hPresentation : chartPresentationIdeal J j =
      chartPresentationIdeal I j ⊔ Ideal.span ({q} : Set (MvPolynomial (Fin 4) K)) := by
    dsimp only [chartPresentationIdeal, J, I]
    rw [projectiveIntersectionIdeal_toIdeal]
    change (Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) ⊔ Ideal.span {X j - 1}) =
      (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) ⊔ Ideal.span {X j - 1}) ⊔ Ideal.span {q}
    rw [Ideal.span_insert]
    ac_rfl
  have hOriginalZero : (chartPresentationIdeal I j).map evI = ⊥ :=
    (Ideal.map_eq_bot_iff_le_ker evI).mpr (by
      change chartPresentationIdeal I j ≤ RingHom.ker
        (eval₂Hom (chartBaseMap I j) (chartCoordinate I j))
      rw [chartEvaluation_ker])
  change RingHom.ker (PfaffianDescent.chartQuotientMap I J le_sup_left j) =
    Ideal.span ({evI q} : Set (ChartRing I j))
  rw [homogeneousQuotient_chartKernel_eq_presentationImage001 I J le_sup_left j, hPresentation,
    Ideal.map_sup, hOriginalZero, bot_sup_eq, Ideal.map_span, Set.image_singleton]

/-- The SAME affine chart of the original p/q curve is the honest principal
quotient of the original cubic chart, with the actual quotient-map equality. -/
theorem cubicSecondEquation_chart_exists_normalizedQuotientEquiv001
    {K : Type u} [Field K]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (n : ℕ) (hq : q.IsHomogeneous n) (j : Fin 4) :
    let I := equationIdeal p hp
    let J := projectiveIntersectionIdeal p q hp hq
    let Q := Ideal.span ({q.eval₂ (chartBaseMap I j) (chartCoordinate I j)} : Set (ChartRing I j))
    ∃ e : (ChartRing I j ⧸ Q) ≃+* ChartRing J j,
      e.toRingHom.comp (Ideal.Quotient.mk Q) =
        PfaffianDescent.chartQuotientMap I J le_sup_left j := by
  let I := equationIdeal p hp
  let J := projectiveIntersectionIdeal p q hp hq
  let f := PfaffianDescent.chartQuotientMap I J le_sup_left j
  let Q := Ideal.span ({q.eval₂ (chartBaseMap I j) (chartCoordinate I j)} : Set (ChartRing I j))
  have hKernel : RingHom.ker f = Q :=
    cubicSecondEquation_chartQuotientMap_ker_eq_normalizedEquation001 p q hp n hq j
  have hSurj : Function.Surjective f := PfaffianDescent.chartQuotientMap_surjective I J le_sup_left j
  let e : (ChartRing I j ⧸ Q) ≃+* ChartRing J j :=
    (Ideal.quotEquivOfEq hKernel.symm).trans (RingHom.quotientKerEquivOfSurjective hSurj)
  refine ⟨e, ?_⟩
  apply RingHom.ext
  intro r
  change (RingHom.quotientKerEquivOfSurjective hSurj)
    ((Ideal.quotEquivOfEq hKernel.symm) (Ideal.Quotient.mk Q r)) = f r
  exact (congrArg (RingHom.quotientKerEquivOfSurjective hSurj)
    (Ideal.quotEquivOfEq_mk hKernel.symm r)).trans
      (RingHom.quotientKerEquivOfSurjective_apply_mk hSurj r)


/-- Native scheme equivalence and its actual map square identify the chart
with the literal principal cut of the ORIGINAL cubic chart. The final
Cartesian assertion is the SAME whole p/q immersion restriction. -/
theorem cubicSecondEquation_chart_exists_nativePrincipalCutIso001
    {K : Type u} [Field K]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (n : ℕ) (hq : q.IsHomogeneous n) (j : Fin 4) :
    let I := equationIdeal p hp
    let J := projectiveIntersectionIdeal p q hp hq
    let Q := Ideal.span ({q.eval₂ (chartBaseMap I j) (chartCoordinate I j)} : Set (ChartRing I j))
    ∃ E : Spec (.of (ChartRing J j)) ≅ Spec (.of (ChartRing I j ⧸ Q)),
      E.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk Q)) =
        Spec.map (CommRingCat.ofHom (PfaffianDescent.chartQuotientMap I J le_sup_left j)) ∧
      E.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk Q)) ≫ chartι I j =
        chartι J j ≫ cubicSecondEquationCurveImmersion p q hp n hq ∧
      IsPullback
        (Spec.map (CommRingCat.ofHom (PfaffianDescent.chartQuotientMap I J le_sup_left j)))
        (chartι J j) (chartι I j) (cubicSecondEquationCurveImmersion p q hp n hq) := by
  let I := equationIdeal p hp
  let J := projectiveIntersectionIdeal p q hp hq
  let Q := Ideal.span ({q.eval₂ (chartBaseMap I j) (chartCoordinate I j)} : Set (ChartRing I j))
  obtain ⟨e, he⟩ := cubicSecondEquation_chart_exists_normalizedQuotientEquiv001 p q hp n hq j
  let E : Spec (.of (ChartRing J j)) ≅ Spec (.of (ChartRing I j ⧸ Q)) :=
    Scheme.Spec.mapIso e.toCommRingCatIso.op
  have hE : E.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk Q)) =
      Spec.map (CommRingCat.ofHom (PfaffianDescent.chartQuotientMap I J le_sup_left j)) := by
    change Spec.map (CommRingCat.ofHom e.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk Q)) = _
    rw [← Spec.map_comp]
    change Spec.map (CommRingCat.ofHom (e.toRingHom.comp (Ideal.Quotient.mk Q))) = _
    rw [he]
  refine ⟨E, hE, ?_, PfaffianDescent.isPullback_schemeQuotientMap_chart I J le_sup_left j⟩
  rw [← Category.assoc, hE]
  exact (PfaffianDescent.chartι_schemeQuotientMap I J le_sup_left j).symm

end PfaffianDescent.Coray
