import PfaffianDescent.CorayOriginalBasisNativeHyperplaneMember
import PfaffianDescent.CorayOriginalLiteralPQChartPrincipalKernel
import PfaffianDescent.CorayNativeFullAffineQuotientBaseChange
import AllCharacteristics.EffectiveCycleToZeroCycle

/-! SAME original basis hyperplane pullback IS the full literal q-curve
restriction on the actual denominator-nonzero original cubic chart. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
open scoped PfaffianDescent.Coray
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

/-- Normalized homogeneous evaluation depends on the literal graded class. -/
private theorem wholeCurve_normalizedGradeEvaluation002
    {K L : Type u} [Field K] [CommRing L] [Algebra K L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (n : ℕ)
    (y : Fin 4 → L) (hpy : p.eval₂ (algebraMap K L) y = 0) (j : Fin 4)
    (s : cubicThroughCoordinateSections p hp n y hpy)
    (q : MvPolynomial (Fin 4) K) (hq : q.IsHomogeneous n)
    (hs : Ideal.Quotient.mk (equationIdeal p hp).toIdeal q = s.1.1) :
    q.eval₂ (chartBaseMap (equationIdeal p hp) j)
      (chartCoordinate (equationIdeal p hp) j) =
      cubicThroughPointChartEvaluation p hp n y hpy j s := by
  let I := equationIdeal p hp
  have hGrade : (⟨Ideal.Quotient.mk I.toIdeal q,
      polynomial_class_mem_grading I q hq⟩ : grading I n) = s.1 := Subtype.ext hs
  rw [eval₂_chartCoordinate_eq_fraction I j q hq]
  change gradedChartSectionEvaluation (grading I) (coordinate_mem I j) n
    ⟨Ideal.Quotient.mk I.toIdeal q, polynomial_class_mem_grading I q hq⟩ =
      gradedChartSectionEvaluation (grading I) (coordinate_mem I j) n s.1
  exact congrArg (gradedChartSectionEvaluation (grading I) (coordinate_mem I j) n) hGrade

/-- Membership in every entire ideal identifies entire extended principal ideals. -/
private theorem wholeCurve_mapSpan_eq002
    {A R S : Type u} [CommRing A] [CommRing R] [CommRing S]
    (phi : A →+* S) (l : R →+* S) (h : A) (q : R)
    (hMembership : ∀ T : Ideal S, phi h ∈ T ↔ l q ∈ T) :
    (Ideal.span ({h} : Set A)).map phi = (Ideal.span ({q} : Set R)).map l := by
  rw [Ideal.map_span, Set.image_singleton, Ideal.map_span, Set.image_singleton]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro z hz
    obtain rfl := Set.mem_singleton_iff.mp hz
    exact (hMembership _).mpr (Ideal.subset_span (Set.mem_singleton _))
  · apply Ideal.span_le.mpr
    intro z hz
    obtain rfl := Set.mem_singleton_iff.mp hz
    exact (hMembership _).mp (Ideal.subset_span (Set.mem_singleton _))

/-- Equal entire ideals give a Spec isomorphism preserving the quotient projection. -/
private theorem wholeCurve_equalIdealSpecIso002
    {S : Type u} [CommRing S] (H Q : Ideal S) (h : H = Q) :
    ∃ E : Spec (.of (S ⧸ H)) ≅ Spec (.of (S ⧸ Q)),
      E.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk Q)) =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk H)) := by
  let e : (S ⧸ H) ≃+* S ⧸ Q := Ideal.quotEquivOfEq h
  let E : Spec (.of (S ⧸ H)) ≅ Spec (.of (S ⧸ Q)) :=
    Scheme.Spec.mapIso e.symm.toCommRingCatIso.op
  refine ⟨E, ?_⟩
  change Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk Q)) = _
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro s
  change (Ideal.quotEquivOfEq h).symm (Ideal.Quotient.mk Q s) = Ideal.Quotient.mk H s
  rw [Ideal.quotEquivOfEq_symm, Ideal.quotEquivOfEq_mk]

/-- Abstract chart transport, with the original inverse and all four literal maps. -/
private theorem wholeCurve_transportPullback002
    {R S : Type u} [CommRing R] [CommRing S]
    (l : R →+* S) (Q : Ideal R)
    (V : Scheme.{u}) (g : V ⟶ Spec (.of R))
    (Echart : V ≅ Spec (.of (R ⧸ Q)))
    (hEchart : Echart.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk Q)) = g) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Q.map l))))
      (Spec.map (CommRingCat.ofHom (nativeQuotientBaseChangeMap l Q)) ≫ Echart.inv)
      (Spec.map (CommRingCat.ofHom l)) g := by
  have HQ := nativeQuotientBaseChange_isPullback001 l Q
  apply HQ.of_iso (Iso.refl _) (Iso.refl _) Echart.symm (Iso.refl _)
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · simp only [Iso.refl_hom, Iso.symm_hom, Category.id_comp]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom]
    calc
      _ = Echart.inv ≫ (Echart.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk Q))) := by
        simp only [Iso.inv_hom_id_assoc]
      _ = Echart.inv ≫ g := by rw [hEchart]

/-- Full affine cuts glued to a Cartesian chart compare over the same source. -/
private theorem wholeCurve_affineChartRestrictionIso002
    {A R S : Type u} [CommRing A] [CommRing R] [CommRing S]
    (phi : A →+* S) (l : R →+* S) (H : Ideal A) (Q : Ideal R)
    (hIdeals : H.map phi = Q.map l)
    (X C V : Scheme.{u}) (i : Spec (.of R) ⟶ X) (f : C ⟶ X)
    (g : V ⟶ Spec (.of R)) (j : V ⟶ C)
    (Echart : V ≅ Spec (.of (R ⧸ Q)))
    (hEchart : Echart.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk Q)) = g)
    (hChart : IsPullback g j i f) :
    ∃ E : pullback (Spec.map (CommRingCat.ofHom phi))
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk H))) ≅
        pullback (Spec.map (CommRingCat.ofHom l) ≫ i) f,
      E.hom ≫ pullback.fst (Spec.map (CommRingCat.ofHom l) ≫ i) f =
        pullback.fst (Spec.map (CommRingCat.ofHom phi))
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk H))) := by
  have HQchart := wholeCurve_transportPullback002 l Q V g Echart hEchart
  have HQwhole := HQchart.paste_vert hChart
  have HH := nativeQuotientBaseChange_isPullback001 phi H
  obtain ⟨Ecut, hEcut⟩ := wholeCurve_equalIdealSpecIso002 (H.map phi) (Q.map l) hIdeals
  let E := HH.isoPullback.symm ≪≫ Ecut ≪≫ HQwhole.isoPullback
  refine ⟨E, ?_⟩
  change (HH.isoPullback.inv ≫ Ecut.hom ≫ HQwhole.isoPullback.hom) ≫ _ = _
  rw [Category.assoc, Category.assoc, HQwhole.isoPullback_hom_fst]
  rw [hEcut]
  exact HH.isoPullback_inv_fst

/-- Actual original coefficient vector constructs q and a native isomorphism
between its hyperplane pullback and the restriction of SAME whole (p,q) curve.
Every map/projection is kept literal. No GI/reducedness or matching-ideal/
pullback-isomorphism premise, no point/outcome choice or curve replacement. -/
theorem cubicThroughPointBasis_nativeHyperplanePullback_exists_sameWholeCurveRestrictionIso001
    {K L : Type u} [Field K] [CommRing L] [Algebra K L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ)
    (y : Fin 4 → L) (hpy : p.eval₂ (algebraMap K L) y = 0) (j : Fin 4)
    {m : ℕ} (b : Module.Basis (Fin m) K (cubicThroughCoordinateSections p hp n y hpy))
    (a : Fin m) (c : Fin m → K) (hc : c ≠ 0) :
    let I := equationIdeal p hp
    let e := cubicThroughPointChartEvaluation p hp n y hpy j
    let x := fun i => e (b i)
    let R := ChartRing I j
    let S := Localization.Away (x a)
    let A := ChartRing (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin m) K)) a
    let H := Ideal.span ({projectiveChartLinearForm a c} : Set A)
    let phi := nativeLocalizedProjectiveChartMap (chartBaseMap I j) x a
    let v := Spec.map (CommRingCat.ofHom phi)
    let u := Spec.map (CommRingCat.ofHom (algebraMap R S)) ≫ chartι I j
    x a ≠ 0 ∧ ∃ (q : MvPolynomial (Fin 4) K) (hq : q.IsHomogeneous n),
      q.eval₂ (algebraMap K L) y = 0 ∧ q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) ∧
      Ideal.Quotient.mk I.toIdeal q = (∑ i, c i • b i).1.1 ∧
      ∃ E : pullback v (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk H))) ≅
          pullback u (cubicSecondEquationCurveImmersion p q hp n hq),
        E.hom ≫ pullback.fst u (cubicSecondEquationCurveImmersion p q hp n hq) =
          pullback.fst v (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk H))) := by
  classical
  let I := equationIdeal p hp
  let e := cubicThroughPointChartEvaluation p hp n y hpy j
  let x := fun i => e (b i)
  let R := ChartRing I j
  let S := Localization.Away (x a)
  let l : R →+* S := algebraMap R S
  let A := ChartRing (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin m) K)) a
  let H := Ideal.span ({projectiveChartLinearForm a c} : Set A)
  let phi := nativeLocalizedProjectiveChartMap (chartBaseMap I j) x a
  obtain ⟨hDenominator, q, hq, hy, hnot, hqClass, _hEquation, hMembership⟩ :=
    cubicThroughPointBasis_nativeLocalizedHyperplane_exists_originalMember001
      p hp hp0 n y hpy j b a c hc
  let J := projectiveIntersectionIdeal p q hp hq
  let normalizedQ := q.eval₂ (chartBaseMap I j) (chartCoordinate I j)
  let Q := Ideal.span ({normalizedQ} : Set R)
  have hNormalized : normalizedQ = e (∑ i, c i • b i) :=
    wholeCurve_normalizedGradeEvaluation002 p hp n y hpy j (∑ i, c i • b i) q hq hqClass
  have hIdeals : H.map phi = Q.map l := by
    apply wholeCurve_mapSpan_eq002 phi l (projectiveChartLinearForm a c) normalizedQ
    rw [hNormalized]
    exact hMembership
  obtain ⟨Echart, hEchart, _hChartMap, hChart⟩ :=
    cubicSecondEquation_chart_exists_nativePrincipalCutIso001 p q hp n hq j
  refine ⟨hDenominator, q, hq, hy, hnot, hqClass, ?_⟩
  exact wholeCurve_affineChartRestrictionIso002 phi l H Q hIdeals
    (scheme I) (scheme J) (Spec (.of (ChartRing J j))) (chartι I j)
    (cubicSecondEquationCurveImmersion p q hp n hq)
    (Spec.map (CommRingCat.ofHom (PfaffianDescent.chartQuotientMap I J le_sup_left j)))
    (chartι J j) Echart hEchart hChart

end PfaffianDescent.Coray
