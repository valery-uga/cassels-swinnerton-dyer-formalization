import PfaffianDescent.CorayFixedChartCanonicalResidueHom
import PfaffianDescent.CorayAiMovingRankThreeCutAvoidLowerDivisor
import PfaffianDescent.CorayAiNoSectionRankThreeCutField
import PfaffianDescent.CoraySelectedCurveOriginalClosedPoint
import PfaffianDescent.CorayBoundedOriginalChartEvaluation
import PfaffianDescent.CorayEntireModelIncidenceCycle
import PfaffianDescent.FiniteSchemeAlgebra

noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Ring-homogeneous evaluation bridge with a fixed target type. -/
private theorem normalizedChart_zero_implies_residueEvaluation_zero002
    {L : Type u} [CommRing L]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (j : Fin 4)
    (g : ChartRing I j →+* L) (f : K →+* L)
    (hg : g.comp (chartBaseMap I j) = f) (q : MvPolynomial (Fin 4) K)
    (hZero : g (q.eval₂ (chartBaseMap I j) (chartCoordinate I j)) = 0) :
    q.eval₂ f (fun k => g (chartCoordinate I j k)) = 0 := by
  have h := hom_eval₂ q (chartBaseMap I j) g (chartCoordinate I j)
  rw [hg] at h
  exact h.symm.trans hZero

/-- The native global-section spectrum map is over the same original base.
The finite scheme and its structure map remain abstract for this proof cut. -/
private theorem finiteScheme_nativeSpec_composition_base004
    {X S : Scheme.{u}} (f : X ⟶ Spec (.of K)) [IsFinite f] [IsAffine X]
    (pi : S ⟶ Spec (.of K)) (i : X ⟶ S) (hBase : i ≫ pi = f) :
    letI := finiteSchemeCoefficientAlgebra f
    (X.isoSpec.inv ≫ i) ≫ pi =
      Spec.map (CommRingCat.ofHom (algebraMap K Γ(X, ⊤))) := by
  letI := finiteSchemeCoefficientAlgebra f
  rw [Category.assoc, hBase]
  exact (finiteSchemeCoefficient_spec f).symm

/-- No-section forces the actual finite-scheme coefficient algebra to be a
field and yields an original degree-three closed image with its exact preimage.
No point, field structure or rank outcome is supplied. -/
private theorem finiteOriginalClosedScheme_rankThree_noSection_exists_degreeThreePoint004
    {X : Scheme.{u}}
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (f : X ⟶ Spec (.of K)) [IsFinite f]
    (i : X ⟶ hypersurface p hp) [IsClosedImmersion i]
    (hBase : i ≫ hypersurfaceToBase p hp = f)
    (hRank : finiteSchemeRank f = 3)
    (hno : ¬ ∃ t : Spec (.of K) ⟶ hypersurface p hp,
      t ≫ hypersurfaceToBase p hp = 𝟙 _) :
    ∃ (z : X) (A : closedPoints (hypersurface p hp)),
      A.1 = i z ∧ (hypersurfaceToBase p hp).residueDegree A.1 = 3 := by
  classical
  letI : IsAffine X := isAffine_of_isAffineHom f
  let B := Γ(X, ⊤)
  letI : Algebra K B := finiteSchemeCoefficientAlgebra f
  letI : Module.Finite K B := finiteSchemeCoefficient_finite f
  have hRankB : finrank K B = 3 := (finiteSchemeCoefficient_finrank f).trans hRank
  let j : Spec (.of B) ⟶ hypersurface p hp := X.isoSpec.inv ≫ i
  letI : IsClosedImmersion j := inferInstance
  have hjBase : j ≫ hypersurfaceToBase p hp =
      Spec.map (CommRingCat.ofHom (algebraMap K B)) :=
    finiteScheme_nativeSpec_composition_base004 f (hypersurfaceToBase p hp) i hBase
  have hField : IsField B :=
    cubic_noSection_rankThree_affineClosedCut_isField001 p hp j hjBase hRankB hno
  letI : Field B := hField.toField
  let b : Spec (.of B) := IsLocalRing.closedPoint B
  let A : closedPoints (hypersurface p hp) := ⟨j b, by
    change IsClosed ({j b} : Set (hypersurface p hp))
    rw [← Set.image_singleton]
    exact j.isClosedMap _ isClosed_singleton⟩
  have hDegree : (hypersurfaceToBase p hp).residueDegree A.1 = 3 := by
    letI : IsIso (j.residueFieldMap b) := isIso_residueFieldMap_of_surjectiveOnStalks j b
    have h := residueDegree_comp_of_residueFieldMap_isIso j (hypersurfaceToBase p hp) b
    rw [hjBase] at h
    exact h.symm.trans ((modelFieldSpectrum_original_residueDegree_eq_finrank
      (K := K) (M := B)).trans hRankB)
  exact ⟨X.isoSpec.inv b, A, rfl, hDegree⟩

/-- Original homogeneous divisor avoidance passes along the same quotient
closed immersions. This proof contains no finite-algebra or residue-field data. -/
private theorem homogeneousClass_not_mem_of_sameClosedSubscheme_avoidance004
    (I C Z : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hIC : I ≤ C) (hCZ : C ≤ Z) (s : MvPolynomial (Fin 4) K)
    (z : scheme Z)
    (hAvoid : Ideal.Quotient.mk C.toIdeal s ∉
      (schemeQuotientMap C Z hCZ z).asHomogeneousIdeal) :
    Ideal.Quotient.mk I.toIdeal s ∉
      (schemeQuotientMap I C hIC (schemeQuotientMap C Z hCZ z)).asHomogeneousIdeal := by
  intro hMem
  apply hAvoid
  have hRaw : s ∈ (quotientProjMap I
      (schemeQuotientMap I C hIC (schemeQuotientMap C Z hCZ z))).asHomogeneousIdeal.toIdeal := hMem
  have hEq : quotientProjMap I
      (schemeQuotientMap I C hIC (schemeQuotientMap C Z hCZ z)) =
      quotientProjMap C (schemeQuotientMap C Z hCZ z) :=
    congrArg (fun g => g (schemeQuotientMap C Z hCZ z))
      (schemeQuotientMap_comp_quotientProjMap I C hIC)
  rw [hEq] at hRaw
  exact hRaw

/-- The same finite whole rank-three cut gives a closed original degree-three
point avoiding its supplied divisor. Fieldness is derived from no-section. -/
private theorem originalRankThreeWholeCut_exists_degreeThreePoint_avoiding002
    (p s H G : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hH : H.IsHomogeneous 1) (hG : G.IsHomogeneous 1)
    (hFiniteZ : IsFinite (toBase (projectiveIntersectionIdeal p H hp hH ⊔ equationIdeal G hG)))
    (hRankZ : letI := hFiniteZ; finiteSchemeRank
      (toBase (projectiveIntersectionIdeal p H hp hH ⊔ equationIdeal G hG)) = 3)
    (hAvoidZ : ∀ z : scheme (projectiveIntersectionIdeal p H hp hH ⊔ equationIdeal G hG),
      Ideal.Quotient.mk (projectiveIntersectionIdeal p H hp hH).toIdeal s ∉
        (schemeQuotientMap (projectiveIntersectionIdeal p H hp hH)
          (projectiveIntersectionIdeal p H hp hH ⊔ equationIdeal G hG) le_sup_left z).asHomogeneousIdeal)
    (hno : ¬ ∃ t : Spec (.of K) ⟶ hypersurface p hp,
      t ≫ hypersurfaceToBase p hp = 𝟙 _) :
    let S := hypersurface p hp
    let I := equationIdeal p hp
    ∃ A : closedPoints S, (hypersurfaceToBase p hp).residueDegree A.1 = 3 ∧
      Ideal.Quotient.mk I.toIdeal s ∉ A.1.asHomogeneousIdeal := by
  classical
  intro S I
  let C := projectiveIntersectionIdeal p H hp hH
  let Z := C ⊔ equationIdeal G hG
  let piZ := toBase Z
  letI : IsFinite piZ := hFiniteZ
  let iz := schemeQuotientMap C Z le_sup_left
  let iC := schemeQuotientMap I C le_sup_left
  letI : IsClosedImmersion iz := schemeQuotientMap_closedImmersion C Z le_sup_left
  letI : IsClosedImmersion iC := schemeQuotientMap_closedImmersion I C le_sup_left
  let i : scheme Z ⟶ S := iz ≫ iC
  letI : IsClosedImmersion i := inferInstance
  have hBase : i ≫ hypersurfaceToBase p hp = piZ := by
    have hC : iC ≫ hypersurfaceToBase p hp = toBase C :=
      schemeQuotientMap_toBase I C le_sup_left
    have hZ : iz ≫ toBase C = piZ := schemeQuotientMap_toBase C Z le_sup_left
    change (iz ≫ iC) ≫ hypersurfaceToBase p hp = piZ
    rw [Category.assoc, hC]
    exact hZ
  obtain ⟨z, A, hA, hDegree⟩ :=
    finiteOriginalClosedScheme_rankThree_noSection_exists_degreeThreePoint004
      p hp piZ i hBase hRankZ hno
  refine ⟨A, hDegree, ?_⟩
  rw [hA]
  exact homogeneousClass_not_mem_of_sameClosedSubscheme_avoidance004
    I C Z le_sup_left le_sup_left s z (hAvoidZ z)

/-- Bound the actual moving cut, product avoidance and distinctness separately
from canonical residue recovery. No point or rank is supplied. -/
private theorem originalThroughPointPolynomial_exists_degreeThreePoint_avoiding_chart002
    [Infinite K]
    (p q0 : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq0 : q0.IsHomogeneous n)
    (hnot : q0 ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (P : closedPoints (hypersurface p hp)) (j : Fin 4) :
    let S := hypersurface p hp
    let I := equationIdeal p hp
    letI := pointAlgebra (hypersurfaceToBase p hp) P.1
    ∀ (gP : ChartRing I j →+* S.residueField P.1),
      gP.comp (chartBaseMap I j) = algebraMap K (S.residueField P.1) →
      Spec.map (CommRingCat.ofHom gP) ≫ chartι I j = S.fromSpecResidueField P.1 →
      q0.eval₂ (algebraMap K (S.residueField P.1))
        (fun k => gP (chartCoordinate I j k)) = 0 →
      (¬ ∃ s : Spec (.of K) ⟶ S, s ≫ hypersurfaceToBase p hp = 𝟙 _) →
      ∃ A : closedPoints S,
        (hypersurfaceToBase p hp).residueDegree A.1 = 3 ∧ A ≠ P ∧
        A.1 ∈ (chartι I j).opensRange ∧
        Ideal.Quotient.mk I.toIdeal q0 ∉ A.1.asHomogeneousIdeal ∧
        coordinate I j ∉ A.1.asHomogeneousIdeal := by
  classical
  intro S I
  letI := pointAlgebra (hypersurfaceToBase p hp) P.1
  intro gP hgPbase hgPpoint hqP hno
  let s := q0 * X j
  have hs : s.IsHomogeneous (n + 1) := hq0.mul (isHomogeneous_X K j)
  have hXnot : X j ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) := by
    intro h
    exact cubicCoordinate_ne_zero p hp hp0 j (Ideal.Quotient.eq_zero_iff_mem.mpr h)
  have hsnot : s ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) := by
    intro h
    rcases (PfaffianDescent.principalIdeal_prime_of_smooth_homogeneous_cubic p hp hp0).mem_or_mem h with h | h
    · exact hnot h
    · exact hXnot h
  have hsP : s.eval₂ (algebraMap K (S.residueField P.1))
      (fun k => gP (chartCoordinate I j k)) = 0 := by
    rw [show s = q0 * X j from rfl, eval₂_mul, hqP, zero_mul]
  obtain ⟨Pcut, hPcut, _, _⟩ :=
    selectedCurve_originalClosedPoint_of_original_chart_q_zero p s hp (n + 1) hs P
      j gP hgPbase hgPpoint hsP
  obtain ⟨H, G, hH, hG, _hAvoidP, hFiniteZ, hRankZ, hAvoidZ⟩ :=
    cubic_nonzeroSection_exists_rankThree_linearCut_avoiding_divisor001
      p s hp hp0 (n + 1) hs hsnot Pcut.1
  obtain ⟨A, hDegree, hSNot⟩ :=
    originalRankThreeWholeCut_exists_degreeThreePoint_avoiding002
      p s H G hp hH hG hFiniteZ hRankZ hAvoidZ hno
  have hQNot : Ideal.Quotient.mk I.toIdeal q0 ∉ A.1.asHomogeneousIdeal := by
    intro h
    apply hSNot
    change Ideal.Quotient.mk I.toIdeal (q0 * X j) ∈ A.1.asHomogeneousIdeal
    rw [map_mul]
    exact A.1.asHomogeneousIdeal.toIdeal.mul_mem_right _ h
  have hJNot : coordinate I j ∉ A.1.asHomogeneousIdeal := by
    intro h
    apply hSNot
    change Ideal.Quotient.mk I.toIdeal (q0 * X j) ∈ A.1.asHomogeneousIdeal
    rw [map_mul]
    exact A.1.asHomogeneousIdeal.toIdeal.mul_mem_left _ h
  have hChart : A.1 ∈ (chartι I j).opensRange := by
    rw [chartι_opensRange]
    exact hJNot
  have hDifferent : A ≠ P := by
    intro h
    apply hSNot
    rw [h]
    apply (homogeneousQuotient_equationSection_range_iff001 I s hs P.1).mp
    exact ⟨Pcut.1, hPcut⟩
  exact ⟨A, hDegree, hDifferent, hChart, hQNot, hJNot⟩

/-- Explicit cubic-target bridge for canonical fixed-chart residue recovery.
All output base and point equations use the same hypersurface residue type. -/
private theorem originalCubicPoint_fixedChart_canonicalResidueHom002
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (A : closedPoints (hypersurface p hp)) (j : Fin 4)
    (hChart : A.1 ∈ (chartι (equationIdeal p hp) j).opensRange) :
    letI := pointAlgebra (hypersurfaceToBase p hp) A.1
    ∃ gA : ChartRing (equationIdeal p hp) j →+* (hypersurface p hp).residueField A.1,
      Function.Surjective gA ∧
      gA.comp (chartBaseMap (equationIdeal p hp) j) =
        algebraMap K ((hypersurface p hp).residueField A.1) ∧
      Spec.map (CommRingCat.ofHom gA) ≫ chartι (equationIdeal p hp) j =
        (hypersurface p hp).fromSpecResidueField A.1 := by
  letI := pointAlgebra (hypersurfaceToBase p hp) A.1
  exact closedProjectivePoint_fixedChart_canonicalResidueHom001
    (equationIdeal p hp) A j hChart

/-- A literal nonzero homogeneous class at the original point forces nonzero
normalized evaluation in its exact recovered residue chart. -/
private theorem originalCubicPoint_chartEvaluation_nonzero_of_class_not_mem002
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (n : ℕ) (hq : q.IsHomogeneous n)
    (A : closedPoints (hypersurface p hp)) (j : Fin 4)
    (hNot : Ideal.Quotient.mk (equationIdeal p hp).toIdeal q ∉ A.1.asHomogeneousIdeal) :
    letI := pointAlgebra (hypersurfaceToBase p hp) A.1
    ∀ gA : ChartRing (equationIdeal p hp) j →+* (hypersurface p hp).residueField A.1,
      gA.comp (chartBaseMap (equationIdeal p hp) j) =
        algebraMap K ((hypersurface p hp).residueField A.1) →
      Spec.map (CommRingCat.ofHom gA) ≫ chartι (equationIdeal p hp) j =
        (hypersurface p hp).fromSpecResidueField A.1 →
      gA (q.eval₂ (chartBaseMap (equationIdeal p hp) j)
        (chartCoordinate (equationIdeal p hp) j)) ≠ 0 := by
  letI := pointAlgebra (hypersurfaceToBase p hp) A.1
  intro gA hgBase hgPoint hZero
  have hQZero := normalizedChart_zero_implies_residueEvaluation_zero002
    (equationIdeal p hp) j gA (algebraMap K ((hypersurface p hp).residueField A.1))
      hgBase q hZero
  obtain ⟨Qcut, hQcut, _, _⟩ :=
    selectedCurve_originalClosedPoint_of_original_chart_q_zero p q hp n hq A
      j gA hgBase hgPoint hQZero
  exact hNot ((homogeneousQuotient_equationSection_range_iff001
    (equationIdeal p hp) q hq A.1).mp ⟨Qcut.1, hQcut⟩)

/-- The original point and a nonzero degree-n section through it internally
produce a DIFFERENT original degree-three closed point in the chosen chart
and denominator open. No auxiliary point, fieldness, or rational section is
assumed. The literal whole cubic rank-three cut supplies its field. -/
theorem originalThroughPointPolynomial_noSection_exists_degreeThreePoint_in_fixedChart_denominatorOpen001
    [Infinite K]
    (p q0 : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq0 : q0.IsHomogeneous n)
    (hnot : q0 ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (P : closedPoints (hypersurface p hp)) (j : Fin 4) :
    let S := hypersurface p hp
    let I := equationIdeal p hp
    letI := pointAlgebra (hypersurfaceToBase p hp) P.1
    ∀ (gP : ChartRing I j →+* S.residueField P.1),
      gP.comp (chartBaseMap I j) = algebraMap K (S.residueField P.1) →
      Spec.map (CommRingCat.ofHom gP) ≫ chartι I j = S.fromSpecResidueField P.1 →
      q0.eval₂ (algebraMap K (S.residueField P.1))
        (fun k => gP (chartCoordinate I j k)) = 0 →
      (¬ ∃ s : Spec (.of K) ⟶ S, s ≫ hypersurfaceToBase p hp = 𝟙 _) →
      ∃ A : closedPoints S,
        (hypersurfaceToBase p hp).residueDegree A.1 = 3 ∧ A ≠ P ∧
        A.1 ∈ (chartι I j).opensRange ∧
        Ideal.Quotient.mk I.toIdeal q0 ∉ A.1.asHomogeneousIdeal ∧
        coordinate I j ∉ A.1.asHomogeneousIdeal ∧
        letI := pointAlgebra (hypersurfaceToBase p hp) A.1
        ∃ gA : ChartRing I j →+* S.residueField A.1,
          Function.Surjective gA ∧
          gA.comp (chartBaseMap I j) = algebraMap K (S.residueField A.1) ∧
          Spec.map (CommRingCat.ofHom gA) ≫ chartι I j = S.fromSpecResidueField A.1 ∧
          gA (q0.eval₂ (chartBaseMap I j) (chartCoordinate I j)) ≠ 0 := by
  classical
  intro S I
  letI := pointAlgebra (hypersurfaceToBase p hp) P.1
  intro gP hgPbase hgPpoint hqP hno
  obtain ⟨A, hDegree, hDifferent, hChart, hQNot, hJNot⟩ :=
    originalThroughPointPolynomial_exists_degreeThreePoint_avoiding_chart002
      p q0 hp hp0 n hq0 hnot P j gP hgPbase hgPpoint hqP hno
  refine ⟨A, hDegree, hDifferent, hChart, hQNot, hJNot, ?_⟩
  letI := pointAlgebra (hypersurfaceToBase p hp) A.1
  obtain ⟨gA, hgSurj, hgBase, hgPoint⟩ :=
    originalCubicPoint_fixedChart_canonicalResidueHom002 p hp A j hChart
  refine ⟨gA, hgSurj, hgBase, hgPoint, ?_⟩
  exact originalCubicPoint_chartEvaluation_nonzero_of_class_not_mem002
    p q0 hp n hq0 A j hQNot gA hgBase hgPoint

end PfaffianDescent.Coray
