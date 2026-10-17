import PfaffianDescent.CorayOriginalLeastWindowFinalCaseReduction
import PfaffianDescent.CoraySelectedCurveOriginalClosedPoint
import PfaffianDescent.CorayAiOriginalSelectedSectionRegularAuxiliaryPointEndpoint

noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial Module TrivSqZeroExt
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open scoped PfaffianDescent.Coray
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The SAME original least-point strict window derives integral WHOLE
members from the accepted A(ii)/A(iii)/B case reduction. The degree4/n2 and
10/n3 outcomes are excluded by the actual strict degree, so no integral
family, selected q, chart, basis or component is supplied. -/
theorem leastOriginalCubicPoint_strictWindow_allFreshSelectedCurves_integral001
    {K : Type u} [Field K] [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (P : closedPoints (hypersurface p hp))
    (hPointCoprime : Nat.Coprime ((hypersurfaceToBase p hp).residueDegree P.1) 3)
    (hleast : ∀ R : closedPoints (hypersurface p hp),
      Nat.Coprime ((hypersurfaceToBase p hp).residueDegree R.1) 3 →
        (hypersurfaceToBase p hp).residueDegree P.1 ≤ (hypersurfaceToBase p hp).residueDegree R.1)
    (hno : ¬ ∃ s : Spec (.of K) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _)
    (n : ℕ) (hn : 3 ≤ n)
    (hStrict : 3 * n.choose 2 + 1 < (hypersurfaceToBase p hp).residueDegree P.1)
    (hUpper : (hypersurfaceToBase p hp).residueDegree P.1 < 1 + 3 * (n + 1).choose 2) :
    ∀ (q : MvPolynomial (Fin 4) K) (hq : q.IsHomogeneous n),
      q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) →
      P.1 ∈ Set.range (cubicSecondEquationCurveImmersion p q hp n hq) →
      IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq)) := by
  have hLower : 1 + 3 * n.choose 2 ≤ (hypersurfaceToBase p hp).residueDegree P.1 := by omega
  rcases coray_leastOriginalPoint_window_eq_four_or_ten_or_strict_integral_family001
    p hp hp0 P hPointCoprime hleast hno n hLower hUpper with hFour | hTen | hResidual
  · have hnTwo := hFour.2
    omega
  · rcases hTen with ⟨hDegree, hnThree⟩
    have h := hStrict
    rw [hnThree] at h
    norm_num at h
    omega
  · rcases hResidual with ⟨_hn, _hLarge, _hStrict, _hFreedom, _hSize, hAll, _hMember⟩
    exact hAll

/-- Original chart-q zero constructs the actual closed lift of the SAME
P, hence its literal image incidence, before using the internally derived
strict integral family. The supplied original chart is retained. -/
theorem leastOriginalCubicPoint_strictWindow_originalChart_allFreshEquations_integral001
    {K : Type u} [Field K] [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (P : closedPoints (hypersurface p hp))
    (hPointCoprime : Nat.Coprime ((hypersurfaceToBase p hp).residueDegree P.1) 3)
    (hleast : ∀ R : closedPoints (hypersurface p hp),
      Nat.Coprime ((hypersurfaceToBase p hp).residueDegree R.1) 3 →
        (hypersurfaceToBase p hp).residueDegree P.1 ≤ (hypersurfaceToBase p hp).residueDegree R.1)
    (hno : ¬ ∃ s : Spec (.of K) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _)
    (n : ℕ) (hn : 3 ≤ n)
    (hStrict : 3 * n.choose 2 + 1 < (hypersurfaceToBase p hp).residueDegree P.1)
    (hUpper : (hypersurfaceToBase p hp).residueDegree P.1 < 1 + 3 * (n + 1).choose 2) :
    let S := hypersurface p hp
    letI := pointAlgebra (hypersurfaceToBase p hp) P.1
    ∀ (j : Fin 4) (gP : ChartRing (equationIdeal p hp) j →+* S.residueField P.1),
      gP.comp (chartBaseMap (equationIdeal p hp) j) = algebraMap K (S.residueField P.1) →
      Spec.map (CommRingCat.ofHom gP) ≫ chartι (equationIdeal p hp) j = S.fromSpecResidueField P.1 →
      ∀ (q : MvPolynomial (Fin 4) K) (hq : q.IsHomogeneous n),
        q.eval₂ (algebraMap K (S.residueField P.1))
          (fun i => gP (chartCoordinate (equationIdeal p hp) j i)) = 0 →
        q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) →
        IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq)) := by
  intro S
  letI := pointAlgebra (hypersurfaceToBase p hp) P.1
  intro j gP hBase hPoint q hq hZero hnot
  obtain ⟨PX, hPX, _hPXiso, _hPXdegree⟩ :=
    selectedCurve_originalClosedPoint_of_original_chart_q_zero p q hp n hq P j gP hBase hPoint hZero
  exact leastOriginalCubicPoint_strictWindow_allFreshSelectedCurves_integral001
    p hp hp0 P hPointCoprime hleast hno n hn hStrict hUpper q hq hnot ⟨PX.1, hPX⟩

/-- Conditional natural Ai contradiction with NO integral-family input.
The SAME original least point/window derives it through the accepted case
reduction; the actual literalB cut, embedding and selected original section
then construct q, own regular degree-three AX, and a strictly smaller
original coprime-degree R. Actual cut/section selection remains explicit. -/
theorem leastOriginalCubicPoint_strictWindow_actualAuxiliarySection_nonzeroNativeJet_false001
    {K B M : Type u} [Field K] [CharZero K] [Field B] [Field M]
    [Algebra K B] [Algebra K M]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 3 ≤ n)
    (P A : closedPoints (hypersurface p hp))
    (hPcop : Nat.Coprime ((hypersurfaceToBase p hp).residueDegree P.1) 3)
    (hleast : ∀ R : closedPoints (hypersurface p hp),
      Nat.Coprime ((hypersurfaceToBase p hp).residueDegree R.1) 3 →
        (hypersurfaceToBase p hp).residueDegree P.1 ≤ (hypersurfaceToBase p hp).residueDegree R.1)
    (hno : ¬ ∃ s : Spec (.of K) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _)
    (hStrict : 3 * n.choose 2 + 1 < (hypersurfaceToBase p hp).residueDegree P.1)
    (hUpper : (hypersurfaceToBase p hp).residueDegree P.1 < 1 + 3 * (n + 1).choose 2)
    (hAdegree : (hypersurfaceToBase p hp).residueDegree A.1 = 3) :
    let S := hypersurface p hp
    letI := pointAlgebra (hypersurfaceToBase p hp) P.1
    ∀ (jP : Fin 4) (gP : ChartRing (equationIdeal p hp) jP →+* S.residueField P.1),
      gP.comp (chartBaseMap (equationIdeal p hp) jP) = algebraMap K (S.residueField P.1) →
      Spec.map (CommRingCat.ofHom gP) ≫ chartι (equationIdeal p hp) jP = S.fromSpecResidueField P.1 →
      ∀ (hpP : p.eval₂ (algebraMap K (S.residueField P.1))
        (fun i => gP (chartCoordinate (equationIdeal p hp) jP i)) = 0),
      ∀ (r : Spec (.of B) ⟶ S) (jA : Fin 4) (gB : ChartRing (equationIdeal p hp) jA →+* B),
      gB.comp (chartBaseMap (equationIdeal p hp) jA) = algebraMap K B →
      Spec.map (CommRingCat.ofHom gB) ≫ chartι (equationIdeal p hp) jA = r →
      r (IsLocalRing.closedPoint B) = A.1 →
      ∀ (sigma : B →ₐ[K] M) (v : Fin 2 → Fin 4 → M)
        (hpJ : p.eval₂ (algebraMap K (SurfacePlaneJet M))
          (surfacePlaneJetCoordinates (fun i => sigma (gB (chartCoordinate (equationIdeal p hp) jA i))) v) = 0)
        (hAnchor : surfacePlaneJetCoordinates
          (fun i => sigma (gB (chartCoordinate (equationIdeal p hp) jA i))) v jA = 1)
        (s : cubicThroughCoordinateSections p hp n
          (fun i => gP (chartCoordinate (equationIdeal p hp) jP i)) hpP),
      gB (cubicThroughPointChartEvaluation p hp n
        (fun i => gP (chartCoordinate (equationIdeal p hp) jP i)) hpP jA s) = 0 →
      cubicNormalizedFullJetChartMap p hp jA
        (fun i => sigma (gB (chartCoordinate (equationIdeal p hp) jA i))) v hpJ hAnchor
        (cubicThroughPointChartEvaluation p hp n
          (fun i => gP (chartCoordinate (equationIdeal p hp) jP i)) hpP jA s) ≠ 0 → False := by
  intro S
  letI := pointAlgebra (hypersurfaceToBase p hp) P.1
  intro jP gP hBaseP hPointP hpP r jA gB hBaseB hChart hOriginalPoint sigma v hpJ hAnchor s hAux hJet
  have hAllIntegral := leastOriginalCubicPoint_strictWindow_originalChart_allFreshEquations_integral001
    p hp hp0 P hPcop hleast hno n hn hStrict hUpper jP gP hBaseP hPointP
  obtain ⟨R, hRcop, _hRbound, hRsmall⟩ :=
    coray_case_Ai_originalSelectedSection_actualAuxiliaryField_nonzeroNativeJet_exists_smaller_originalCubic_closedPoint001
      p hp hp0 n (by omega) P A hPcop hStrict hAdegree jP gP hBaseP hPointP hpP hAllIntegral
      r jA gB hBaseB hChart hOriginalPoint sigma v hpJ hAnchor s hAux hJet
  exact (not_lt_of_ge (hleast R hRcop)) hRsmall

end PfaffianDescent.Coray
