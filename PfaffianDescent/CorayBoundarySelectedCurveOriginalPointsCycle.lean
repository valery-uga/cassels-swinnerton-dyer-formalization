import PfaffianDescent.CorayBoundaryActualCubicPointFullJetEquationChoice
import PfaffianDescent.CoraySelectedCurveOriginalClosedPoint
import PfaffianDescent.CorayGroundProjectiveCurveLocalDefect

/-! SOURCE ONLY / UNVERIFIED. Actual boundary q selection now lifts BOTH
original P and constructed cubic A to SAME selected p/q curve, with actual
residue-map isomorphisms and full original degrees. Its reduced degree3
curve cycle is constructed, not supplied. Native auxiliary full-jet/stalk
transport, nonregularity and genuine GI classification remain separate. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial Module TrivSqZeroExt
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem originalNormalizedFullJet_zero_residue_value
    {K M : Type u} [Field K] [Field M] [Algebra K M]
    (p q : MvPolynomial (Fin 4) K) (j : Fin 4) (x : Fin 4 → M)
    (hx : x j = 1) (pivot : Fin 3)
    (hjet : q.eval₂ ((algebraMap M (PfaffianDescent.CubicSurfaceFirstJet M)).comp (algebraMap K M))
      (PfaffianDescent.cubicNormalizedSurfacePoint_tangentJet
        (p.map (algebraMap K M)) j x pivot) = 0) :
    q.eval₂ (algebraMap K M) x = 0 := by
  have hground : groundAffineSurfaceJetMap (normalizedAffineEquation j p)
      (fun r => x (j.succAbove r)) pivot (normalizedAffineEquation j q) = 0 :=
    (normalizedGroundAffineEquation_jet_evaluation p q j x hx pivot).trans hjet
  have hvalue := congrArg TrivSqZeroExt.fst hground
  rw [groundAffineSurfaceJetMap_fst, TrivSqZeroExt.fst_zero] at hvalue
  exact (normalizedGroundAffineEquation_evaluation q j x hx).symm.trans hvalue

/-- Boundary actual q, BOTH original points lifted to the SAME actual curve,
and its actual disjoint reduced degree3 cycle. Exact auxiliary residue-chart
recovery and the selected full jet are retained for the next OWN stalk cut.
There is no supplied cycle/GI/native surjectivity/nonregularity premise. -/
theorem boundary_exists_selectedCurve_originalPoint_and_disjoint_reducedCubic_cycle
    {K : Type u} [Field K] [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (P : closedPoints (hypersurface p hp))
    (hPcop : Nat.Coprime ((hypersurfaceToBase p hp).residueDegree P.1) 3)
    (hno : ¬ ∃ s : Spec (.of K) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _)
    (m : ℕ) (hm : 3 ≤ m)
    (hdegree : (hypersurfaceToBase p hp).residueDegree P.1 =
      (m + 3).choose 3 - m.choose 3) :
    ∃ (A : closedPoints (hypersurface p hp)) (q : MvPolynomial (Fin 4) K)
      (hq : q.IsHomogeneous (m + 1)),
      q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) ∧ A ≠ P ∧
      (hypersurfaceToBase p hp).residueDegree A.1 = 3 ∧
      let S := hypersurface p hp
      let X := scheme (projectiveIntersectionIdeal p q hp hq)
      let i := cubicSecondEquationCurveImmersion p q hp (m + 1) hq
      ∃ (PX AX : closedPoints X) (zcycle : EffectiveZeroCycle X),
        i PX.1 = P.1 ∧ i AX.1 = A.1 ∧
        IsIso (i.residueFieldMap PX.1) ∧ IsIso (i.residueFieldMap AX.1) ∧
        (toBase (projectiveIntersectionIdeal p q hp hq)).residueDegree PX.1 =
          (hypersurfaceToBase p hp).residueDegree P.1 ∧
        (toBase (projectiveIntersectionIdeal p q hp hq)).residueDegree AX.1 = 3 ∧
        PX ≠ AX ∧ zcycle = Finsupp.single AX 1 ∧
        (∀ B ∈ zcycle.support, zcycle B = 1) ∧
        EffectiveZeroCycle.degree (toBase (projectiveIntersectionIdeal p q hp hq)) zcycle = 3 ∧
        PX ∉ zcycle.support ∧
        letI := pointAlgebra (hypersurfaceToBase p hp) A.1
        ∃ (anchor : Fin 4) (g : ChartRing (equationIdeal p hp) anchor →+* S.residueField A.1)
          (pivot : Fin 3),
          g.comp (chartBaseMap (equationIdeal p hp) anchor) = algebraMap K (S.residueField A.1) ∧
          Spec.map (CommRingCat.ofHom g) ≫ chartι (equationIdeal p hp) anchor =
            S.fromSpecResidueField A.1 ∧
          let x : Fin 4 → S.residueField A.1 := fun j => g (chartCoordinate (equationIdeal p hp) anchor j)
          x anchor = 1 ∧
          Function.Surjective (eval₂Hom (algebraMap K (S.residueField A.1))
            (fun r : Fin 3 => x (anchor.succAbove r))) ∧
          p.eval₂ (algebraMap K (S.residueField A.1)) x = 0 ∧
          (pderiv (anchor.succAbove pivot) p).eval₂ (algebraMap K (S.residueField A.1)) x ≠ 0 ∧
          q.eval₂ ((algebraMap (S.residueField A.1)
              (PfaffianDescent.CubicSurfaceFirstJet (S.residueField A.1))).comp
            (algebraMap K (S.residueField A.1)))
            (PfaffianDescent.cubicNormalizedSurfacePoint_tangentJet
              (p.map (algebraMap K (S.residueField A.1))) anchor x pivot) = 0 := by
  classical
  obtain ⟨A, hAP, hAdegree, hchoice⟩ :=
    boundary_actualOriginalPoint_exists_disjoint_cubicPoint_fullJet_equation p hp hp0
      P hPcop hno m hm hdegree
  let S := hypersurface p hp
  letI := pointAlgebra (hypersurfaceToBase p hp) P.1
  letI := pointAlgebra (hypersurfaceToBase p hp) A.1
  obtain ⟨jP, y, jA, x, pivot, q, hgP, hgA, hy, _hevalP, hx, hevalA,
      hpy, hpx, hpivot, hq, hqP, hqjet, hqnot⟩ := hchoice
  obtain ⟨gP, hgbaseP, hgpointP, hyexact⟩ := hgP
  obtain ⟨gA, hgbaseA, hgpointA, hxexact⟩ := hgA
  have hqPexact : q.eval₂ (algebraMap K (S.residueField P.1))
      (fun j => gP (chartCoordinate (equationIdeal p hp) jP j)) = 0 := by
    simpa only [hyexact] using hqP
  have hqA := originalNormalizedFullJet_zero_residue_value p q jA x hx pivot hqjet
  have hqAexact : q.eval₂ (algebraMap K (S.residueField A.1))
      (fun j => gA (chartCoordinate (equationIdeal p hp) jA j)) = 0 := by
    simpa only [hxexact] using hqA
  obtain ⟨PX, hPX, hPXresidue, hPXdegree⟩ :=
    selectedCurve_originalClosedPoint_of_original_chart_q_zero p q hp (m + 1) hq P
      jP gP hgbaseP hgpointP hqPexact
  obtain ⟨AX, hAX, hAXresidue, hAXdegree⟩ :=
    selectedCurve_originalClosedPoint_of_original_chart_q_zero p q hp (m + 1) hq A
      jA gA hgbaseA hgpointA hqAexact
  let X := scheme (projectiveIntersectionIdeal p q hp hq)
  let i := cubicSecondEquationCurveImmersion p q hp (m + 1) hq
  have hAXdegree3 : (toBase (projectiveIntersectionIdeal p q hp hq)).residueDegree AX.1 = 3 :=
    hAXdegree.trans hAdegree
  have hdisjoint : PX ≠ AX := by
    intro h
    apply hAP
    apply Subtype.ext
    exact hAX.symm.trans ((congrArg (fun B : closedPoints X => i B.1) h).symm.trans hPX)
  let zcycle : EffectiveZeroCycle X := Finsupp.single AX 1
  have hred : ∀ B ∈ zcycle.support, zcycle B = 1 := by
    intro B hB
    have hBA : B = AX := by
      simpa only [zcycle, Finsupp.support_single _ one_ne_zero, Finset.mem_singleton] using hB
    subst B
    simp [zcycle]
  have hzdegree : EffectiveZeroCycle.degree (toBase (projectiveIntersectionIdeal p q hp hq)) zcycle = 3 := by
    simp [EffectiveZeroCycle.degree, zcycle, hAXdegree3]
  have hPoutside : PX ∉ zcycle.support := by
    simpa only [zcycle, Finsupp.support_single _ one_ne_zero, Finset.mem_singleton] using hdisjoint
  refine ⟨A, q, hq, hqnot, hAP, hAdegree, PX, AX, zcycle,
    hPX, hAX, hPXresidue, hAXresidue, hPXdegree, hAXdegree3,
    hdisjoint, rfl, hred, hzdegree, hPoutside, jA, gA, pivot, hgbaseA, hgpointA, ?_⟩
  simpa only [hxexact] using And.intro hx (And.intro hevalA (And.intro hpx (And.intro hpivot hqjet)))

end PfaffianDescent.Coray
