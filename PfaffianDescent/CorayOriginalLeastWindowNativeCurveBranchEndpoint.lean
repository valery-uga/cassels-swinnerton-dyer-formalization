import PfaffianDescent.CorayCanonicalMinimumFamilySameChartPolynomial
import PfaffianDescent.CorayAiSameFixedChartAuxiliaryIndependentPencil
import PfaffianDescent.CorayAiNativeBasisDenominator
import PfaffianDescent.CorayAiOriginalPencilCurveBranchContradiction
import PfaffianDescent.CoraySelectedCurveOriginalClosedPoint

noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
set_option autoImplicit false
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Choose a finite original section basis internally. The basis is of the
same through-point quotient space, without extension of the original field. -/
private theorem originalThroughCoordinateSectionSpace_exists_finBasis001
    {K L : Type u} [Field K] [CommRing L] [Algebra K L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (n : ℕ)
    (y : Fin 4 → L) (hpy : p.eval₂ (algebraMap K L) y = 0) :
    ∃ (m : ℕ) (b : Module.Basis (Fin m) K (cubicThroughCoordinateSections p hp n y hpy)),
      m = finrank K (cubicThroughCoordinateSections p hp n y hpy) := by
  letI : Module.Finite K (grading (equationIdeal p hp) n) :=
    Module.Finite.iff_fg.mpr ((homogeneousSubmodule_fg (Fin 4) K n).map
      (Ideal.Quotient.mkₐ K (equationIdeal p hp).toIdeal).toLinearMap)
  let W := cubicThroughCoordinateSections p hp n y hpy
  letI : Module.Free K W := Module.Free.of_divisionRing K W
  exact ⟨finrank K W, Module.finBasis K W, rfl⟩

/-- The honest curve-image branch is ruled out on an internally produced
original canonical chart, auxiliary point, pencil, full basis and denominator.
Natural4/n2 and10/n3 remain. Failure of the curve bound is not a completed
surface/tangent argument and is not called full Coray. -/
theorem coray_leastOriginalPoint_noSection_window_eq_four_or_ten_or_nativeImage_not_curve001
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
    (n : ℕ)
    (hLower : 1 + 3 * n.choose 2 ≤ (hypersurfaceToBase p hp).residueDegree P.1)
    (hUpper : (hypersurfaceToBase p hp).residueDegree P.1 < 1 + 3 * (n + 1).choose 2)
    : let S := hypersurface p hp
    letI : IsIntegral S :=
      PfaffianDescent.isIntegral_hypersurface_of_smooth_of_nonzero_of_infinite p hp hp0
    letI : Algebra K S.functionField :=
      (schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp)).toAlgebra
    letI := pointAlgebra (hypersurfaceToBase p hp) P.1
    ((hypersurfaceToBase p hp).residueDegree P.1 = 4 ∧ n = 2) ∨
      ((hypersurfaceToBase p hp).residueDegree P.1 = 10 ∧ n = 3) ∨
      ∃ (j : Fin 4)
        (gP : ChartRing (equationIdeal p hp) j →+* S.residueField P.1),
        gP.comp (chartBaseMap (equationIdeal p hp) j) = algebraMap K (S.residueField P.1) ∧
        Spec.map (CommRingCat.ofHom gP) ≫ chartι (equationIdeal p hp) j =
          S.fromSpecResidueField P.1 ∧
        ∃ (hpy : p.eval₂ (algebraMap K (S.residueField P.1))
            (fun i => gP (chartCoordinate (equationIdeal p hp) j i)) = 0)
          (hChart : Nonempty (chartι (equationIdeal p hp) j).opensRange),
          letI := hChart
          ∃ (m : ℕ), 5 ≤ m ∧
            ∃ (b : Module.Basis (Fin m) K (cubicThroughCoordinateSections p hp n
                (fun i => gP (chartCoordinate (equationIdeal p hp) j i)) hpy))
              (a : Fin m),
              ¬ ∀ z : cubicThroughPointBasisEvaluationImage p hp hp0 n
                  (fun i => gP (chartCoordinate (equationIdeal p hp) j i)) hpy j b a,
                Ring.DimensionLEOne
                  ((cubicThroughPointBasisEvaluationImage p hp hp0 n
                    (fun i => gP (chartCoordinate (equationIdeal p hp) j i)) hpy j b a).presheaf.stalk z) := by
  classical
  intro S
  letI : IsIntegral S :=
    PfaffianDescent.isIntegral_hypersurface_of_smooth_of_nonzero_of_infinite p hp hp0
  letI : Algebra K S.functionField :=
    (schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp)).toAlgebra
  letI := pointAlgebra (hypersurfaceToBase p hp) P.1
  rcases coray_leastOriginalPoint_window_eq_four_or_ten_or_canonical_minimumDegree_family001
      p hp hp0 P hPointCoprime hleast hno n hLower hUpper with hFour | hTen | hResidual
  · exact Or.inl hFour
  · exact Or.inr (Or.inl hTen)
  rcases hResidual with ⟨hn, hLarge, _hStrict, hFreedom, hSize, hAllIntegral, _hCanonical⟩
  obtain ⟨j, gP, hgPBase, hgPPoint, hpx, _hChartP, _hOne, hRank, _hLowerSections,
      q0, hq0, hq0not, hq0P⟩ :=
    leastOriginalCubicPoint_largeWindow_exists_sameCanonicalChart_nonzeroPolynomial001
      p hp hp0 P hPointCoprime hleast n (by omega) hLower hUpper hLarge hSize
  obtain ⟨A, hChartA, _hDegreeA, _hDifferent, _hQNot, _hJNot, hA⟩ :=
    originalAiWindow_noSection_exists_sameAuxiliaryPoint_fixedChart_independentPencil001
      p q0 hp hp0 n (by omega) hq0 hq0not P hPointCoprime (by omega)
        j gP hgPBase hgPPoint hq0P hno
  letI := pointAlgebra (hypersurfaceToBase p hp) A.1
  obtain ⟨gA, _hgSurj, hgBase, _hgPoint, hgDenominator, hPencil⟩ := hA
  let hChart : Nonempty (chartι (equationIdeal p hp) j).opensRange := ⟨⟨A.1, hChartA⟩⟩
  letI := hChart
  obtain ⟨hpy, hpz, s, hli, hAux, _hGenericNonzero, _hTranscendental⟩ := hPencil
  obtain ⟨m, b, hM⟩ := originalThroughCoordinateSectionSpace_exists_finBasis001
    p hp n (fun i => gP (chartCoordinate (equationIdeal p hp) j i)) hpy
  have hFive : 5 ≤ m := by
    rw [hM]
    exact hRank
  obtain ⟨a, ha⟩ := cubicThroughPointBasis_nonzero_polynomial_value_exists_nativeDenominator001
    p hp n (fun i => gP (chartCoordinate (equationIdeal p hp) j i)) hpy j b
      q0 hq0 hq0P gA hgDenominator
  right
  right
  refine ⟨j, gP, hgPBase, hgPPoint, hpy, hChart, m, hFive, b, a, ?_⟩
  intro hDim
  obtain ⟨_t, q, hq, hqP, _hqA, hnot, _hClass, hWhole⟩ :=
    originalIndependentPencil_curveBranch_exists_nonintegralWholeMember001
      p hp hp0 n (fun i => gP (chartCoordinate (equationIdeal p hp) j i)) hpy
        j b s hli gA hgBase hpz hAux a ha hDim
  obtain ⟨Q, hQ, _hIso, _hDegree⟩ :=
    selectedCurve_originalClosedPoint_of_original_chart_q_zero p q hp n hq P
      j gP hgPBase hgPPoint hqP
  exact hWhole (hAllIntegral q hq hnot ⟨Q.1, hQ⟩)

end PfaffianDescent.Coray
