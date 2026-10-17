import PfaffianDescent.CorayAiDegreeThreePointFixedChartDenominator
import PfaffianDescent.CorayAiOriginalAuxiliaryIndependentPencil
import PfaffianDescent.CorayAiOriginalWindowRankFiveHilbertRoom

noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open scoped PfaffianDescent.Coray
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The SAME constructed original degree-three A, fixed chart and q0-open
now give two independent degree-n through-P/A sections and an ORIGINAL-K
transcendental ratio. Neither A nor its field, rank, pencil, ratio, or chart
incidence is supplied. This stops before any attained parameter or member
nonintegrality assertion. -/
theorem originalAiWindow_noSection_exists_sameAuxiliaryPoint_fixedChart_independentPencil001
    {K : Type u} [Field K] [Infinite K]
    (p q0 : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 2 ≤ n)
    (hq0 : q0.IsHomogeneous n)
    (hnot : q0 ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (P : closedPoints (hypersurface p hp))
    (hcop : Nat.Coprime ((hypersurfaceToBase p hp).residueDegree P.1) 3)
    (hfreedom : 3 ≤ 3 * (n + 1).choose 2 -
      (hypersurfaceToBase p hp).residueDegree P.1)
    (j : Fin 4) :
    let S := hypersurface p hp
    let I := equationIdeal p hp
    letI := pointAlgebra (hypersurfaceToBase p hp) P.1
    ∀ gP : ChartRing I j →+* S.residueField P.1,
      gP.comp (chartBaseMap I j) = algebraMap K (S.residueField P.1) →
      Spec.map (CommRingCat.ofHom gP) ≫ chartι I j = S.fromSpecResidueField P.1 →
      q0.eval₂ (algebraMap K (S.residueField P.1))
        (fun k => gP (chartCoordinate I j k)) = 0 →
      (¬ ∃ s : Spec (.of K) ⟶ S, s ≫ hypersurfaceToBase p hp = 𝟙 _) →
      ∃ (A : closedPoints S) (hChart : A.1 ∈ (chartι I j).opensRange),
        (hypersurfaceToBase p hp).residueDegree A.1 = 3 ∧ A ≠ P ∧
        Ideal.Quotient.mk I.toIdeal q0 ∉ A.1.asHomogeneousIdeal ∧
        coordinate I j ∉ A.1.asHomogeneousIdeal ∧
        letI := pointAlgebra (hypersurfaceToBase p hp) A.1
        ∃ gA : ChartRing I j →+* S.residueField A.1,
          Function.Surjective gA ∧
          gA.comp (chartBaseMap I j) = algebraMap K (S.residueField A.1) ∧
          Spec.map (CommRingCat.ofHom gA) ≫ chartι I j = S.fromSpecResidueField A.1 ∧
          gA (q0.eval₂ (chartBaseMap I j) (chartCoordinate I j)) ≠ 0 ∧
          letI : IsIntegral S :=
            PfaffianDescent.isIntegral_hypersurface_of_smooth_of_nonzero_of_infinite p hp hp0
          letI : Algebra K S.functionField :=
            (schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp)).toAlgebra
          letI : Nonempty (chartι I j).opensRange := ⟨⟨A.1, hChart⟩⟩
          ∃ (hpy : p.eval₂ (algebraMap K (S.residueField P.1))
              (fun k => gP (chartCoordinate I j k)) = 0)
            (hpz : p.eval₂ (algebraMap K (S.residueField A.1))
              (fun k => gA (chartCoordinate I j k)) = 0),
          ∃ s : Fin 2 → cubicThroughCoordinateSections p hp n
              (fun k => gP (chartCoordinate I j k)) hpy,
            LinearIndependent K s ∧
            (∀ i, cubicThroughPointAuxiliaryEvaluation p hp n
              (fun k => gP (chartCoordinate I j k)) hpy
              (fun k => gA (chartCoordinate I j k)) hpz (s i) = 0) ∧
            (∀ i, (show S.functionField from cubicThroughPointGenericLinearEvaluation
              p hp n (fun k => gP (chartCoordinate I j k)) hpy j (s i)) ≠ 0) ∧
            Transcendental K
              ((show S.functionField from cubicThroughPointGenericLinearEvaluation p hp n
                (fun k => gP (chartCoordinate I j k)) hpy j (s 1)) /
               (show S.functionField from cubicThroughPointGenericLinearEvaluation p hp n
                (fun k => gP (chartCoordinate I j k)) hpy j (s 0))) := by
  classical
  intro S I
  letI := pointAlgebra (hypersurfaceToBase p hp) P.1
  intro gP hgPbase hgPpoint hqP hno
  obtain ⟨A, hDegree, hDifferent, hChart, hQNot, hJNot, hA⟩ :=
    originalThroughPointPolynomial_noSection_exists_degreeThreePoint_in_fixedChart_denominatorOpen001
      p q0 hp hp0 n hq0 hnot P j gP hgPbase hgPpoint hqP hno
  refine ⟨A, hChart, hDegree, hDifferent, hQNot, hJNot, ?_⟩
  letI := pointAlgebra (hypersurfaceToBase p hp) A.1
  obtain ⟨gA, hgSurj, hgBase, hgPoint, hgDenominator⟩ := hA
  refine ⟨gA, hgSurj, hgBase, hgPoint, hgDenominator, ?_⟩
  letI : IsIntegral S :=
    PfaffianDescent.isIntegral_hypersurface_of_smooth_of_nonzero_of_infinite p hp hp0
  letI : Algebra K S.functionField :=
    (schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp)).toAlgebra
  letI : Nonempty (chartι I j).opensRange := ⟨⟨A.1, hChart⟩⟩
  have hSize : (hypersurfaceToBase p hp).residueDegree P.1 + 5 ≤
      (n + 3).choose 3 - n.choose 3 :=
    coray_case_Ai_originalWindow_rankFive_hilbertRoom001 n _ hn hcop hfreedom
  exact originalClosedPoints_exists_independent_sameDegree_pencil_through_both_transcendental001
    p hp hp0 n P A hDegree hSize j j gP hgPbase hgPpoint gA hgBase hgPoint

end PfaffianDescent.Coray
