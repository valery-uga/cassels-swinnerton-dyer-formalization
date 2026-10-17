import PfaffianDescent.CorayModelIncidencePositive

/-! Every actual support point of SAME literal model incidence retains original degree. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
variable {K M : Type u} [Field K] [Field M] [Algebra K M] [Module.Finite K M]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

/-- Actual coefficient-map base square and residue tower give a pointwise
original-degree multiple. Closedness produces positive actual model degree.
This helper takes honest incidence, never a desired degree/count outcome. -/
theorem coefficientComponent_originalPoint_modelClosedPoint_degreeTower001
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (D : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) M))
    (hID : (I.map (componentPolynomialCoefficientMap (algebraMap K M))).toIdeal ≤ D.toIdeal)
    (P : closedPoints (scheme I)) (Q : closedPoints (scheme D))
    (hQP : coefficientComponentToOriginal I D hID Q.1 = P.1) :
    let f := coefficientComponentToOriginal I D hID
    Module.finrank K M * (toBase D).residueDegree Q.1 =
      (toBase I).residueDegree P.1 * f.residueDegree Q.1 ∧
    (toBase I).residueDegree P.1 ∣
      Module.finrank K M * (toBase D).residueDegree Q.1 ∧
    (toBase I).residueDegree P.1 ≤
      Module.finrank K M * (toBase D).residueDegree Q.1 := by
  let f := coefficientComponentToOriginal I D hID
  let b := Spec.map (CommRingCat.ofHom (algebraMap K M))
  have hSquare : f ≫ toBase I = toBase D ≫ b :=
    (coefficientComponentToOriginal_finite_and_toBase I D hID).2
  have hTower : Module.finrank K M * (toBase D).residueDegree Q.1 =
      (toBase I).residueDegree P.1 * f.residueDegree Q.1 := by
    calc
      _ = (toBase D ≫ b).residueDegree Q.1 := by
        rw [residueDegree_comp,
          show (toBase D) Q.1 = IsLocalRing.closedPoint M from Subsingleton.elim _ _]
        rw [modelFieldSpectrum_original_residueDegree_eq_finrank]
      _ = (f ≫ toBase I).residueDegree Q.1 :=
        congrArg (fun g : scheme D ⟶ Spec (.of K) => g.residueDegree Q.1) hSquare.symm
      _ = _ := by rw [residueDegree_comp, hQP]
  have hDiv : (toBase I).residueDegree P.1 ∣
      Module.finrank K M * (toBase D).residueDegree Q.1 := ⟨f.residueDegree Q.1, hTower⟩
  letI : Algebra M ((scheme D).residueField Q.1) := pointAlgebra (toBase D) Q.1
  letI : Module.Finite M ((scheme D).residueField Q.1) := closedPoint_moduleFinite (toBase D) Q
  have hQPositive : 0 < (toBase D).residueDegree Q.1 := by
    rw [← closedPoint_finrank_eq_residueDegree (toBase D) Q]
    exact Module.finrank_pos
  have hPositive : 0 < Module.finrank K M * (toBase D).residueDegree Q.1 :=
    Nat.mul_pos Module.finrank_pos hQPositive
  exact ⟨hTower, hDiv, Nat.le_of_dvd hPositive hDiv⟩

/-- The entire literal point/model cycle is constructed, and EVERY support
point gets the actual original-degree lower bound. No cycle/incidence/count
certificate, transitivity, reducedness or genus bound is supplied. -/
theorem originalPointModelIncidence_entireCycle_supportPointDegreeLowerBounds001
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (D : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) M))
    (hID : (I.map (componentPolynomialCoefficientMap (algebraMap K M))).toIdeal ≤ D.toIdeal)
    (P : closedPoints (scheme I)) :
    let ep := (scheme I).fromSpecResidueField P.1
    let f := coefficientComponentToOriginal I D hID
    let a := pullback.snd ep f
    let pi := a ≫ toBase D
    ∃ hclosed : IsClosedImmersion a, ∃ hfinite : IsFinite pi,
      letI := hclosed
      letI := hfinite
      let z := pushforwardClosedCycle a (finiteSchemeFundamentalCycle pi)
      EffectiveZeroCycle.degree (toBase D) z = finiteSchemeRank pi ∧
        (∀ Q ∈ z.support, f Q.1 = P.1) ∧
        (∀ Q ∈ z.support,
          (toBase I).residueDegree P.1 ∣
            Module.finrank K M * (toBase D).residueDegree Q.1 ∧
          (toBase I).residueDegree P.1 ≤
            Module.finrank K M * (toBase D).residueDegree Q.1) := by
  obtain ⟨hclosed, hfinite, hDegree, _hOriginalDegree, hPoints⟩ :=
    originalPointModelIncidence_entireCycle_degrees_and_originalPoint I D hID P
  refine ⟨hclosed, hfinite, hDegree, hPoints, ?_⟩
  intro Q hQ
  exact (coefficientComponent_originalPoint_modelClosedPoint_degreeTower001
    I D hID P Q (hPoints Q hQ)).2

/-- ORIGINAL p/q/minimal I, actual geometric minimal component G and SAME P
internally produce the SAME joint stabilizer model and ENTIRE cycle, now
with the genuine original degree lower bound on EVERY support point. -/
theorem originalMinimalGeometricComponent_exists_jointModel_entireIncidence_supportPointDegreeLowerBounds001
    {Ω : Type u} [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsAlgClosed Ω]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 1 ≤ n) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hI : I.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes)
    (P : closedPoints (scheme I))
    (G : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) Ω))
    (hG : G.toIdeal ∈
      (I.map (componentPolynomialCoefficientMap (algebraMap K Ω))).toIdeal.minimalPrimes) :
    ∃ (L : FiniteGaloisIntermediateField K Ω)
      (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) L)),
      C.toIdeal ∈ (I.map (componentPolynomialCoefficientMap (algebraMap K L))).toIdeal.minimalPrimes ∧
      C.toIdeal.map (MvPolynomial.map (algebraMap L Ω)) = G.toIdeal ∧
      let M := homogeneousIdealStabilizerFixedField (K := K) C
      let D := C.comap (componentPolynomialCoefficientMap (algebraMap M L))
      ∃ hID : (I.map (componentPolynomialCoefficientMap (algebraMap K M))).toIdeal ≤ D.toIdeal,
      let ep := (scheme I).fromSpecResidueField P.1
      let f := coefficientComponentToOriginal I D hID
      let a := pullback.snd ep f
      let c := pullback.fst ep f
      let pi := a ≫ toBase D
      ∃ hclosed : IsClosedImmersion a, ∃ hfinite : IsFinite pi, ∃ hfiniteP : IsFinite c,
        letI := hclosed
        letI := hfinite
        letI := hfiniteP
        let z := pushforwardClosedCycle a (finiteSchemeFundamentalCycle pi)
        D.toIdeal ∈ (I.map (componentPolynomialCoefficientMap (algebraMap K M))).toIdeal.minimalPrimes ∧
          GeometricallyIntegral (toBase D) ∧
          Module.finrank K M = Nat.card (irreducibleComponents
            (scheme (I.map (componentPolynomialCoefficientMap (algebraMap K Ω))))) ∧
          0 < actualCurveCoordinateHilbertDegree D ∧
          Module.finrank K M * actualCurveCoordinateHilbertDegree D ≤ 3 * n ∧
          EffectiveZeroCycle.degree (toBase D) z = finiteSchemeRank pi ∧
          EffectiveZeroCycle.degree (toBase D ≫ Spec.map (CommRingCat.ofHom (algebraMap K M))) z =
            Module.finrank K M * finiteSchemeRank pi ∧
          Module.finrank K M * finiteSchemeRank pi =
            (toBase I).residueDegree P.1 * (@finiteSchemeRank.{u} ((scheme I).residueField P.1) inferInstance (pullback ep f) c hfiniteP) ∧
          0 < finiteSchemeRank pi ∧ 0 < (@finiteSchemeRank.{u} ((scheme I).residueField P.1) inferInstance (pullback ep f) c hfiniteP) ∧
          (∀ Q ∈ z.support, f Q.1 = P.1) ∧
          (∀ Q ∈ z.support,
            (toBase I).residueDegree P.1 ∣
              Module.finrank K M * (toBase D).residueDegree Q.1 ∧
            (toBase I).residueDegree P.1 ≤
              Module.finrank K M * (toBase D).residueDegree Q.1) := by
  obtain ⟨L, C, hCL, hCO, hID, hclosed, hfinite, hfiniteP,
      hDmin, hGI, hField, hMuPositive, hMuBound, hDegreeM, hDegreeK,
      hCount, hNuPositive, hSPositive, hPoints⟩ :=
    originalMinimalGeometricComponent_exists_jointModel_entire_incidence_positive_rank_count
      p q hp hp0 n hn hq hnot I hI P G hG
  let M := homogeneousIdealStabilizerFixedField (K := K) C
  let D := C.comap (componentPolynomialCoefficientMap (algebraMap M L))
  letI : Module.Finite K M := inferInstance
  refine ⟨L, C, hCL, hCO, hID, hclosed, hfinite, hfiniteP,
    hDmin, hGI, hField, hMuPositive, hMuBound, hDegreeM, hDegreeK,
    hCount, hNuPositive, hSPositive, hPoints, ?_⟩
  intro Q hQ
  exact (coefficientComponent_originalPoint_modelClosedPoint_degreeTower001
    (K := K) (M := M) I D hID P Q (hPoints Q hQ)).2

end PfaffianDescent.Coray
